/*
 * filecarver - recover deleted/lost files from a raw disk image by signature
 *
 * Supports: JPEG, PNG, PDF, GIF
 * Build:    gcc -O2 -Wall -Wextra -o filecarver filecarver.c
 * Usage:    ./filecarver [-a align] [-m max_MB] [-n min_bytes] [-c] image outdir
 *
 * How it works
 *   File carving ignores the filesystem entirely. Deleted files usually leave
 *   their data blocks intact until overwritten, so we scan the raw bytes for
 *   file headers and then "walk" each format's internal structure to find the
 *   true end of the file (more reliable than searching for the first footer):
 *     JPEG: walks marker segments, so an embedded EXIF thumbnail's FFD9 is
 *           skipped; stops at the real EOI.
 *     PNG:  walks chunks and verifies each CRC32 until IEND.
 *     PDF:  finds %%EOF, and extends across incremental updates.
 *     GIF:  walks blocks until the 0x3B trailer.
 *   Limitation: files stored in non-contiguous fragments cannot be rebuilt;
 *   they appear as PARTIAL (or are rejected).
 *
 * POSIX only (uses mmap). Image must fit in the process address space.
 */
#define _GNU_SOURCE
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

/* ---------- CRC32 (IEEE) ---------- */
static uint32_t crc_table[256];
static void crc_init(void) {
    for (uint32_t i = 0; i < 256; i++) {
        uint32_t c = i;
        for (int k = 0; k < 8; k++) c = (c & 1) ? 0xEDB88320u ^ (c >> 1) : c >> 1;
        crc_table[i] = c;
    }
}
static uint32_t crc32_buf(const uint8_t *p, size_t n) {
    uint32_t c = 0xFFFFFFFFu;
    while (n--) c = crc_table[(c ^ *p++) & 0xFF] ^ (c >> 8);
    return c ^ 0xFFFFFFFFu;
}
static uint32_t be32(const uint8_t *p) {
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | p[3];
}

/*
 * Walkers: p points at a candidate file start, n = bytes available.
 * Return the length of the recoverable data (0 = not a valid file).
 * *complete is set to 1 only if a proper end-of-file marker was reached.
 */

/* ---------- JPEG ---------- */
static int jpeg_marker_ok(uint8_t m) {
    if (m >= 0xC0 && m <= 0xCF) return m != 0xC8;
    if (m >= 0xDA && m <= 0xDF) return 1;
    if (m >= 0xE0 && m <= 0xEF) return 1;
    return m == 0xFE;
}
static size_t walk_jpeg(const uint8_t *p, size_t n, int *complete) {
    *complete = 0;
    if (n < 4 || p[0] != 0xFF || p[1] != 0xD8 || p[2] != 0xFF) return 0;
    size_t i = 2, good = 0;
    int sof = 0, sos = 0;
    for (;;) {
        if (i + 2 > n || p[i] != 0xFF) break;
        while (i + 1 < n && p[i + 1] == 0xFF) i++; /* fill bytes */
        if (i + 2 > n) break;
        uint8_t m = p[i + 1];
        if (m == 0xD9) { /* EOI */
            if (sof && sos) { *complete = 1; return i + 2; }
            return 0;
        }
        if (!jpeg_marker_ok(m) || i + 4 > n) break;
        size_t len = ((size_t)p[i + 2] << 8) | p[i + 3];
        if (len < 2 || i + 2 + len > n) break;
        if (m >= 0xC0 && m <= 0xCF && m != 0xC4 && m != 0xCC) sof = 1;
        i += 2 + len;
        if (m == 0xDA) { /* scan data: skip stuffed bytes and RSTn */
            sos = 1;
            while (i < n) {
                if (p[i] != 0xFF) { i++; continue; }
                if (i + 1 >= n) { i = n; break; }
                uint8_t b = p[i + 1];
                if (b == 0x00 || (b >= 0xD0 && b <= 0xD7)) { i += 2; continue; }
                if (b == 0xFF) { i++; continue; }
                break; /* real marker */
            }
        }
        good = i;
    }
    return (sof && sos) ? good : 0;
}

/* ---------- PNG ---------- */
static size_t walk_png(const uint8_t *p, size_t n, int *complete) {
    static const uint8_t sig[8] = {0x89, 'P', 'N', 'G', 0x0D, 0x0A, 0x1A, 0x0A};
    *complete = 0;
    if (n < 33 || memcmp(p, sig, 8) != 0) return 0;
    size_t i = 8;
    int first = 1;
    while (i + 12 <= n) {
        uint32_t len = be32(p + i);
        const uint8_t *t = p + i + 4;
        if (!isalpha(t[0]) || !isalpha(t[1]) || !isalpha(t[2]) || !isalpha(t[3])) break;
        if (first && (memcmp(t, "IHDR", 4) != 0 || len != 13)) return 0;
        if (len > 0x7FFFFFFFu) break;
        size_t total = 12 + (size_t)len;
        if (i + total > n) break;
        if (crc32_buf(t, 4 + (size_t)len) != be32(p + i + 8 + len)) break; /* bad CRC */
        i += total;
        first = 0;
        if (memcmp(t, "IEND", 4) == 0) { *complete = 1; return i; }
    }
    return i > 33 ? i : 0;
}

/* ---------- PDF ---------- */
static size_t walk_pdf(const uint8_t *p, size_t n, int *complete) {
    *complete = 0;
    if (n < 16 || memcmp(p, "%PDF-", 5) != 0 || !isdigit(p[5])) return 0;
    size_t limit = n;
    const uint8_t *nx = memmem(p + 5, n - 5, "%PDF-", 5); /* next file begins */
    if (nx) limit = (size_t)(nx - p);

    const uint8_t *e = memmem(p + 5, limit - 5, "%%EOF", 5);
    if (!e) return 0;
    size_t end = (size_t)(e - p) + 5;
    for (;;) { /* extend across incremental updates / linearization */
        size_t after = end;
        const uint8_t *ne = (after < limit) ? memmem(p + after, limit - after, "%%EOF", 5) : NULL;
        if (!ne) break;
        size_t seg = (size_t)(ne - (p + after));
        if (!memmem(p + after, seg, "startxref", 9)) break;
        end = (size_t)(ne - p) + 5;
    }
    if (end < limit && p[end] == '\r') end++;
    if (end < limit && p[end] == '\n') end++;
    *complete = 1;
    return end;
}

/* ---------- GIF ---------- */
static int gif_skip_sub(const uint8_t *p, size_t n, size_t *i) {
    for (;;) {
        if (*i >= n) return 0;
        size_t sz = p[(*i)++];
        if (sz == 0) return 1;
        *i += sz;
        if (*i > n) return 0;
    }
}
static size_t walk_gif(const uint8_t *p, size_t n, int *complete) {
    *complete = 0;
    if (n < 14 || (memcmp(p, "GIF87a", 6) != 0 && memcmp(p, "GIF89a", 6) != 0)) return 0;
    size_t i = 13, good = 0;
    if (p[10] & 0x80) i += (size_t)3 << ((p[10] & 7) + 1);
    int frames = 0;
    while (i < n) {
        uint8_t b = p[i++];
        if (b == 0x3B) { *complete = 1; return frames ? i : 0; }
        if (b == 0x21) {
            if (i >= n) break;
            i++;
            if (!gif_skip_sub(p, n, &i)) break;
        } else if (b == 0x2C) {
            if (i + 9 > n) break;
            uint8_t lf = p[i + 8];
            i += 9;
            if (lf & 0x80) i += (size_t)3 << ((lf & 7) + 1);
            if (i >= n) break;
            i++; /* LZW min code size */
            if (!gif_skip_sub(p, n, &i)) break;
            frames++;
        } else break;
        good = i;
    }
    return frames ? good : 0;
}

/* ---------- signature table ---------- */
typedef size_t (*walker_fn)(const uint8_t *, size_t, int *);
typedef struct {
    const char *name, *ext;
    uint8_t magic[8];
    size_t mlen;
    walker_fn walk;
} sig_t;

static const sig_t SIGS[] = {
    {"JPEG", "jpg", {0xFF, 0xD8, 0xFF}, 3, walk_jpeg},
    {"PNG", "png", {0x89, 'P', 'N', 'G', 0x0D, 0x0A, 0x1A, 0x0A}, 8, walk_png},
    {"PDF", "pdf", {'%', 'P', 'D', 'F', '-'}, 5, walk_pdf},
    {"GIF", "gif", {'G', 'I', 'F', '8'}, 4, walk_gif},
};
#define NSIGS (sizeof(SIGS) / sizeof(SIGS[0]))

/* ---------- records ---------- */
typedef struct {
    size_t index, sig;
    uint64_t off, len;
    int complete;
    uint32_t crc;
    char name[96];
} rec_t;

static void usage(const char *a0) {
    fprintf(stderr,
            "Usage: %s [options] <disk_image> <output_dir>\n"
            "  -a N   scan alignment in bytes (default 512; use 1 for unaligned data)\n"
            "  -m N   max size of a single recovered file in MB (default 64)\n"
            "  -n N   min size in bytes to keep a file (default 128)\n"
            "  -c     recover only COMPLETE files (skip partial ones)\n",
            a0);
}

static int write_file(const char *path, const uint8_t *d, size_t n) {
    FILE *f = fopen(path, "wb");
    if (!f) return -1;
    size_t w = fwrite(d, 1, n, f);
    int rc = (fclose(f) == 0 && w == n) ? 0 : -1;
    return rc;
}

int main(int argc, char **argv) {
    size_t align = 512, maxsz = (size_t)64 << 20, minsz = 128;
    int complete_only = 0, opt;
    while ((opt = getopt(argc, argv, "a:m:n:ch")) != -1) {
        switch (opt) {
        case 'a': align = strtoull(optarg, NULL, 10); break;
        case 'm': maxsz = (size_t)strtoull(optarg, NULL, 10) << 20; break;
        case 'n': minsz = strtoull(optarg, NULL, 10); break;
        case 'c': complete_only = 1; break;
        default: usage(argv[0]); return 2;
        }
    }
    if (argc - optind != 2 || align == 0 || maxsz == 0) { usage(argv[0]); return 2; }
    const char *imgpath = argv[optind], *outdir = argv[optind + 1];

    int fd = open(imgpath, O_RDONLY);
    if (fd < 0) { fprintf(stderr, "open %s: %s\n", imgpath, strerror(errno)); return 1; }
    off_t sz = lseek(fd, 0, SEEK_END); /* works for files and block devices */
    if (sz <= 0) { fprintf(stderr, "image is empty or unreadable\n"); return 1; }
    size_t size = (size_t)sz;
    const uint8_t *img = mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
    if (img == MAP_FAILED) { fprintf(stderr, "mmap failed: %s\n", strerror(errno)); return 1; }
    madvise((void *)img, size, MADV_SEQUENTIAL);

    if (mkdir(outdir, 0755) != 0 && errno != EEXIST) {
        fprintf(stderr, "mkdir %s: %s\n", outdir, strerror(errno));
        return 1;
    }
    crc_init();

    rec_t *recs = NULL;
    size_t nrec = 0, cap = 0;
    size_t rejected[NSIGS] = {0};
    time_t t0 = time(NULL);

    size_t off = 0, last_prog = (size_t)-1;
    while (off < size) {
        if ((off >> 28) != last_prog) { /* every 256 MB */
            last_prog = off >> 28;
            fprintf(stderr, "\rscanning... %5.1f%%", 100.0 * (double)off / (double)size);
        }
        const uint8_t *q = img + off;
        int matched = 0;
        for (size_t s = 0; s < NSIGS; s++) {
            const sig_t *g = &SIGS[s];
            if (off + g->mlen > size || q[0] != g->magic[0] || memcmp(q, g->magic, g->mlen)) continue;
            size_t avail = size - off;
            if (avail > maxsz) avail = maxsz;
            int comp = 0;
            size_t len = g->walk(q, avail, &comp);
            if (len < minsz || (complete_only && !comp)) { rejected[s]++; continue; }

            if (nrec == cap) {
                cap = cap ? cap * 2 : 64;
                recs = realloc(recs, cap * sizeof(rec_t));
                if (!recs) { perror("realloc"); return 1; }
            }
            rec_t *r = &recs[nrec];
            r->index = nrec + 1;
            r->sig = s;
            r->off = off;
            r->len = len;
            r->complete = comp;
            r->crc = crc32_buf(q, len);
            snprintf(r->name, sizeof r->name, "%s_%05zu_0x%08llx%s.%s", g->ext, r->index,
                     (unsigned long long)off, comp ? "" : "_partial", g->ext);
            char path[4096];
            snprintf(path, sizeof path, "%s/%s", outdir, r->name);
            if (write_file(path, q, len) != 0) {
                fprintf(stderr, "\nwrite %s failed: %s\n", path, strerror(errno));
                return 1;
            }
            nrec++;
            off = ((off + len + align - 1) / align) * align; /* skip past recovered file */
            matched = 1;
            break;
        }
        if (!matched) off += align;
    }
    fprintf(stderr, "\rscanning... 100.0%%\n");
    time_t t1 = time(NULL);

    /* ---------- reports ---------- */
    char rpath[4096];
    snprintf(rpath, sizeof rpath, "%s/recovery_report.csv", outdir);
    FILE *csv = fopen(rpath, "w");
    if (csv) {
        fprintf(csv, "index,type,offset,offset_hex,size_bytes,status,crc32,file\n");
        for (size_t i = 0; i < nrec; i++) {
            rec_t *r = &recs[i];
            fprintf(csv, "%zu,%s,%llu,0x%llx,%llu,%s,%08x,%s\n", r->index, SIGS[r->sig].name,
                    (unsigned long long)r->off, (unsigned long long)r->off,
                    (unsigned long long)r->len, r->complete ? "COMPLETE" : "PARTIAL", r->crc, r->name);
        }
        fclose(csv);
    }

    snprintf(rpath, sizeof rpath, "%s/recovery_report.txt", outdir);
    FILE *rt = fopen(rpath, "w");
    if (!rt) { perror("report"); return 1; }
    char tbuf[64];
    strftime(tbuf, sizeof tbuf, "%Y-%m-%d %H:%M:%S", localtime(&t0));
    fprintf(rt, "FILE CARVING RECOVERY REPORT\n============================\n");
    fprintf(rt, "Image:       %s\n", imgpath);
    fprintf(rt, "Image size:  %zu bytes (%.2f MB)\n", size, (double)size / 1048576.0);
    fprintf(rt, "Scan start:  %s (%lds elapsed)\n", tbuf, (long)(t1 - t0));
    fprintf(rt, "Parameters:  align=%zu, max=%zu MB, min=%zu B, complete-only=%s\n\n", align,
            maxsz >> 20, minsz, complete_only ? "yes" : "no");

    fprintf(rt, "%-5s %-5s %-12s %12s  %-9s %-8s %s\n", "#", "Type", "Offset", "Size(B)", "Status", "CRC32",
            "File");
    fprintf(rt, "-------------------------------------------------------------------------------\n");
    size_t cnt_c[NSIGS] = {0}, cnt_p[NSIGS] = {0};
    uint64_t total = 0;
    for (size_t i = 0; i < nrec; i++) {
        rec_t *r = &recs[i];
        fprintf(rt, "%-5zu %-5s 0x%010llx %12llu  %-9s %08x %s\n", r->index, SIGS[r->sig].name,
                (unsigned long long)r->off, (unsigned long long)r->len, r->complete ? "COMPLETE" : "PARTIAL",
                r->crc, r->name);
        (r->complete ? cnt_c : cnt_p)[r->sig]++;
        total += r->len;
    }
    fprintf(rt, "\nSUMMARY\n-------\n%-6s %9s %9s %9s\n", "Type", "Complete", "Partial", "Rejected");
    for (size_t s = 0; s < NSIGS; s++)
        fprintf(rt, "%-6s %9zu %9zu %9zu\n", SIGS[s].name, cnt_c[s], cnt_p[s], rejected[s]);
    fprintf(rt, "\nTotal files recovered: %zu (%llu bytes)\n", nrec, (unsigned long long)total);
    fprintf(rt, "\nNotes\n-----\n"
                "* COMPLETE = format's end marker reached (JPEG EOI, PNG IEND with valid CRCs, PDF %%%%EOF, GIF trailer).\n"
                "* PARTIAL  = data valid up to the point shown; the tail was missing, overwritten or fragmented.\n"
                "* Rejected = header matched but the structure was invalid or below the minimum size.\n"
                "* Files split into non-contiguous fragments cannot be reassembled by this tool.\n"
                "* CRC32 is of the recovered bytes, for integrity tracking (not a filesystem checksum).\n");
    fclose(rt);

    printf("Recovered %zu file(s) -> %s\nReport: %s/recovery_report.txt (+ .csv)\n", nrec, outdir, outdir);
    free(recs);
    munmap((void *)img, size);
    close(fd);
    return 0;
}

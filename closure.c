/* closure -- streaming congruence closure over a challenge's word corpus.
 *
 * Reads rule lines from stdin (one alphabet case, --case upper|lower), packs
 * each word over 5 letters into a base-6 uint64, and closes the given
 * equalities under transitivity, left/right cancellation, relator rotation,
 * and extension congruence.
 *
 * Emits the short relations of each class (--out FILE, total length <=
 * --max-emit) and, to stderr, an "orders: k0..k4" line of generator-order
 * divisors read off the powers that collapse to the identity class. Every
 * derived equality is a consequence of the input rules.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXW 13
#define D 5

static uint64_t POW6[MAXW + 2];

static uint64_t *ncode;
static uint32_t *npar;
static uint32_t *nnxt;
static uint32_t *ncnt;
static uint32_t nnodes, ncap;

static uint64_t *hkey;
static uint32_t *hval;
static uint64_t hmask;
static uint64_t hcount;

static inline uint64_t mix64(uint64_t x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

static void hash_grow(void);

static inline uint32_t hget(uint64_t code) {
    uint64_t i = mix64(code) & hmask;
    while (hkey[i]) {
        if (hkey[i] == code) return hval[i] + 1;
        i = (i + 1) & hmask;
    }
    return 0;
}

static uint32_t node_new(uint64_t code) {
    if (nnodes == ncap) {
        ncap = ncap + (ncap >> 1);
        ncode = realloc(ncode, (size_t)ncap * 8);
        npar  = realloc(npar,  (size_t)ncap * 4);
        nnxt  = realloc(nnxt,  (size_t)ncap * 4);
        ncnt  = realloc(ncnt,  (size_t)ncap * 4);
        if (!ncode || !npar || !nnxt || !ncnt) { fprintf(stderr, "OOM nodes\n"); exit(1); }
    }
    uint32_t id = nnodes++;
    ncode[id] = code;
    npar[id] = id;
    nnxt[id] = UINT32_MAX;
    ncnt[id] = 1;
    return id;
}

static inline uint32_t hput(uint64_t code) {
    uint64_t i = mix64(code) & hmask;
    while (hkey[i]) {
        if (hkey[i] == code) return hval[i];
        i = (i + 1) & hmask;
    }
    uint32_t id = node_new(code);
    hkey[i] = code;
    hval[i] = id;
    if (++hcount > (hmask >> 1) + (hmask >> 2)) hash_grow();
    return id;
}

static void hash_grow(void) {
    uint64_t oldslots = hmask + 1;
    uint64_t *ok = hkey; uint32_t *ov = hval;
    uint64_t slots = oldslots << 1;
    hkey = calloc(slots, 8);
    hval = malloc(slots * 4);
    if (!hkey || !hval) { fprintf(stderr, "OOM hash\n"); exit(1); }
    hmask = slots - 1;
    for (uint64_t i = 0; i < oldslots; i++) {
        if (!ok[i]) continue;
        uint64_t j = mix64(ok[i]) & hmask;
        while (hkey[j]) j = (j + 1) & hmask;
        hkey[j] = ok[i];
        hval[j] = ov[i];
    }
    free(ok); free(ov);
    fprintf(stderr, "[hash] grown to 2^%d slots\n", __builtin_ctzll(slots));
}

static inline int wlen(uint64_t code) {
    int l = 0;
    while (code >= POW6[l + 1]) l++;
    return l;
}
static inline void wdec(uint64_t code, int len, uint8_t *out) {
    for (int i = len - 1; i >= 0; i--) { out[i] = (uint8_t)(code % 6) - 1; code /= 6; }
}
static inline uint64_t wenc(const uint8_t *w, int len) {
    uint64_t c = 1;
    for (int i = 0; i < len; i++) c = c * 6 + (uint64_t)(w[i] + 1);
    return c;
}

static inline uint64_t wstrip(uint64_t code, int len, int p, int s) {
    code /= POW6[s];
    int l = len - s;
    return POW6[l - p] + (code % POW6[l - p]);
}

static uint64_t *ustack;
static size_t utop, ucap;

static inline void upush(uint32_t a, uint32_t b) {
    if (utop == ucap) {
        ucap += ucap >> 1;
        ustack = realloc(ustack, ucap * 8);
        if (!ustack) { fprintf(stderr, "OOM stack\n"); exit(1); }
    }
    ustack[utop++] = ((uint64_t)a << 32) | b;
}

static inline uint32_t ufind(uint32_t x) {
    while (npar[x] != x) { npar[x] = npar[npar[x]]; x = npar[x]; }
    return x;
}

static uint64_t st_rules, st_pairs, st_cancel, st_ext, st_rot, st_dupline;

static uint32_t eps_node;
static uint32_t warn_bigclass = 0;

static uint32_t *memA, *memB;
static size_t memcapA, memcapB;

static void cancel_pair(uint32_t x, uint32_t y);

static void drain(void) {
    while (utop) {
        uint64_t pk = ustack[--utop];
        uint32_t a = (uint32_t)(pk >> 32), b = (uint32_t)pk;
        uint32_t ra = ufind(a), rb = ufind(b);
        if (ra == rb) continue;
        if (ncnt[ra] < ncnt[rb]) { uint32_t t = ra; ra = rb; rb = t; }

        uint32_t sa = ncnt[ra], sb = ncnt[rb];
        if (sa > memcapA) { memcapA = sa * 2; memA = realloc(memA, memcapA * 4); }
        if (sb > memcapB) { memcapB = sb * 2; memB = realloc(memB, memcapB * 4); }
        uint32_t k = 0;
        for (uint32_t m = ra; m != UINT32_MAX; m = nnxt[m]) memA[k++] = m;
        k = 0;
        uint32_t tail = rb;
        for (uint32_t m = rb; m != UINT32_MAX; m = nnxt[m]) { memB[k++] = m; tail = m; }

        nnxt[tail] = nnxt[ra];
        nnxt[ra] = rb;
        npar[rb] = ra;
        ncnt[ra] = sa + sb;
        if (ncnt[ra] > 5000 && ncnt[ra] > warn_bigclass) {
            warn_bigclass = ncnt[ra];
            fprintf(stderr, "[warn] class size %u (soundness canary)\n", ncnt[ra]);
        }

        for (uint32_t i = 0; i < sb; i++)
            for (uint32_t j = 0; j < sa; j++) {
                st_pairs++;
                cancel_pair(memB[i], memA[j]);
            }
    }
}

static void cancel_pair(uint32_t x, uint32_t y) {
    uint64_t cx = ncode[x], cy = ncode[y];
    int lx = wlen(cx), ly = wlen(cy);
    uint8_t wx[MAXW], wy[MAXW];
    wdec(cx, lx, wx);
    wdec(cy, ly, wy);
    int lim = lx < ly ? lx : ly;
    int p = 0;
    while (p < lim && wx[p] == wy[p]) p++;
    int s = 0, rem = lim - p;
    while (s < rem && wx[lx - 1 - s] == wy[ly - 1 - s]) s++;
    if (p + s > 0) {
        st_cancel++;
        uint64_t ax = wstrip(cx, lx, p, s);
        uint64_t ay = wstrip(cy, ly, p, s);

        uint32_t nx = hput(ax), ny = hput(ay);
        int lax = lx - p - s, lay = ly - p - s;

        if (lax == 0 || lay == 0) {
            uint64_t w = lax == 0 ? ay : ax;
            int lw = lax == 0 ? lay : lax;
            if (lw > 0) {
                uint8_t buf[2 * MAXW];
                wdec(w, lw, buf);
                memcpy(buf + lw, buf, (size_t)lw);
                for (int r = 1; r < lw; r++) {
                    uint64_t rot = wenc(buf + r, lw);
                    uint32_t nr = hput(rot);
                    st_rot++;
                    upush(nr, eps_node);
                }
            }
        }
        upush(nx, ny);
    }

    if (lx <= MAXW - 1 && ly <= MAXW - 1) {
        for (int d = 1; d <= D; d++) {
            uint32_t r1 = hget(cx * 6 + (uint64_t)d);
            if (r1) {
                uint32_t r2 = hget(cy * 6 + (uint64_t)d);
                if (r2 && ufind(r1 - 1) != ufind(r2 - 1)) { st_ext++; upush(r1 - 1, r2 - 1); }
            }
            uint32_t l1 = hget(cx + POW6[lx] * (uint64_t)(5 + d));
            if (l1) {
                uint32_t l2 = hget(cy + POW6[ly] * (uint64_t)(5 + d));
                if (l2 && ufind(l1 - 1) != ufind(l2 - 1)) { st_ext++; upush(l1 - 1, l2 - 1); }
            }
        }
    }
}

static int parse_line(const char *line, int upper, uint64_t *u, uint64_t *v) {

    const char *q[4] = {0, 0, 0, 0};
    const char *pos = line;
    const char *t0s = 0, *t0e = 0, *t1s = 0, *t1e = 0;
    while (1) {
        const char *a = strchr(pos, '"');
        if (!a) break;
        const char *b = strchr(a + 1, '"');
        if (!b) break;
        t0s = t1s; t0e = t1e;
        t1s = a + 1; t1e = b;
        pos = b + 1;
    }
    (void)q;
    if (!t0s || !t1s) return 0;

    const char *c = t0e + 1;
    while (c < t1s && *c != ':') c++;
    if (c >= t1s) return 0;
    size_t l0 = (size_t)(t0e - t0s), l1 = (size_t)(t1e - t1s);
    if (l0 == 0 || l0 > MAXW || l1 == 0 || l1 > MAXW) return 0;
    char lo = upper ? 'A' : 'a', hi = upper ? 'E' : 'e';
    uint64_t cu = 1, cv = 1;
    for (size_t i = 0; i < l0; i++) {
        char ch = t0s[i];
        if (ch < lo || ch > hi) return 0;
        cu = cu * 6 + (uint64_t)(ch - lo + 1);
    }
    for (size_t i = 0; i < l1; i++) {
        char ch = t1s[i];
        if (ch < lo || ch > hi) return 0;
        cv = cv * 6 + (uint64_t)(ch - lo + 1);
    }
    *u = cu; *v = cv;
    return 1;
}

static void emit_word(FILE *f, uint64_t code) {
    int l = wlen(code);
    uint8_t w[MAXW];
    wdec(code, l, w);
    fprintf(f, "%d", l);
    for (int i = 0; i < l; i++) fprintf(f, " %d", w[i]);
}

static uint64_t emit_relations(const char *path, int max_emit) {
    FILE *out = fopen(path, "w");
    if (!out) { perror(path); exit(1); }
    uint64_t emitted = 0;
    for (uint32_t r = 0; r < nnodes; r++) {
        if (ufind(r) != r || ncnt[r] < 2) continue;

        uint32_t best = r;
        uint64_t bkey = ncode[r];
        int blen = wlen(bkey);
        for (uint32_t m = nnxt[r]; m != UINT32_MAX; m = nnxt[m]) {
            int l = wlen(ncode[m]);
            if (l < blen || (l == blen && ncode[m] < bkey)) {
                best = m; blen = l; bkey = ncode[m];
            }
        }
        for (uint32_t m = r; m != UINT32_MAX; m = nnxt[m]) {
            if (m == best) continue;
            int l = wlen(ncode[m]);
            if (blen + l > max_emit) continue;
            emit_word(out, bkey);
            fprintf(out, " ");
            emit_word(out, ncode[m]);
            fprintf(out, "\n");
            emitted++;
        }
    }
    fclose(out);
    fprintf(stderr, "[emit] %llu relations (total len <= %d) -> %s\n",
            (unsigned long long)emitted, max_emit, path);
    return emitted;
}

int main(int argc, char **argv) {
    int upper = 1;
    int max_emit = 26;
    const char *outpath = "closure_relations.txt";
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--case") && i + 1 < argc) upper = !strcmp(argv[++i], "upper");
        else if (!strcmp(argv[i], "--out") && i + 1 < argc) outpath = argv[++i];
        else if (!strcmp(argv[i], "--max-emit") && i + 1 < argc) max_emit = atoi(argv[++i]);
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }
    POW6[0] = 1;
    for (int i = 1; i <= MAXW + 1; i++) POW6[i] = POW6[i - 1] * 6;

    /* Most retained corpora use far fewer than 67 million distinct words.
     * Starting there consumed about 3 GiB before the first input byte and made
     * a cold PSL run needlessly fragile. Both tables already grow exactly, so
     * start at practical production sizes and pay for larger corpora only when
     * they actually occur. */
    ncap = 1u << 24;
    ncode = malloc((size_t)ncap * 8);
    npar = malloc((size_t)ncap * 4);
    nnxt = malloc((size_t)ncap * 4);
    ncnt = malloc((size_t)ncap * 4);
    uint64_t slots = 1ull << 25;
    hkey = calloc(slots, 8);
    hval = malloc(slots * 4);
    hmask = slots - 1;
    ucap = 1 << 22;
    ustack = malloc(ucap * 8);
    memcapA = memcapB = 1 << 12;
    memA = malloc(memcapA * 4);
    memB = malloc(memcapB * 4);
    if (!ncode || !npar || !nnxt || !ncnt || !hkey || !hval || !ustack || !memA || !memB) {
        fprintf(stderr, "OOM init\n"); return 1;
    }
    eps_node = hput(1);
    time_t t0 = time(NULL);
    char *line = malloc(1 << 20);
    size_t lsz = 1 << 20;
    while (fgets(line, (int)lsz, stdin)) {

        size_t ll = strlen(line);
        while (ll == lsz - 1 && line[ll - 1] != '\n') {
            if (!fgets(line, (int)lsz, stdin)) break;
            ll = strlen(line);
        }
        uint64_t cu, cv;
        if (!parse_line(line, upper, &cu, &cv)) continue;
        st_rules++;
        if (cu == cv) { st_dupline++; continue; }
        uint32_t nu = hput(cu), nv = hput(cv);
        upush(nu, nv);
        drain();
        if ((st_rules & 0xFFFFF) == 0)
            fprintf(stderr, "[stream] rules=%.1fM nodes=%.1fM pairs=%.1fM cancels=%.1fM ext=%.1fM t=%lds\n",
                    (double)st_rules / 1e6, (double)nnodes / 1e6,
                    (double)st_pairs / 1e6, (double)st_cancel / 1e6,
                    (double)st_ext / 1e6, (long)(time(NULL) - t0));
    }
    drain();
    fprintf(stderr, "[done-stream] rules=%llu nodes=%u pairs=%llu cancels=%llu ext=%llu rot=%lld t=%lds\n",
            (unsigned long long)st_rules, nnodes, (unsigned long long)st_pairs,
            (unsigned long long)st_cancel, (unsigned long long)st_ext,
            (long long)st_rot, (long)(time(NULL) - t0));

    uint64_t hist[64] = {0};
    uint32_t nclasses = 0;
    for (uint32_t i = 0; i < nnodes; i++)
        if (ufind(i) == i) {
            nclasses++;
            uint32_t c = ncnt[i] < 63 ? ncnt[i] : 63;
            hist[c]++;
        }
    fprintf(stderr, "[classes] %u classes over %u nodes\n", nclasses, nnodes);
    for (int i = 1; i < 64; i++)
        if (hist[i]) fprintf(stderr, "  size %d: %llu\n", i, (unsigned long long)hist[i]);

    uint32_t eps_root = ufind(eps_node);
    int order_mult[D] = {0};
    for (int d = 1; d <= D; d++) {
        int order = 0;
        uint32_t roots[MAXW + 1];
        for (int k = 1; k <= MAXW; k++) {
            uint64_t c = 1;
            for (int i = 0; i < k; i++) c = c * 6 + (uint64_t)d;
            uint32_t n = hget(c);
            roots[k] = n ? ufind(n - 1) : UINT32_MAX;
            if (n && roots[k] == eps_root) {
                if (order == 0 || k < order) order = k;
            }
        }
        for (int a = 1; a <= MAXW; a++)
            for (int b = a + 1; b <= MAXW; b++)
                if (roots[a] != UINT32_MAX && roots[a] == roots[b]) {
                    int g = b - a;
                    order = order ? (order < g ? order : g) : g;
                }
        order_mult[d - 1] = order;
        fprintf(stderr, "[order] generator %d: order divides %s%d\n",
                d - 1, order ? "" : "unknown 0/", order);
    }
    fprintf(stderr, "orders:");
    for (int d = 0; d < D; d++) fprintf(stderr, " %d", order_mult[d]);
    fprintf(stderr, "\n");

    {
        uint32_t r = eps_root, cnt = 0;
        fprintf(stderr, "[eps] class size %u; shortest relators:\n", ncnt[r]);
        for (uint32_t m = r; m != UINT32_MAX && cnt < 20; m = nnxt[m]) {
            if (m == eps_node) continue;
            int l = wlen(ncode[m]);
            if (l <= 14) {
                uint8_t w[MAXW];
                wdec(ncode[m], l, w);
                fprintf(stderr, "  relator len %d: ", l);
                for (int i = 0; i < l; i++) fprintf(stderr, "%d", w[i]);
                fprintf(stderr, "\n");
                cnt++;
            }
        }
    }

    emit_relations(outpath, max_emit);

    fprintf(stderr, "[total] wall %lds\n", (long)(time(NULL) - t0));
    return 0;
}

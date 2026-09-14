#include "group.h"

#include <stdlib.h>
#include <string.h>

static gf343 add_table[GF343_Q][GF343_Q];
static gf343 mul_table[GF343_Q][GF343_Q];
static gf343 inv_table[GF343_Q];
static gf343 neg_table[GF343_Q];
static gf343 frobenius_table[GF343_Q];
static uint8_t square_table[GF343_Q];
/* Order and kind of a PSL element depend only on its trace invariant
 * tr^2/det, so both reduce to a table lookup.  Entries for non-square
 * invariants are unreachable and stay zero. */
static uint16_t order_by_invariant[GF343_Q];
static int8_t kind_by_invariant[GF343_Q];
static int initialized;

static gf343 encode(int a0, int a1, int a2) {
    a0 %= GF343_P; if (a0 < 0) a0 += GF343_P;
    a1 %= GF343_P; if (a1 < 0) a1 += GF343_P;
    a2 %= GF343_P; if (a2 < 0) a2 += GF343_P;
    return (gf343)(a0 + GF343_P * a1 + GF343_P * GF343_P * a2);
}

static void digits(gf343 a, int *a0, int *a1, int *a2) {
    *a0 = a % GF343_P;
    *a1 = (a / GF343_P) % GF343_P;
    *a2 = a / (GF343_P * GF343_P);
}

static gf343 add_slow(gf343 a, gf343 b) {
    int a0, a1, a2, b0, b1, b2;
    digits(a, &a0, &a1, &a2); digits(b, &b0, &b1, &b2);
    return encode(a0 + b0, a1 + b1, a2 + b2);
}

static gf343 mul_slow(gf343 a, gf343 b) {
    int a0, a1, a2, b0, b1, b2;
    digits(a, &a0, &a1, &a2); digits(b, &b0, &b1, &b2);
    return encode(a0 * b0 + 2 * (a1 * b2 + a2 * b1),
                  a0 * b1 + a1 * b0 + 2 * a2 * b2,
                  a0 * b2 + a1 * b1 + a2 * b0);
}

static gf343 pow_slow(gf343 a, unsigned exponent) {
    gf343 result = 1;
    while (exponent) {
        if (exponent & 1u) result = mul_slow(result, a);
        a = mul_slow(a, a);
        exponent >>= 1;
    }
    return result;
}

void psl2_343_init(void) {
    if (initialized) return;
    for (int a = 0; a < GF343_Q; a++)
        for (int b = 0; b < GF343_Q; b++) {
            add_table[a][b] = add_slow((gf343)a, (gf343)b);
            mul_table[a][b] = mul_slow((gf343)a, (gf343)b);
        }
    inv_table[0] = 0;
    for (int a = 0; a < GF343_Q; a++) {
        int a0, a1, a2;
        digits((gf343)a, &a0, &a1, &a2);
        neg_table[a] = encode(-a0, -a1, -a2);
        frobenius_table[a] = pow_slow((gf343)a, GF343_P);
        if (a) inv_table[a] = pow_slow((gf343)a, GF343_Q - 2);
    }
    square_table[0] = 1;
    for (int a = 1; a < GF343_Q; a++)
        square_table[a] = pow_slow((gf343)a, (GF343_Q - 1) / 2) == 1;
    initialized = 1;

    /* Companion matrices [[0,-1],[1,t]] have determinant one and trace t, so
     * they realize every reachable invariant t^2 exactly once. */
    static const unsigned orders[] = {1, 2, 3, 4, 7, 9, 19, 43, 57, 86, 171, 172};
    for (int t = 0; t < GF343_Q; t++) {
        psl2_343 m = {{0, neg_table[1], 1, (gf343)t}};
        if (!psl2_343_canonicalize(&m)) abort();
        gf343 invariant = mul_table[mul_table[t][t]][inv_table[psl2_343_det(m)]];
        for (size_t i = 0; i < sizeof(orders) / sizeof(orders[0]); i++)
            if (psl2_343_equal(psl2_343_pow(m, orders[i]), psl2_343_identity())) {
                order_by_invariant[invariant] = (uint16_t)orders[i];
                break;
            }
        gf343 discriminant = gf343_sub(mul_table[t][t],
                                       mul_table[4][psl2_343_det(m)]);
        kind_by_invariant[invariant] = (int8_t)(
            t == 0 && psl2_343_equal(m, psl2_343_identity())
                ? PSL2_343_KIND_IDENTITY
            : !discriminant ? PSL2_343_KIND_UNIPOTENT
            : square_table[discriminant] ? PSL2_343_KIND_SPLIT
                                         : PSL2_343_KIND_NONSPLIT);
    }
}

gf343 gf343_add(gf343 a, gf343 b) { return add_table[a][b]; }

gf343 gf343_neg(gf343 a) { return neg_table[a]; }

gf343 gf343_sub(gf343 a, gf343 b) { return gf343_add(a, gf343_neg(b)); }
gf343 gf343_mul(gf343 a, gf343 b) { return mul_table[a][b]; }

gf343 gf343_pow(gf343 a, unsigned exponent) {
    gf343 result = 1;
    while (exponent) {
        if (exponent & 1u) result = gf343_mul(result, a);
        a = gf343_mul(a, a);
        exponent >>= 1;
    }
    return result;
}

gf343 gf343_inv(gf343 a) {
    if (!a) abort();
    return inv_table[a];
}

int gf343_is_square(gf343 a) { return square_table[a]; }
gf343 gf343_frobenius(gf343 a) { return frobenius_table[a]; }

psl2_343 psl2_343_identity(void) {
    psl2_343 result = {{1, 0, 0, 1}};
    return result;
}

int psl2_343_equal(psl2_343 a, psl2_343 b) {
    return memcmp(a.v, b.v, sizeof(a.v)) == 0;
}

int psl2_343_canonicalize(psl2_343 *m) {
    gf343 pivot = 0;
    for (int i = 0; i < 4 && !pivot; i++) pivot = m->v[i];
    if (!pivot) return 0;
    gf343 scale = gf343_inv(pivot);
    for (int i = 0; i < 4; i++) m->v[i] = gf343_mul(scale, m->v[i]);
    return 1;
}

gf343 psl2_343_det(psl2_343 m) {
    return gf343_sub(gf343_mul(m.v[0], m.v[3]),
                     gf343_mul(m.v[1], m.v[2]));
}

gf343 psl2_343_trace(psl2_343 m) { return gf343_add(m.v[0], m.v[3]); }
int psl2_343_is_pgl(psl2_343 m) { return psl2_343_det(m) != 0; }
int psl2_343_is_psl(psl2_343 m) {
    gf343 det = psl2_343_det(m);
    return det && gf343_is_square(det);
}

psl2_343 psl2_343_mul(psl2_343 left, psl2_343 right) {
    psl2_343 result = {{
        gf343_add(gf343_mul(left.v[0], right.v[0]), gf343_mul(left.v[1], right.v[2])),
        gf343_add(gf343_mul(left.v[0], right.v[1]), gf343_mul(left.v[1], right.v[3])),
        gf343_add(gf343_mul(left.v[2], right.v[0]), gf343_mul(left.v[3], right.v[2])),
        gf343_add(gf343_mul(left.v[2], right.v[1]), gf343_mul(left.v[3], right.v[3]))
    }};
    if (!psl2_343_canonicalize(&result)) abort();
    return result;
}

psl2_343 psl2_343_compose(psl2_343 first, psl2_343 second) {
    return psl2_343_mul(second, first);
}

psl2_343 psl2_343_inverse(psl2_343 m) {
    if (!psl2_343_is_pgl(m)) abort();
    psl2_343 result = {{m.v[3], gf343_neg(m.v[1]),
                        gf343_neg(m.v[2]), m.v[0]}};
    if (!psl2_343_canonicalize(&result)) abort();
    return result;
}

psl2_343 psl2_343_pow(psl2_343 m, unsigned exponent) {
    psl2_343 result = psl2_343_identity();
    while (exponent) {
        if (exponent & 1u) result = psl2_343_mul(result, m);
        m = psl2_343_mul(m, m);
        exponent >>= 1;
    }
    return result;
}

/* The identity and the unipotent classes share the invariant 4, so it alone
 * cannot separate them; every other class is determined by the invariant. */
unsigned psl2_343_element_order(psl2_343 m) {
    if (!psl2_343_is_psl(m)) return 0;
    if (psl2_343_equal(m, psl2_343_identity())) return 1;
    return order_by_invariant[psl2_343_trace_invariant(m)];
}

int psl2_343_order_matches(psl2_343 m, unsigned order_multiple) {
    if (!order_multiple) return 1;
    return psl2_343_equal(
        psl2_343_pow(m, order_multiple), psl2_343_identity());
}

int psl2_343_element_kind(psl2_343 m) {
    if (!psl2_343_is_psl(m)) return -1;
    if (psl2_343_equal(m, psl2_343_identity())) return PSL2_343_KIND_IDENTITY;
    return kind_by_invariant[psl2_343_trace_invariant(m)];
}

gf343 psl2_343_trace_invariant(psl2_343 m) {
    gf343 trace = psl2_343_trace(m);
    return gf343_mul(gf343_mul(trace, trace), gf343_inv(psl2_343_det(m)));
}

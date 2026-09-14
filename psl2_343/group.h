#ifndef HENBANE_PSL2_343_H
#define HENBANE_PSL2_343_H

#include <stdint.h>

enum {
    GF343_P = 7,
    GF343_Q = 343
};

enum {
    PSL2_343_KIND_IDENTITY = 0,
    PSL2_343_KIND_NONSPLIT = 1,
    PSL2_343_KIND_UNIPOTENT = 2,
    PSL2_343_KIND_SPLIT = 3
};

#define PSL2_343_ORDER UINT32_C(20176632)
#define PGL2_343_ORDER UINT32_C(40353264)

typedef uint16_t gf343;

typedef struct {
    gf343 v[4];                 /* row-major a,b,c,d; projectively canonical */
} psl2_343;

void psl2_343_init(void);

gf343 gf343_add(gf343 a, gf343 b);
gf343 gf343_neg(gf343 a);
gf343 gf343_sub(gf343 a, gf343 b);
gf343 gf343_mul(gf343 a, gf343 b);
gf343 gf343_pow(gf343 a, unsigned exponent);
gf343 gf343_inv(gf343 a);
int gf343_is_square(gf343 a);
gf343 gf343_frobenius(gf343 a);

psl2_343 psl2_343_identity(void);
int psl2_343_equal(psl2_343 a, psl2_343 b);
int psl2_343_canonicalize(psl2_343 *m);
gf343 psl2_343_det(psl2_343 m);
gf343 psl2_343_trace(psl2_343 m);
int psl2_343_is_pgl(psl2_343 m);
int psl2_343_is_psl(psl2_343 m);
psl2_343 psl2_343_mul(psl2_343 left, psl2_343 right);
psl2_343 psl2_343_compose(psl2_343 first, psl2_343 second);
psl2_343 psl2_343_inverse(psl2_343 m);
psl2_343 psl2_343_pow(psl2_343 m, unsigned exponent);
/* `order_multiple=0` disables the g^k=1 filter. */
int psl2_343_order_matches(psl2_343 m, unsigned order_multiple);

unsigned psl2_343_element_order(psl2_343 m);
int psl2_343_element_kind(psl2_343 m);
gf343 psl2_343_trace_invariant(psl2_343 m);

#endif

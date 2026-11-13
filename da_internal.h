/* What the files of the library share and their users need not see:
   the 128-bit type, the layout of the representation, and the
   rounding of a fixed-point result. Not installed with dec-alpha.h. */
#ifndef DA_INTERNAL_H
#define DA_INTERNAL_H

#include "dec-alpha.h"

/* A 128-bit unsigned type is needed for access to the 64x64->128
   multiplication and 128/64->64 division that the host processor
   hopefully provides. Prefer the standard C23 type; fall back to the
   GCC/Clang extension for compilers that provide the latter but not the
   former. */
#if defined(__BITINT_MAXWIDTH__) && __BITINT_MAXWIDTH__ >= 128
typedef unsigned _BitInt(128) ulll;
#elif defined(__SIZEOF_INT128__)
typedef __uint128_t ulll;
#else
#error "DEC alpha needs a 128-bit unsigned integer type"
#endif

/* The number of bits of a nonzero x, from the standard C23 function,
   from the count of leading zeros that GCC and Clang provide before
   C23, or from a slow loop in plain C11. */
#if __STDC_VERSION__ >= 202311L
#include <stdbit.h>
#define bit_width(x) ((int)stdc_bit_width_ull(x))
#elif defined(__GNUC__)
#define bit_width(x) (64 - __builtin_clzll(x))
#else
static inline int bit_width(uint64_t x) {
  int w = 0;
  for (; x; x >>= 1) w++;
  return w;
}
#endif

#define DECADE_LO DA_DECADE_LO
#define DECADE_HI DA_DECADE_HI

/* After subtracting DECADE_LO from the representation of a normal da,
   shift by EXP_SHIFT to obtain the biased exponent: */
#define EXP_SHIFT 55
#define SIGN_MASK UINT64_C(0x8000000000000000)
#define SD_MASK ((UINT64_C(1) << EXP_SHIFT) - 1)

#define WRAP(sd, exp) \
  ((da){DECADE_LO \
        + ((sd - DECADE_LO) | (uint64_t)(exp) << EXP_SHIFT)})

/* The minimum unbiased exponent: */
#define EXP_MIN (-142)

/* The biased exponent of inf and NaN: */
#define EXP_INFNAN 255

#define HALF (UINT64_C(1) << 63) // half of 2^64, or one half in Q64
#define E14 UINT64_C(100000000000000)
#define E15 UINT64_C(1000000000000000)
#define E16 UINT64_C(10000000000000000)
#define E17 UINT64_C(100000000000000000)

/* The least Q64 fraction v at or above DECADE_LO 10^-16: v 10^16 has
   its integer part in a decade from there on, and v 10^17 below. */
#define VLO ((uint64_t)((((ulll)DECADE_LO << 64) + E16 - 1) / E16))

/* 10^n for n up to 19, the largest that fits in 64 bits, defined in
   dec-alpha.c: */
extern const uint64_t da_powers[20];

/* The inexact flag, raised where results are rounded when the file
   is compiled with DA_INEXACT defined, and untouched otherwise: */
#ifdef DA_INEXACT
#define INEXACT(cond) (da_inexact |= (cond))
#else
#define INEXACT(cond) ((void)0)
#endif

/* m and e such that the finite positive da of representation r is
   m 10^e, e being EXP_MIN for zero and the subnormals. */
static inline int split(uint64_t r, uint64_t *m) {
  int64_t o = (int64_t)r - (int64_t)DECADE_LO;
  if (o < 0) {
    *m = r;
    return EXP_MIN;
  }
  *m = DECADE_LO + (o & SD_MASK);
  return (int)(o >> EXP_SHIFT) + EXP_MIN;
}

/* The da nearest to n 2^-64 10^(exp-142), ties to even, the integer
   part of n 2^-64 being in a decade or the holes above it, or below
   the decade when exp is 0. */
static inline da nearest(ulll n, int exp) {
  uint64_t sd = n >> 64, rem = n;
  if (sd >= DECADE_HI) {
    // the candidates are DECADE_HI and the DECADE_LO of the next
    // decade, whose representation is the next one; the midpoint is
    // DECADE_HI + 4, on which DECADE_HI is the even one
    return (da){WRAP(DECADE_HI, exp).r
                + (n > (ulll)(DECADE_HI + 4) << 64)};
  }
  sd += (rem | sd & 1) > HALF; // ties to even, without a branch
  return WRAP(sd, exp);
}

#endif

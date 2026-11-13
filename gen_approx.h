/* What the generators share: the working precision, the rounding of
   a value to fixed point, and the fit of polynomials to functions by
   Remez's exchange. Qn denotes an integer standing for its quotient
   by 2^n. */
#ifndef GEN_APPROX_H
#define GEN_APPROX_H

#include <gmp.h>
#include <mpfr.h>

#define PRECISION 256
#define DEGREE_MAX 8 // the largest degree of a polynomial fitted

typedef void fn(mpfr_ptr y, mpfr_srcptr x);

/* Sets the precision of MPFR to PRECISION and initializes the
   variables of remez. */
void approx_init(void);

/* v as a Qn integer, rounded to nearest, ties to even, in i, which
   must fit in an int64_t or a uint64_t; returns the error in units. */
double q(mpz_t i, mpfr_srcptr v, int n);

/* Adds units of Qn to v: q then rounds it that far above the nearest,
   for a constant whose error makes up for truncations. */
void bias(mpfr_ptr v, double units, int n);

/* The polynomial p of n coefficients, highest degree first, with the
   least largest (p - f) weight on (0, top], for a positive weight, in
   c; and that largest error, returned. 0 is left out, where f, often
   a quotient by x, may be undefined. n is at most DEGREE_MAX + 1. */
double remez(mpfr_t *c, fn *f, fn *weight, mpfr_srcptr top, int n);

#endif

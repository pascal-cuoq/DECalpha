/* Random tests for da_sincos.c and da_log.c, with MPFR as the oracle.
   These functions are not correctly rounded: each documents a bound on
   its error, in units in the last place of the exact result. The test
   measures that error on random arguments, uniform or drawn around the
   hard cases, and reports for each function the largest error it met
   and the argument that produced it. Signs, zeros, infinities and NaNs
   must be the ones of the exact result, and the inexact flag is
   compared with what the theorems say when the library was built with
   it, and checked to stay clear otherwise. The first result that
   breaks one of these rules, or exceeds the bound, stops the test.

   The unit in the last place. Consecutive values have consecutive
   representations, so the exact result y has a position on the scale of
   the representations: lo + t, when it is the fraction t of the way from
   the value of representation lo to the next one. The error of a result
   of representation r is |r - lo - t|. As long as the result is one of
   the two neighbors of y, this is |result - y| in units of their
   distance, the unit in the last place of the exact result, of which the
   format has three in turn: 10^e inside a decade, 8 10^e in the gap from
   the top of the decade to the bottom of the next, where 7 significands
   are missing, then 10^(e+1). Past the neighbors, each interval crossed
   counts for one, whatever its width. So the correct rounding is always
   within 0.5, and only it is below 0.5: dividing by the unit of the exact
   result throughout would instead call a result 3 values below the gap
   0.44 off when y is just above the top of the decade. Decoding the
   representation of +inf as DECADE_LO 10^113 gives the last interval,
   and an exact result beyond it has the position of +inf.

   Build: cc -std=c11 -O2 test-math-random.c dec-alpha.o da_printing.o
             da_sincos.o da_log.o -lmpfr -lgmp
          with either build of the library
   Usage: ./test-math-random [seed] [count]
          (defaults: the time in seconds since 1970, and 2000) */

#include <math.h>
#include <stdio.h> /* before mpfr.h, which then declares mpfr_printf */
#include <mpfr.h>
#include "test-random.h"

#define E15 UINT64_C(1000000000000000)
#define E16 (10 * E15)
#define PREC 256 /* the working precision of the oracle, in bits */

/* y = x, to the precision of y */
static void fr_of(mpfr_t y, da x) {
  mpq_t q;
  if (is_nan(x.r)) {
    mpfr_set_nan(y);
    return;
  }
  if (is_inf(x.r)) {
    mpfr_set_inf(y, x.r & SIGN ? -1 : 1);
    return;
  }
  mpq_init(q);
  q_of(q, mag(x.r));
  if (x.r & SIGN) mpq_neg(q, q);
  mpfr_set_q(y, q, MPFR_RNDN);
  mpq_clear(q);
}

/* The error of the magnitude r as a result when the exact one is y, of
   the same sign, in units in the last place as defined above. A binary
   search over the representations finds the two neighbors of y, relying
   only on the encoding being monotone. */
static double ulps(uint64_t r, const mpfr_t y) {
  mpfr_t s;
  mpz_t z, w;
  mpfr_init2(s, PREC);
  mpz_inits(z, w, NULL);
  /* s is |y| at the scale of z_of */
  mpfr_mul_z(s, y, pow10z[BIAS], MPFR_RNDN);
  mpfr_abs(s, s, MPFR_RNDN);
  uint64_t lo = 0, hi = INF;
  double t = 0;
  z_of(z, INF);
  if (mpfr_cmp_z(s, z) >= 0) lo = INF;
  else {
    while (hi - lo > 1) {
      uint64_t mid = lo + (hi - lo) / 2;
      z_of(z, mid);
      if (mpfr_cmp_z(s, z) >= 0) lo = mid; else hi = mid;
    }
    z_of(z, lo);
    z_of(w, hi);
    mpz_sub(w, w, z);
    mpfr_sub_z(s, s, z, MPFR_RNDN);
    mpfr_div_z(s, s, w, MPFR_RNDN);
    t = mpfr_get_d(s, MPFR_RNDN);
  }
  mpfr_clear(s);
  mpz_clears(z, w, NULL);
  return fabs((double)(int64_t)(r - lo) - t);
}

/* ---- the oracles ----

   Each sets y to the exact result of x, as close as PREC bits allow,
   with the sign that a zero or an infinity must have, or to NaN, which
   is exact. Each returns whether the result is inexact, which no
   precision would tell: the theorems do. */

/* s and c = the sine and the cosine of x degrees, from one
   mpfr_sin_cos. The reduction is exact: |x| is k quarter turns plus r,
   from -45 to less than 45 degrees, so that a result near 0 is the sine
   of a small r, as precise as any other, and the sine and the cosine of
   r give those of |x|, swapped for an odd k and negated as the quarter
   turn k mod 4 requires. A zero is then +0, and the sine is negated for
   a negative x, as the library documents. By Niven's theorem, the sine
   of r is rational at 0 and ±30 degrees only, its cosine at 0, and
   their quotient at 0 and -45: returns those of the sine, the cosine
   and the tangent of x that are not, as bits 0, 1 and 2. */
static int sincosd(mpfr_t s, mpfr_t c, da x) {
  if (mag(x.r) >= INF) {
    mpfr_set_nan(s);
    mpfr_set_nan(c);
    return 0;
  }
  mpq_t r, t;
  mpz_t n;
  mpfr_t pi;
  mpq_inits(r, t, NULL);
  mpz_init(n);
  mpfr_init2(pi, PREC);
  q_of(r, mag(x.r));
  mpz_mul_ui(n, mpq_denref(r), 45);
  mpz_add(n, n, mpq_numref(r));
  mpz_fdiv_q(n, n, mpq_denref(r));
  mpz_fdiv_q_ui(n, n, 90);
  int k = (int)mpz_fdiv_ui(n, 4);
  mpz_mul_ui(n, n, 90);
  mpq_set_z(t, n);
  mpq_sub(r, r, t);
  mpfr_const_pi(pi, MPFR_RNDN);
  mpfr_set_q(s, r, MPFR_RNDN);
  mpfr_mul(s, s, pi, MPFR_RNDN);
  mpfr_div_ui(s, s, 180, MPFR_RNDN);
  mpfr_sin_cos(s, c, s, MPFR_RNDN);
  if (k & 1) mpfr_swap(s, c);
  if (k & 2) mpfr_neg(s, s, MPFR_RNDN);
  if (k + 1 & 2) mpfr_neg(c, c, MPFR_RNDN);
  if (mpfr_zero_p(s)) mpfr_set_zero(s, 1);
  if (mpfr_zero_p(c)) mpfr_set_zero(c, 1);
  if (x.r & SIGN) mpfr_neg(s, s, MPFR_RNDN);
  mpq_abs(t, r);
  int r0 = mpq_sgn(r) == 0, r30 = mpq_cmp_ui(t, 30, 1) == 0,
      r45 = mpq_cmp_ui(t, 45, 1) == 0;
  int sin_rational = r0 | r30 & !(k & 1);
  int cos_rational = r0 | r30 & k & 1;
  mpq_clears(r, t, NULL);
  mpz_clear(n);
  mpfr_clear(pi);
  return !sin_rational | !cos_rational << 1 | !(r0 | r45) << 2;
}

/* 10^x is rational for an integer x only, and then representable from
   10^-142 to 10^128; the limits at the infinities are exact. */
static int o_exp10(mpfr_t y, da x) {
  fr_of(y, x);
  int exact = !mpfr_number_p(y) || mpfr_integer_p(y)
              && mpfr_cmp_si(y, -BIAS) >= 0 && mpfr_cmp_si(y, 128) <= 0;
  mpfr_exp10(y, y, MPFR_RNDN);
  return !exact;
}

/* log10 x is rational for a power of ten only. A zero, an infinity
   and a negative x have exact results or none. */
static int o_log10(mpfr_t y, da x) {
  int inexact = 0;
  if (x.r - 1 < INF - 1) { // positive and finite
    mpz_t z;
    mpz_init(z);
    z_of(z, x.r);
    mpz_remove(z, z, pow10z[1]);
    inexact = mpz_cmp_ui(z, 1) != 0;
    mpz_clear(z);
  }
  fr_of(y, x);
  mpfr_log10(y, y, MPFR_RNDN);
  return inexact;
}

/* x radians in degrees, x times 180 / pi, irrational for a finite x
   other than zero, which keeps its sign: fr_of drops it. */
static int o_degrees(mpfr_t y, da x) {
  mpfr_t pi;
  mpfr_init2(pi, PREC);
  mpfr_const_pi(pi, MPFR_RNDN);
  fr_of(y, x);
  int inexact = mpfr_regular_p(y) != 0;
  mpfr_mul_ui(y, y, 180, MPFR_RNDN);
  mpfr_div(y, y, pi, MPFR_RNDN);
  if (mpfr_zero_p(y)) mpfr_setsign(y, y, x.r >> 63, MPFR_RNDN);
  mpfr_clear(pi);
  return inexact;
}

/* ---- random arguments ---- */

static da either_sign(da x) { return (da){x.r | rnd() & SIGN}; }

/* v 10^-15, rounded when v has more than 17 digits */
static da femto(uint64_t v) {
  return da_from_integer_and_biased_exp(v, BIAS - 15);
}

/* an argument for any function */
static da any(void) {
  static const uint64_t s[] = {0, 1, LO - 1, LO, INF - 1, INF, NAN_R};
  switch (below(4)) {
  case 0: return (da){rnd()}; /* any representation, 1 NaN in 256 */
  case 1: return either_sign((da){below(LO)}); /* 0 or subnormal */
  case 2: return either_sign((da){s[below(7)]});
  default: /* 1 to 3 digits */
    return either_sign(
      da_from_integer_and_biased_exp(below(1000), exp_rand()));
  }
}

static da arg_trig(void) {
  switch (below(5)) {
  case 0: return any();
  case 1: /* a multiple of 15 degrees, where the exact results are */
    return either_sign(da_from_integer_and_biased_exp(
      15 * below(1 << 26), BIAS + (int)below(3)));
  case 2: /* next to a multiple of 45 degrees: the folds, the poles */
    return either_sign(
      femto(45 * E15 * (1 + below(255)) + below(2001) - 1000));
  case 3: /* below 4.0032 degrees, down to 4e-45 */
    return either_sign(enc(sd_rand(), between(BIAS - 60, BIAS - 16)));
  default: /* within a turn */
    return either_sign(femto(below(360 * E15)));
  }
}

static da arg_exp10(void) {
  switch (below(5)) {
  case 0: return any();
  case 1: /* an integer, where the result is exact or out of range */
    return either_sign(da_from_integer(below(150)));
  case 2: /* below 0.04, down to 4e-27 */
    return either_sign(enc(sd_rand(), between(BIAS - 42, BIAS - 18)));
  case 3: { /* next to the thresholds of overflow and of underflow */
    da t = strtoda(coin() ? "128.6024072520796" : "-142.301029995664",
                   NULL);
    return (da){t.r + below(1001) - 500};
  }
  default: /* where the result is finite and not 0, or about */
    return either_sign(femto(below(144 * E15)));
  }
}

static da arg_log10(void) {
  switch (below(5)) {
  case 0: return any();
  case 1: /* a power of ten or next to one */
    return (da){enc(E16, exp_rand()).r + below(5) - 2};
  case 2: /* a subnormal power of ten */
    return (da){mpz_get_ui(pow10z[below(16)])};
  case 3: { /* next to 1, by 1e-16 to 0.45 */
    uint64_t k = rnd() >> between(12, 63);
    return enc(coin() ? E16 + k : E16 - k, BIAS - 16);
  }
  default: return (da){below(INF + 1)}; /* positive */
  }
}

static da arg_degrees(void) {
  switch (below(4)) {
  case 0: return any();
  case 1: /* 0 or subnormal */
    return either_sign((da){below(LO)});
  case 2: /* a result next to the top of a decade, where the error of
             the constant weighs the most, or to the largest value */
    return either_sign((da){enc(UINT64_C(6986901483484879),
                                exp_rand()).r - (rnd() >> 24)});
  default: return either_sign(enc(sd_rand(), exp_rand()));
  }
}

/* ---- the tests ---- */

/* whether da_sincos.c, da_log.c and dec-alpha.c, whose da_mult_integer
   rounds for da_degrees_of_radians, were built with the inexact flag:
   main probes the library. */
static int inexact_sincos, inexact_log, inexact_arith;

/* The functions, sin, cos and tan first, in the order of the bits of
   sincosd, which is their oracle: section_trig calls it. */
enum { SIN, COS, TAN };
static const struct fn {
  const char *name;
  da (*f)(da);
  int (*oracle)(mpfr_t, da);
  da (*arg)(void);
  double bound; /* the one dec-alpha.h documents */
  const int *raises;
} fns[] = {
  {"sin", da_sin, NULL, arg_trig, 0.504, &inexact_sincos},
  {"cos", da_cos, NULL, arg_trig, 0.504, &inexact_sincos},
  {"tan", da_tan, NULL, arg_trig, 0.519, &inexact_sincos},
  {"exp10", da_exp10, o_exp10, arg_exp10, 0.531, &inexact_log},
  {"log10", da_log10, o_log10, arg_log10, 0.511, &inexact_log},
  {"degrees", da_degrees_of_radians, o_degrees, arg_degrees, 0.503,
   &inexact_arith},
};

/* the largest error of a section and the argument that produced it */
struct worst { double err; da at; };

/* Checks got, returned for x with the inexact flag left at flag, as
   the result of f, whose exact value y and inexactness the oracle has
   given: a NaN must be returned as it is, a NaN from another argument
   must be DA_NAN, and any other result must have the sign of the exact
   one and be within the bound. */
static void check(const struct fn *f, da x, da got, int flag,
                  const mpfr_t y, int inexact, struct worst *w) {
  const char *why = 0;
  double err = 0;
  checks++;
  if (is_nan(x.r)) {
    if (got.r != x.r) why = "a NaN argument must be returned";
  } else {
    if (mpfr_nan_p(y)) {
      if (got.r != NAN_R) why = "the result must be DA_NAN";
    } else if (is_nan(got.r)) why = "NaN for a number";
    else if (got.r >> 63 != !!mpfr_signbit(y)) why = "wrong sign";
    else {
      err = ulps(mag(got.r), y);
      if (err > w->err) *w = (struct worst){err, x};
      if (err > f->bound) why = "error above the bound";
    }
  }
  int want_flag = *f->raises & inexact;
  if (!why && flag != want_flag) why = "wrong inexact flag";
  if (unlikely(why)) {
    failure(f->name, why);
    show("x", x);
    show("got", got);
    mpfr_printf("  exact = %.25Rg, error %.5f, bound %.3f\n", y, err,
                f->bound);
    printf("  inexact flag %d, want %d\n", flag, want_flag);
    stop();
  }
}

static void report(const char *name, long n, double bound,
                   struct worst w) {
  printf("%-7s %7ld checks, bound %.3f, worst %.5f at 0x%016" PRIx64
         " = ", name, n, bound, w.err, w.at.r);
  da_print(w.at);
  puts("");
}

/* n random arguments for the function f */
static void section(const struct fn *f, long n) {
  struct worst w = {0, DA_ZERO};
  mpfr_t y;
  mpfr_init2(y, PREC);
  for (long i = 0; i < n; i++) {
    da x = f->arg();
    da_inexact = 0;
    da got = f->f(x);
    int flag = da_inexact;
    check(f, x, got, flag, y, f->oracle(y, x), &w);
  }
  mpfr_clear(y);
  report(f->name, n, f->bound, w);
}

/* n random angles for da_sin, da_cos, da_tan and da_sincos at once,
   against one call of sincosd, the exact tangent being the quotient of
   the exact sine and cosine, whose zeros and infinities then have the
   signs the library documents. The first three are checked and
   reported as above, each with its own worst case, and the pair must
   be the sine and the cosine, with the flag raised when either raises
   it. */
static void section_trig(long n) {
  struct worst w[3] = {{0, DA_ZERO}, {0, DA_ZERO}, {0, DA_ZERO}};
  mpfr_t y[3];
  mpfr_inits2(PREC, y[SIN], y[COS], y[TAN], (mpfr_ptr)0);
  for (long i = 0; i < n; i++) {
    da x = arg_trig(), got[3];
    int flag[3];
    for (int op = SIN; op <= TAN; op++) {
      da_inexact = 0;
      got[op] = fns[op].f(x);
      flag[op] = da_inexact;
    }
    da_inexact = 0;
    da_pair pair = da_sincos(x);
    int pair_flag = da_inexact;
    int irrational = sincosd(y[SIN], y[COS], x);
    mpfr_div(y[TAN], y[SIN], y[COS], MPFR_RNDN);
    for (int op = SIN; op <= TAN; op++)
      check(&fns[op], x, got[op], flag[op], y[op],
            irrational >> op & 1, &w[op]);
    checks++;
    if (likely(pair.sin.r == got[SIN].r && pair.cos.r == got[COS].r
               && pair_flag == (flag[SIN] | flag[COS])))
      continue;
    failure("sincos", "the pair must be da_sin and da_cos, with the "
            "flag of either");
    show("x", x);
    show("sin", pair.sin);
    show("want", got[SIN]);
    show("cos", pair.cos);
    show("want", got[COS]);
    printf("  inexact flag %d, want %d\n", pair_flag,
           flag[SIN] | flag[COS]);
    stop();
  }
  mpfr_clears(y[SIN], y[COS], y[TAN], (mpfr_ptr)0);
  for (int op = SIN; op <= TAN; op++)
    report(fns[op].name, n, fns[op].bound, w[op]);
}

int main(int argc, char **argv) {
  long n = setup(argc, argv);
  /* a probe of each file: the sine and the logarithm of 2 */
  da two = da_from_integer(2);
  da_inexact = 0;
  da_sin(two);
  inexact_sincos = da_inexact;
  da_inexact = 0;
  da_log10(two);
  inexact_log = da_inexact;
  da_inexact = 0;
  da_div(two, da_from_integer(3));
  inexact_arith = da_inexact;
  printf("seed %" PRIu64 ", inexact flag %s in da_sincos.c, %s in "
         "da_log.c, %s in dec-alpha.c\n", seed,
         inexact_sincos ? "on" : "off", inexact_log ? "on" : "off",
         inexact_arith ? "on" : "off");
  section_trig(n);
  for (size_t i = TAN + 1; i < sizeof fns / sizeof *fns; i++)
    section(&fns[i], n);
  printf("math: %ld checks, all passed\n", checks);
  return 0;
}

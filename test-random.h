/* What the random tests, test-random.c and test-math-random.c, share:
   the layout of the representation, its decoding into GMP integers and
   rationals, the random generator, and the start of main. */
#ifndef TEST_RANDOM_H
#define TEST_RANDOM_H

#include <gmp.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "dec-alpha.h"

#define SIGN UINT64_C(0x8000000000000000)
/* as integer constants, usable in static initializers; setup checks
   them */
#define INF (UINT64_C(0x7f80000000000000) + LO)
#define NAN_R (INF + 1)
#define LO DA_DECADE_LO
#define HI DA_DECADE_HI
#define EXP_SHIFT 55
#define SD_MASK ((UINT64_C(1) << EXP_SHIFT) - 1)
#define BIAS 142
#define NPOW 512

static mpz_t pow10z[NPOW]; /* 10^0 .. 10^(NPOW-1) */

static inline void set_u64(mpz_t z, uint64_t v) {
  mpz_import(z, 1, 1, sizeof v, 0, 0, &v);
}

/* out = num * 10^pow, pow of either sign */
static inline void set_q(mpq_t out, const mpz_t num, int pow) {
  if (pow >= 0) {
    mpz_mul(mpq_numref(out), num, pow10z[pow]);
    mpz_set_ui(mpq_denref(out), 1);
  }
  else {
    mpz_set(mpq_numref(out), num);
    mpz_set(mpq_denref(out), pow10z[-pow]);
  }
  mpq_canonicalize(out);
}

static inline uint64_t mag(uint64_t r) { return r & ~SIGN; }
static inline int is_nan(uint64_t r) { return mag(r) > INF; }
static inline int is_inf(uint64_t r) { return mag(r) == INF; }

/* The encoding of a normal value. */
static inline da enc(uint64_t sd, int e) {
  return (da){LO + ((sd - LO) | ((uint64_t)e << EXP_SHIFT))};
}

/* z = the value of the magnitude r (no sign bit, at most INF) times
   10^142, which is the integer sd * 10^e. Decoding INF this way gives
   LO * 10^113, the value that would follow the largest finite one: it is
   the threshold above which results overflow, midpoint rule included. */
static inline void z_of(mpz_t z, uint64_t r) {
  if (r < LO) {
    set_u64(z, r);
    return;
  }
  uint64_t o = r - LO;
  set_u64(z, LO + (o & SD_MASK));
  mpz_mul(z, z, pow10z[o >> EXP_SHIFT]);
}

/* q = the value of the magnitude r */
static inline void q_of(mpq_t q, uint64_t r) {
  mpz_t z;
  mpz_init(z);
  z_of(z, r);
  set_q(q, z, -BIAS);
  mpz_clear(z);
}

/* ---- reporting ---- */

/* As in Linux: the branch the compiler should lay out as the
   fall-through, here the success of a check. __has_builtin, in GCC 10
   and Clang, tells whether __builtin_expect exists; an older GCC has
   it without the test. It must be nested: a preprocessor without
   __has_builtin cannot parse __has_builtin(...) even after a false
   operand of &&. Elsewhere, the hint is dropped. */
#if defined __has_builtin
#if __has_builtin(__builtin_expect)
#define HAVE_BUILTIN_EXPECT
#endif
#elif defined __GNUC__
#define HAVE_BUILTIN_EXPECT
#endif
#ifdef HAVE_BUILTIN_EXPECT
#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
#else
#define likely(x) (x)
#define unlikely(x) (x)
#endif

static long checks;
static uint64_t seed; /* the seed of the generator, set by setup() */

/* The banner of a failure, before the caller shows the argument and
   the results, and the end of the program after them: the first
   failure stops it, with the seed that repeats the run. */
static inline void failure(const char *op, const char *why) {
  printf("\n*** FAILURE of %s: %s ***\n", op, why);
}
static inline void stop(void) {
  printf("*** STOPPED at the first failure, after %ld checks: "
         "seed %" PRIu64 " repeats it ***\n", checks, seed);
  exit(1);
}

static inline void show(const char *what, da d) {
  printf("  %5s = 0x%016" PRIx64 " = ", what, d.r);
  da_print(d);
  puts("");
}

/* ---- random inputs ---- */

static uint64_t state;

static inline uint64_t rnd(void) { /* splitmix64 */
  uint64_t z = (state += UINT64_C(0x9e3779b97f4a7c15));
  z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
  return z ^ (z >> 31);
}

static inline uint64_t below(uint64_t n) { return rnd() % n; }
static inline int between(int a, int b) {
  return a + (int)below(b - a + 1);
}
static inline int coin(void) { return rnd() >> 63; }
static inline int exp_rand(void) { return (int)below(255); }
static inline uint64_t sd_rand(void) { return LO + below(HI - LO + 1); }

/* The start of main, for the usage [seed] [count]: seeds the generator,
   with the time in seconds since 1970 by default, fills the table of
   powers and returns the count, 2000 by default. The caller prints the
   seed, kept in seed, without which a failing run cannot be
   repeated. */
static inline long setup(int argc, char **argv) {
  seed = state = argc > 1 ? strtoull(argv[1], NULL, 0)
                          : (uint64_t)time(NULL);
  if (unlikely(INF != DA_INFINITY.r || NAN_R != DA_NAN.r)) {
    puts("constants out of sync with dec-alpha.h");
    exit(1);
  }
  mpz_init_set_ui(pow10z[0], 1);
  for (int i = 1; i < NPOW; i++) {
    mpz_init(pow10z[i]);
    mpz_mul_ui(pow10z[i], pow10z[i - 1], 10);
  }
  return argc > 2 ? strtol(argv[2], NULL, 0) : 2000;
}

#endif

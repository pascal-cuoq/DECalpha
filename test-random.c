/* Random tests for dec-alpha.c, with GMP rationals as the oracle. Every
   result of the library is compared with the correct rounding of the exact
   rational result, which the function nearest() computes from the format's
   definition alone, without any arithmetic of its own. Operands are drawn
   at random, uniformly or constructed around the hard cases: ties, decade
   boundaries, cancellation, subnormals, overflow. The fixed tests, with
   expected results written by hand, are in test-fixed.c.

   Build: cc -std=c11 -O2 test-random.c dec-alpha.o -lgmp
   Usage: ./test-random [seed] [count]         (defaults: 1 and 2000) */

#include <gmp.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "dec-alpha.h"

#define SIGN UINT64_C(0x8000000000000000)
/* as integer constants, usable in static initializers; main checks them */
#define INF (UINT64_C(0x7f80000000000000) + LO)
#define NAN_R (INF + 1)
#define LO DA_DECADE_LO
#define HI DA_DECADE_HI
#define EXP_SHIFT 55
#define SD_MASK ((UINT64_C(1) << EXP_SHIFT) - 1)
#define BIAS 142
#define NPOW 512

static mpz_t pow10z[NPOW]; /* 10^0 .. 10^(NPOW-1) */

static void set_u64(mpz_t z, uint64_t v) {
  mpz_import(z, 1, 1, sizeof v, 0, 0, &v);
}

/* out = num * 10^pow, pow of either sign */
static void set_q(mpq_t out, const mpz_t num, int pow) {
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

static uint64_t mag(uint64_t r) { return r & ~SIGN; }
static int is_nan(uint64_t r) { return mag(r) > INF; }
static int is_inf(uint64_t r) { return mag(r) == INF; }
static da signed_da(uint64_t m, int neg) { return (da){m | (neg ? SIGN : 0)}; }

/* The encoding of a normal value. */
static da enc(uint64_t sd, int e) {
  return (da){LO + ((sd - LO) | ((uint64_t)e << EXP_SHIFT))};
}

/* z = the value of the magnitude r (no sign bit, at most INF) times 10^142,
   which is the integer sd * 10^e. Decoding INF this way gives LO * 10^113,
   the value that would follow the largest finite one: it is the threshold
   above which results overflow, midpoint rule included. */
static void z_of(mpz_t z, uint64_t r) {
  if (r < LO) {
    set_u64(z, r);
    return;
  }
  uint64_t o = r - LO;
  set_u64(z, LO + (o & SD_MASK));
  mpz_mul(z, z, pow10z[o >> EXP_SHIFT]);
}

/* q = the value of the magnitude r */
static void q_of(mpq_t q, uint64_t r) {
  mpz_t z;
  mpz_init(z);
  z_of(z, r);
  set_q(q, z, -BIAS);
  mpz_clear(z);
}

static long ties; /* exact midpoints met by nearest() */

/* Is key(r) <= s, where key(r) is z(r), or z(r)^2 in square mode? */
static int key_le(uint64_t r, const mpq_t s, int square, mpz_t z) {
  z_of(z, r);
  if (square) mpz_mul(z, z, z);
  return mpq_cmp_z(s, z) >= 0;
}

/* The oracle: the representation of the non-negative value nearest to q,
   ties to even, or INF when q rounds beyond the largest finite value. In
   square mode, nearest to sqrt(q) instead. Works by binary search over the
   representations, relying only on the encoding being monotone (which
   test_roundtrip checks). The even representation among two neighbors is the
   even integer: LO is odd and each decade holds 2^55 significands, so the
   parity of a representation is that of its significand. */
static uint64_t nearest(const mpq_t q, int square) {
  mpq_t s;
  mpz_t z, zm;
  mpq_init(s);
  mpz_inits(z, zm, NULL);
  /* s is q at the scale of z: q * 10^142, or q * 10^284 in square mode */
  mpq_set_z(s, pow10z[square ? 2 * BIAS : BIAS]);
  mpq_mul(s, s, q);
  uint64_t lo = 0, hi = INF, res;
  if (key_le(INF, s, square, z))
    res = INF;
  else {
    while (hi - lo > 1) {
      uint64_t mid = lo + (hi - lo) / 2;
      if (key_le(mid, s, square, z)) lo = mid; else hi = mid;
    }
    /* key(lo) <= s < key(hi). Compare with the midpoint m = (v(lo)+v(hi))/2:
       2s against z(lo)+z(hi), or in square mode 4s against (z(lo)+z(hi))^2,
       which is four times the square of the midpoint. */
    z_of(z, lo);
    z_of(zm, hi);
    mpz_add(zm, zm, z);
    if (square) {
      mpz_mul(zm, zm, zm);
      mpq_mul_2exp(s, s, 2);
    }
    else
      mpq_mul_2exp(s, s, 1);
    int c = mpq_cmp_z(s, zm);
    if (c == 0) ties++;
    res = c < 0 || c == 0 && lo % 2 == 0 ? lo : hi;
  }
  mpq_clear(s);
  mpz_clears(z, zm, NULL);
  return res;
}

/* nearest to m * 10^(e-142) */
static da mk(uint64_t m, int e) {
  mpz_t z;
  mpq_t q;
  mpz_init(z);
  mpq_init(q);
  set_u64(z, m);
  set_q(q, z, e - BIAS);
  da d = (da){nearest(q, 0)};
  mpz_clear(z);
  mpq_clear(q);
  return d;
}

/* ---- oracles for the operations, following the README ---- */

static da o_add(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  if (is_nan(x)) return dx;
  if (is_nan(y)) return dy;
  if (is_inf(x) && is_inf(y)) return x == y ? dx : DA_NAN;
  if (is_inf(x)) return dx;
  if (is_inf(y)) return dy;
  mpq_t qx, qy;
  mpq_inits(qx, qy, NULL);
  q_of(qx, mag(x));
  if (x & SIGN) mpq_neg(qx, qx);
  q_of(qy, mag(y));
  if (y & SIGN) mpq_neg(qy, qy);
  mpq_add(qx, qx, qy);
  /* an exact zero is +0 unless both operands are -0; a nonzero sum cannot
     round to zero, all values being multiples of the smallest subnormal */
  int neg = mpq_sgn(qx) ? mpq_sgn(qx) < 0 : x == SIGN && y == SIGN;
  mpq_abs(qx, qx);
  da d = signed_da(nearest(qx, 0), neg);
  mpq_clears(qx, qy, NULL);
  return d;
}

static da o_mult(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  if (is_nan(x)) return dx;
  if (is_nan(y)) return dy;
  int neg = ((x ^ y) & SIGN) != 0;
  if (is_inf(x) || is_inf(y)) {
    if (mag(x) == 0 || mag(y) == 0) return DA_NAN;
    return signed_da(INF, neg);
  }
  mpq_t qx, qy;
  mpq_inits(qx, qy, NULL);
  q_of(qx, mag(x));
  q_of(qy, mag(y));
  mpq_mul(qx, qx, qy);
  da d = signed_da(nearest(qx, 0), neg);
  mpq_clears(qx, qy, NULL);
  return d;
}

static da o_div(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  if (is_nan(x)) return dx;
  if (is_nan(y)) return dy;
  int neg = ((x ^ y) & SIGN) != 0;
  uint64_t mx = mag(x), my = mag(y);
  if (mx == INF && my == INF || mx == 0 && my == 0) return DA_NAN;
  if (mx == INF || my == 0) return signed_da(INF, neg);
  if (my == INF || mx == 0) return signed_da(0, neg);
  mpq_t qx, qy;
  mpq_inits(qx, qy, NULL);
  q_of(qx, mx);
  q_of(qy, my);
  mpq_div(qx, qx, qy);
  da d = signed_da(nearest(qx, 0), neg);
  mpq_clears(qx, qy, NULL);
  return d;
}

static da o_sqrt(da dx) {
  uint64_t x = dx.r;
  if (is_nan(x) || mag(x) == 0 || x == INF) return dx;
  if (x & SIGN) return DA_NAN;
  mpq_t q;
  mpq_init(q);
  q_of(q, x);
  da d = (da){nearest(q, 1)};
  mpq_clear(q);
  return d;
}

/* x * y + z from the exact rational, with the sign rules of addition */
static da o_fma(da dx, da dy, da dz) {
  uint64_t x = dx.r, y = dy.r, z = dz.r;
  if (mag(x) >= INF || mag(y) >= INF || mag(z) >= INF)
    return o_add(o_mult(dx, dy), dz);
  mpq_t q, t;
  mpq_inits(q, t, NULL);
  q_of(q, mag(x));
  q_of(t, mag(y));
  mpq_mul(q, q, t);
  if ((x ^ y) & SIGN) mpq_neg(q, q);
  q_of(t, mag(z));
  if (z & SIGN) mpq_neg(t, t);
  mpq_add(q, q, t);
  int neg = mpq_sgn(q) ? mpq_sgn(q) < 0 : ((x ^ y) & z & SIGN) != 0;
  mpq_abs(q, q);
  da d = signed_da(nearest(q, 0), neg);
  mpq_clears(q, t, NULL);
  return d;
}

/* the multiple of 10^e nearest to x, ties to even, then rounded */
static da o_quantize(da dx, int e) {
  uint64_t x = dx.r;
  if (mag(x) >= INF) return dx;
  /* beyond these, every value is a multiple of 10^e, or below 10^e / 2 */
  if (e < -300) return dx;
  if (e > 300) return (da){x & SIGN};
  mpq_t q;
  mpz_t n, r;
  mpq_init(q);
  mpz_inits(n, r, NULL);
  q_of(q, mag(x));
  if (e >= 0) mpz_mul(mpq_denref(q), mpq_denref(q), pow10z[e]);
  else mpz_mul(mpq_numref(q), mpq_numref(q), pow10z[-e]);
  mpq_canonicalize(q); // q is now |x| / 10^e
  mpz_fdiv_qr(n, r, mpq_numref(q), mpq_denref(q));
  mpz_mul_2exp(r, r, 1);
  int c = mpz_cmp(r, mpq_denref(q));
  if (c == 0) ties++;
  if (c > 0 || c == 0 && mpz_odd_p(n)) mpz_add_ui(n, n, 1);
  set_q(q, n, e);
  da d = signed_da(nearest(q, 0), (x & SIGN) != 0);
  mpq_clear(q);
  mpz_clears(n, r, NULL);
  return d;
}

/* ---- reporting ---- */

static long checks, failures;

static void show(const char *what, da d) {
  printf("  %4s = 0x%016" PRIx64 " = ", what, d.r);
  da_print(d);
  puts("");
}

static void check(const char *op, da x, const da *y, da got, da want) {
  checks++;
  if (got.r == want.r) return;
  failures++;
  printf("FAIL %s\n", op);
  show("x", x);
  if (y) show("y", *y);
  show("got", got);
  show("want", want);
  if (failures >= 50) {
    puts("too many failures, stopping");
    exit(1);
  }
}

static void check2(const char *op, da x, da y, da got, da want) {
  check(op, x, &y, got, want);
}

static void check1(const char *op, da x, da got, da want) {
  check(op, x, NULL, got, want);
}

static void check3(const char *op, da x, da y, da z, da got, da want) {
  long f = failures;
  check(op, x, &y, got, want);
  if (failures > f) show("z", z);
}

/* ---- random inputs ---- */

static uint64_t state;

static uint64_t rnd(void) { /* splitmix64 */
  uint64_t z = (state += UINT64_C(0x9e3779b97f4a7c15));
  z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
  return z ^ (z >> 31);
}

static uint64_t below(uint64_t n) { return rnd() % n; }
static int between(int a, int b) { return a + (int)below(b - a + 1); }
static int coin(void) { return rnd() >> 63; }
static int exp_rand(void) { return (int)below(255); }
static uint64_t sd_rand(void) { return LO + below(HI - LO + 1); }

/* a significand at a decade edge, a round number or the boundary midpoint */
static uint64_t sd_edge(void) {
  static const uint64_t base[] = {
    LO, HI, UINT64_C(5000000000000000), UINT64_C(10000000000000000),
    UINT64_C(20000000000000000), UINT64_C(20015998343868873),
    UINT64_C(10007999171934436), UINT64_C(8006399337547550)};
  uint64_t sd = base[below(8)] + below(5) - 2;
  return sd < LO ? LO : sd > HI ? HI : sd;
}

/* a significand with a particular arithmetic structure */
static uint64_t sd_shaped(void) {
  uint64_t sd = sd_rand();
  switch (below(4)) {
  case 0: return sd | 1;                               /* odd */
  case 1: return sd & ~(UINT64_C(0xffff) >> below(16)); /* trailing zero bits */
  case 2: { uint64_t p = mpz_get_ui(pow10z[between(1, 15)]); sd -= sd % p;
            return sd < LO ? sd + p : sd; }             /* trailing zero digits */
  default: return sd - sd % 5 + 5 <= HI ? sd - sd % 5 + 5 : sd; /* multiple of 5 */
  }
}

/* a magnitude (no sign bit), finite, infinite or NaN */
static uint64_t mag_rand(void) {
  switch (below(8)) {
  case 0: return rnd() >> 1;                        /* anything, NaNs included */
  case 1: return below(INF + 1);                    /* uniform in representation */
  case 2: return below(LO);                         /* zero or subnormal */
  case 3: return enc(sd_edge(), exp_rand()).r;
  case 4: return enc(sd_rand(), between(120, 165)).r; /* 1e-22 .. 1e23 */
  case 5: return mk(1 + below(999), exp_rand()).r;  /* few significant digits */
  case 6: {
    static const uint64_t s[] = {0, 1, 2, LO - 1, LO, INF - 1, INF, NAN_R};
    return coin() ? s[below(8)] : INF + 1 + below(1000);
  }
  default: return enc(sd_shaped(), exp_rand()).r;
  }
}

static da da_rand(void) { return signed_da(mag_rand(), coin()); }
static da finite_rand(void) {
  uint64_t m;
  do m = mag_rand(); while (m >= INF);
  return signed_da(m, coin());
}
static da special_rand(void) {
  static const uint64_t s[] = {0, SIGN, INF, INF | SIGN, NAN_R};
  return coin() ? (da){s[below(5)]} : signed_da(INF + 1 + below(1 << 20), coin());
}

/* Random biased exponents with e1 + e2 (sign 1) or e1 - e2 (sign -1) in
   [lo, hi] when the ranges allow. */
static void exps(int *e1, int *e2, int sign, int lo, int hi) {
  *e1 = exp_rand();
  int a = sign > 0 ? lo - *e1 : *e1 - hi, b = sign > 0 ? hi - *e1 : *e1 - lo;
  if (a < 0) a = 0;
  if (a > 254) a = 254;
  if (b > 254) b = 254;
  if (b < a) b = a;
  *e2 = between(a, b);
}

/* ---- the tests ---- */

/* The oracle must send each finite value back to its representation. This
   checks the decoding against the binary search, and the encoding's
   monotonicity, on which everything else relies. */
static void test_roundtrip(long n) {
  mpq_t q;
  mpq_init(q);
  for (long i = 0; i < n; i++) {
    uint64_t r = below(INF + 1);
    if (coin()) r = mag_rand() % (INF + 1);
    q_of(q, r);
    check1("oracle roundtrip", (da){r}, (da){nearest(q, 0)}, (da){r});
  }
  mpq_clear(q);
}

static void test_from_integer(long n) {
  for (long i = 0; i < n; i++) {
    uint64_t v;
    switch (i % 5) {
    case 0: v = rnd(); break;
    case 1: v = below(1000000); break;
    case 2: v = 10 * (LO + below(UINT64_C(20000000000000000) - LO)) + 5; break;
    case 3: v = (HI + between(1, 9)) * mpz_get_ui(pow10z[below(3)]); break;
    default: v = sd_edge() * mpz_get_ui(pow10z[below(4)]); break;
    }
    int e = i % 3 == 0 ? exp_rand() : between(0, 2) * 127;
    check2("from_integer_and_biased_exp", (da){v}, (da){(uint64_t)e},
           da_from_integer_and_biased_exp(v, e), mk(v, e));
    if (i % 4 == 0)
      check1("from_integer", (da){v}, da_from_integer(v), mk(v, BIAS));
  }
}

static void test_add(long n) {
  for (long i = 0; i < n; i++) {
    da x, y;
    int e;
    switch (i % 7) {
    case 0: x = da_rand(); y = da_rand(); break;
    case 1: /* exact or near cancellation */
      x = finite_rand();
      y = signed_da(mag(x.r) + below(3) - (mag(x.r) > 0), !(x.r & SIGN));
      break;
    case 2: /* y is half a unit of x, or less: ties and near-ties */
      e = between(1, 254);
      x = signed_da(enc(sd_rand(), e).r, coin());
      y = signed_da(mk(coin() ? 5 : between(1, 9), e - (coin() ? 1 : between(1, 4))).r,
                    coin());
      break;
    case 3: /* around a decade boundary */
      e = between(1, 254);
      x = signed_da(enc(coin() ? HI : LO, e).r, coin());
      y = signed_da(mk(between(1, 9), e - coin()).r, coin());
      break;
    case 4: /* exponent gaps around the cutoff */
      e = between(20, 254);
      x = signed_da(enc(coin() ? sd_edge() : sd_rand(), e).r, coin());
      y = signed_da(enc(coin() ? sd_edge() : sd_rand(), e - between(14, 19)).r,
                    coin());
      break;
    case 5: /* subnormals and the lowest decades */
      x = signed_da(below(LO), coin());
      y = signed_da(coin() ? below(LO) : enc(sd_rand(), between(0, 2)).r, coin());
      break;
    default: x = special_rand(); y = da_rand(); break;
    }
    check2("add", x, y, da_add(x, y), o_add(x, y));
    check2("add", y, x, da_add(y, x), o_add(y, x));
  }
}

static void test_mult(long n) {
  for (long i = 0; i < n; i++) {
    da x, y;
    int e1, e2;
    switch (i % 7) {
    case 0: x = da_rand(); y = da_rand(); break;
    case 1: /* (2t+1) * 5 = 10t + 5, the midpoint between t and t+1 */
      exps(&e1, &e2, 1, 125 - 17, 125 + 255);
      x = signed_da(enc(2 * (LO + below(UINT64_C(20000000000000000) - LO)) + 1,
                        e1).r, coin());
      y = signed_da(mk(5, e2).r, coin());
      break;
    case 2: /* decade boundaries: HI * m, LO * m, and 2 * 20015998343868873 */
      exps(&e1, &e2, 1, 125 - 17, 125 + 255);
      x = signed_da(enc(sd_edge(), e1).r, coin());
      y = signed_da(mk(between(1, 99), e2).r, coin());
      break;
    case 3: /* subnormal results */
      exps(&e1, &e2, 1, 100, 145);
      x = signed_da(enc(coin() ? sd_edge() : sd_rand(), e1).r, coin());
      y = signed_da(enc(coin() ? sd_edge() : sd_rand(), e2).r, coin());
      break;
    case 4: /* near overflow */
      exps(&e1, &e2, 1, 372, 384);
      x = signed_da(enc(coin() ? sd_edge() : sd_rand(), e1).r, coin());
      y = signed_da(enc(coin() ? sd_edge() : sd_rand(), e2).r, coin());
      break;
    case 5: /* a subnormal operand */
      x = signed_da(below(LO), coin());
      y = signed_da(enc(sd_rand(), between(200, 254)).r, coin());
      break;
    default: x = special_rand(); y = da_rand(); break;
    }
    check2("mult", x, y, da_mult(x, y), o_mult(x, y));
    check2("mult", y, x, da_mult(y, x), o_mult(y, x));
  }
}

static void test_div(long n) {
  for (long i = 0; i < n; i++) {
    da x, y;
    int e1, e2;
    switch (i % 7) {
    case 0: x = da_rand(); y = da_rand(); break;
    case 1: { /* (2t+1) 2^(k-1) / 2^k = t + 1/2, a midpoint */
      int k = between(1, 3);
      uint64_t t = LO + below(UINT64_C(40000000000000000) / (2 << (k - 1)) - LO);
      exps(&e1, &e2, -1, 255 - 127, 17 - 127 + 1);
      x = signed_da(enc((2 * t + 1) << (k - 1), e1).r, coin());
      y = signed_da(mk(UINT64_C(1) << k, e2).r, coin());
      break;
    }
    case 2: /* decade boundaries, including 20015998343868873 / 5 */
      exps(&e1, &e2, -1, 255 - 127, 17 - 127 + 1);
      x = signed_da(enc(sd_edge(), e1).r, coin());
      y = signed_da(mk(between(1, 99), e2).r, coin());
      break;
    case 3: /* subnormal divisor or dividend */
      x = signed_da(1 + below(LO - 1), coin());
      y = signed_da(enc(coin() ? sd_edge() : sd_rand(), between(0, 254)).r, coin());
      break;
    case 4: /* results near the underflow and overflow thresholds */
      if (coin()) exps(&e1, &e2, -1, -17 - 127, 2 - 127);
      else exps(&e1, &e2, -1, 252 - 127, 256 - 127);
      x = signed_da(enc(coin() ? sd_edge() : sd_rand(), e1).r, coin());
      y = signed_da(enc(coin() ? sd_edge() : sd_rand(), e2).r, coin());
      break;
    case 5: /* exact quotients: m * y / y */
      y = finite_rand();
      x = o_mult(y, mk(between(1, 999), BIAS));
      break;
    default: x = special_rand(); y = da_rand(); break;
    }
    check2("div", x, y, da_div(x, y), o_div(x, y));
    check2("div", y, x, da_div(y, x), o_div(y, x));
  }
}

static void test_sqrt(long n) {
  mpz_t z;
  mpq_t q;
  mpz_init(z);
  mpq_init(q);
  for (long i = 0; i < n; i++) {
    da x;
    switch (i % 6) {
    case 0: x = da_rand(); break;
    case 1: { /* exact squares, in a decade or subnormal */
      uint64_t a = coin() ? (uint64_t)between(63271633, 200079975) : below(63271633);
      x = mk(a * a, exp_rand());
      break;
    }
    case 2: case 3: { /* the value nearest to the square of a midpoint (t+1/2)
      * 10^k, and its neighbors, at both exponent parities */
      uint64_t t = i % 6 == 2 ? sd_rand() : sd_edge();
      set_u64(z, 2 * t + 1);
      mpz_mul(z, z, z);
      set_q(q, z, 2 * between(0, 126) + coin() - BIAS);
      mpq_div_2exp(q, q, 2);
      x = (da){nearest(q, 0) + below(3) - 1};
      break;
    }
    case 4: x = (da){coin() ? below(LO) : enc(sd_rand(), between(0, 3)).r}; break;
    default: x = coin() ? special_rand() : signed_da(mag_rand(), 1); break;
    }
    check1("sqrt", x, da_sqrt(x), o_sqrt(x));
  }
  mpz_clear(z);
  mpq_clear(q);
}

/* a and b (representations, a < b <= INF) are adjacent if the midpoint of
   their values, nudged by less than any gap, rounds to each of them */
static void check_adjacent(const char *op, da x, uint64_t a, uint64_t b) {
  mpq_t qa, qb, tiny;
  mpz_t one;
  mpq_inits(qa, qb, tiny, NULL);
  mpz_init_set_ui(one, 1);
  set_q(tiny, one, -300);
  q_of(qa, a);
  q_of(qb, b);
  mpq_add(qa, qa, qb);
  mpq_div_2exp(qa, qa, 1);
  mpq_sub(qb, qa, tiny);
  check1(op, x, (da){nearest(qb, 0)}, (da){a});
  mpq_add(qb, qa, tiny);
  check1(op, x, (da){nearest(qb, 0)}, (da){b});
  mpq_clears(qa, qb, tiny, NULL);
  mpz_clear(one);
}

static void test_succ_pred(long n) {
  for (long i = 0; i < n; i++) {
    uint64_t r = i % 2 ? mag_rand() : below(INF + 1);
    da x = {r}, nx = da_neg(x), s = da_succ(x), p = da_pred(x);
    check1("neg", x, nx, (da){r ^ SIGN});
    if (r > INF) { /* NaN */
      check1("succ", x, s, x);
      check1("pred", x, p, x);
    }
    else if (r == INF) {
      check1("succ", x, s, x);
      check_adjacent("pred", x, p.r, INF);
    }
    else {
      check_adjacent("succ", x, r, s.r);
      /* as nextDown(+0) in IEEE 754, pred(+0) is the smallest negative
         subnormal, -0 not being less than +0 */
      if (r == 0) check1("pred", x, p, (da){SIGN | 1});
      else check_adjacent("pred", x, p.r, r);
    }
    /* the negative side mirrors the positive one */
    check1("succ", nx, da_succ(nx), da_neg(p));
    check1("pred", nx, da_pred(nx), da_neg(s));
  }
}

/* The oracle for strtoda: an independent parse of the same syntax with
   every digit kept, the value being digits * 10^(exp - fraction digits). */
static da o_strtoda(const char *str) {
  const char *s = str;
  int neg = *s == '-';
  if (*s == '-' || *s == '+') s++;
  char digits[400] = "0";
  int nd = 0, frac = 0;
  long scale = 0;
  for (; *s; s++) {
    if (*s == '.') { frac = 1; continue; }
    if (*s < '0' || *s > '9') break;
    if (nd || *s != '0') digits[nd++] = *s;
    scale -= frac;
  }
  if (nd) digits[nd] = 0;
  if (*s == 'e' || *s == 'E') scale += strtol(s + 1, NULL, 10);
  mpz_t z;
  mpq_t q;
  mpz_init_set_str(z, digits, 10);
  mpq_init(q);
  if (scale > 400) scale = 400;
  if (scale < -400) scale = -400;
  set_q(q, z, (int)scale);
  da d = signed_da(nearest(q, 0), neg);
  mpz_clear(z);
  mpq_clear(q);
  return d;
}

/* a random number in the syntax strtoda accepts, built from a random value
   with a random layout: leading zeros, point position, exponent, and digits
   beyond the nineteen that are kept exactly */
static void random_numeral(char *buf) {
  char *p = buf;
  if (coin()) *p++ = coin() ? '-' : '+';
  int lead = coin() ? 0 : between(0, 30);
  while (lead--) *p++ = '0';
  char mant[80];
  int n;
  switch (below(5)) {
  case 0: n = sprintf(mant, "%" PRIu64, rnd()); break;
  case 1: n = sprintf(mant, "%" PRIu64, sd_edge()); break;
  case 2: n = sprintf(mant, "%" PRIu64 "5", coin() ? sd_rand() : sd_edge());
    break; /* a midpoint */
  case 3: /* a midpoint followed by digits, decisive or not */
    n = sprintf(mant, "%" PRIu64 "5%0*d%d", coin() ? sd_rand() : sd_edge(),
                between(0, 30), 0, (int)below(2));
    break;
  default: n = sprintf(mant, "%" PRIu64 "%" PRIu64, rnd(), rnd()); break;
  }
  int point = coin() ? -1 : between(0, n);
  for (int i = 0; i < n; i++) {
    if (i == point) *p++ = '.';
    *p++ = mant[i];
  }
  if (point == n) *p++ = '.';
  if (coin()) {
    int e = coin() ? between(-160, 145) : between(-400, 400);
    p += sprintf(p, "%c%s%d", coin() ? 'e' : 'E', e >= 0 && coin() ? "+" : "", e);
  }
  *p = 0;
}

static void test_strtoda(long n) {
  char buf[160];
  for (long i = 0; i < n; i++) {
    random_numeral(buf);
    char *end;
    da got = strtoda(buf, &end);
    da want = o_strtoda(buf);
    if (got.r != want.r || *end) {
      failures++;
      printf("FAIL strtoda \"%s\"\n", buf);
      show("got", got);
      show("want", want);
    }
    checks++;
  }
}

/* The total order, stated directly: a sign difference decides, positive
   values follow their magnitude and negative ones reverse it. */
static int o_total_order(da x, da y) {
  int nx = x.r >> 63, ny = y.r >> 63;
  if (nx != ny) return nx ? -1 : 1;
  uint64_t mx = mag(x.r), my = mag(y.r);
  return nx ? (mx < my) - (mx > my) : (mx > my) - (mx < my);
}

static int o_compare(da x, da y) {
  if (is_nan(x.r) || is_nan(y.r)) return DA_UNORDERED;
  mpq_t qx, qy;
  mpq_inits(qx, qy, NULL);
  q_of(qx, mag(x.r));
  if (x.r & SIGN) mpq_neg(qx, qx);
  q_of(qy, mag(y.r));
  if (y.r & SIGN) mpq_neg(qy, qy);
  int c = mpq_cmp(qx, qy);
  mpq_clears(qx, qy, NULL);
  return (c > 0) - (c < 0);
}

static void test_compare(long n) {
  for (long i = 0; i < n; i++) {
    da x = da_rand(), y;
    switch (i % 5) {
    case 0: y = da_rand(); break;
    case 1: y = x; break;
    case 2: y = da_neg(x); break;
    case 3: y = coin() ? da_succ(x) : da_pred(x); break;
    default: y = special_rand(); break;
    }
    if (i % 7 == 0) x = special_rand();
    check2("compare", x, y, (da){da_compare(x, y)}, (da){o_compare(x, y)});
    check2("total_order", x, y, (da){da_total_order(x, y)},
           (da){o_total_order(x, y)});
  }
}

static void test_fma(long n) {
  for (long i = 0; i < n; i++) {
    da x, y, z;
    int e1, e2;
    switch (i % 8) {
    case 0: x = da_rand(); y = da_rand(); z = da_rand(); break;
    case 1: /* the rounding error of a product: z cancels most of x * y */
      x = finite_rand();
      y = finite_rand();
      z = da_neg(da_mult(x, y));
      if (coin()) z = coin() ? da_succ(z) : da_pred(z);
      break;
    case 2: /* a product on a midpoint, z deciding the tie or absent */
      exps(&e1, &e2, 1, 125 - 17, 125 + 255);
      x = signed_da(enc(2 * (LO + below(UINT64_C(20000000000000000) - LO)) + 1,
                        e1).r, coin());
      y = signed_da(mk(5, e2).r, coin());
      z = coin() ? signed_da(coin() ? 1 : mag_rand() % (INF + 1), coin())
                 : (da){coin() ? 0 : SIGN};
      break;
    case 3: { /* z large, the product at half a unit of z or nearby */
      int e = between(17, 254);
      z = signed_da(enc(coin() ? sd_edge() : sd_rand(), e).r, coin());
      x = signed_da(mk(5, e - 1 - below(3)).r, coin());
      y = signed_da(mk(1 + below(3) * 4, BIAS).r, coin()); /* 1, 5 or 9 */
      if (coin()) x = coin() ? da_succ(x) : da_pred(x);
      break;
    }
    case 4: /* small products and subnormal results */
      x = signed_da(below(LO), coin());
      y = signed_da(enc(sd_rand(), between(100, 200)).r, coin());
      z = signed_da(coin() ? below(LO) : enc(sd_rand(), between(0, 20)).r, coin());
      break;
    case 5: /* overflow region */
      exps(&e1, &e2, 1, 372, 384);
      x = signed_da(enc(sd_rand(), e1).r, coin());
      y = signed_da(enc(sd_rand(), e2).r, coin());
      z = signed_da(enc(sd_rand(), between(240, 254)).r, coin());
      break;
    case 6: /* wide exponent gaps in both directions */
      x = signed_da(enc(sd_rand(), exp_rand()).r, coin());
      y = signed_da(enc(sd_rand(), exp_rand()).r, coin());
      z = signed_da(enc(sd_rand(), exp_rand()).r, coin());
      break;
    default:
      x = special_rand(); y = da_rand(); z = da_rand();
      if (coin()) { da t = x; x = z; z = t; }
      break;
    }
    check3("fma", x, y, z, da_fma(x, y, z), o_fma(x, y, z));
    check3("fma", y, x, z, da_fma(y, x, z), o_fma(y, x, z));
  }
}

static void test_quantize(long n) {
  for (long i = 0; i < n; i++) {
    da x = i % 5 ? finite_rand() : da_rand();
    int e;
    switch (i % 5) {
    case 0: e = between(-160, 140); break;
    case 4: { /* a tie: the dropped digits of x are 5 followed by zeros */
      int d = between(1, 16), ex = exp_rand();
      uint64_t p = mpz_get_ui(pow10z[d]), sd = sd_rand() / p * p + p / 2;
      x = signed_da(enc(sd < LO ? sd + p : sd, ex).r, coin());
      e = ex - BIAS + d;
      break;
    }
    case 1: /* around the unit of x */
      e = (int)(mag(x.r) < LO ? 0 : ((mag(x.r) - LO) >> EXP_SHIFT)) - BIAS
          + between(-2, 20);
      break;
    case 2: e = coin() ? between(-2, 2) : between(-1000000, 1000000); break;
    default: e = coin() ? 2147483647 : -2147483647 - 1; break;
    }
    check2("quantize", x, (da){(uint64_t)(int64_t)e}, da_quantize(x, e),
           o_quantize(x, e));
  }
}

/* ---- main ---- */

static void section(const char *name, void (*f)(long), long n) {
  long c = checks, t = ties;
  f(n);
  printf("%-16s %8ld checks %6ld ties\n", name, checks - c, ties - t);
}

int main(int argc, char **argv) {
  state = argc > 1 ? strtoull(argv[1], NULL, 0) : 1;
  long n = argc > 2 ? strtol(argv[2], NULL, 0) : 2000;
  if (INF != DA_INFINITY.r || NAN_R != DA_NAN.r) {
    puts("constants out of sync with dec-alpha.h");
    return 1;
  }
  mpz_init_set_ui(pow10z[0], 1);
  for (int i = 1; i < NPOW; i++) {
    mpz_init(pow10z[i]);
    mpz_mul_ui(pow10z[i], pow10z[i - 1], 10);
  }
  section("roundtrip", test_roundtrip, n);
  section("from_integer", test_from_integer, n);
  section("add", test_add, n);
  section("mult", test_mult, n);
  section("div", test_div, n);
  section("sqrt", test_sqrt, n);
  section("succ/pred", test_succ_pred, n);
  section("strtoda", test_strtoda, n);
  section("compare", test_compare, n);
  section("fma", test_fma, n);
  section("quantize", test_quantize, n);
  printf("random: %ld checks, %ld failures\n", checks, failures);
  return failures != 0;
}

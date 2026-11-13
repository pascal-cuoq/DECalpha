/* Random tests for dec-alpha.c, with GMP rationals as the oracle. Every
   result of the library is compared with the correct rounding of the exact
   rational result, which the function nearest() computes from the format's
   definition alone, without any arithmetic of its own. Operands are drawn
   at random, uniformly or constructed around the hard cases: ties, decade
   boundaries, cancellation, subnormals, overflow. The printing functions
   are compared with glibc's printf instead. The inexact flag is compared
   with the oracle's when the library was built with it, and checked to
   stay clear otherwise. The first failure stops the test. The fixed
   tests, with expected results written by hand, are in test-fixed.c.

   Build: cc -std=c11 -O2 test-random.c dec-alpha.o da_printing.o -lgmp
          with either build of the library
   Usage: ./test-random [seed] [count]
          (defaults: the time in seconds since 1970, and 2000) */

#include <math.h>
#include <string.h>
#include "test-random.h"

static da signed_da(uint64_t m, int neg) {
  return (da){m | (neg ? SIGN : 0)};
}

static long ties; /* exact midpoints met by nearest() */
/* the oracle's inexact flag, raised by nearest() as the library raises
   da_inexact, and compared with it by check() after a rounding
   operation */
static int o_inexact;

/* The sign of s - key(r), where key(r) is z(r), or z(r)^2 in square
   mode. */
static int key_cmp(uint64_t r, const mpq_t s, int square, mpz_t z) {
  z_of(z, r);
  if (square) mpz_mul(z, z, z);
  return mpq_cmp_z(s, z);
}

/* The oracle: the representation of the non-negative value nearest to q,
   ties to even, or INF when q rounds beyond the largest finite value. In
   square mode, nearest to sqrt(q) instead. Works by binary search over the
   representations, relying only on the encoding being monotone (which
   test_roundtrip checks). The even representation among two neighbors is
   the even integer: LO is odd and each decade holds 2^55 significands, so
   the parity of a representation is that of its significand. */
static uint64_t nearest(const mpq_t q, int square) {
  mpq_t s;
  mpz_t z, zm;
  mpq_init(s);
  mpz_inits(z, zm, NULL);
  /* s is q at the scale of z: q * 10^142, or q * 10^284 in square mode */
  mpq_set_z(s, pow10z[square ? 2 * BIAS : BIAS]);
  mpq_mul(s, s, q);
  uint64_t lo = 0, hi = INF, res;
  if (key_cmp(INF, s, square, z) >= 0) {
    res = INF;
    o_inexact = 1;
  }
  else {
    while (hi - lo > 1) {
      uint64_t mid = lo + (hi - lo) / 2;
      if (key_cmp(mid, s, square, z) >= 0) lo = mid; else hi = mid;
    }
    /* key(lo) <= s < key(hi): the result is exact, and lo, when key(lo)
       is s. Otherwise compare with the midpoint m = (v(lo)+v(hi))/2: 2s
       against z(lo)+z(hi), or in square mode 4s against (z(lo)+z(hi))^2,
       which is four times the square of the midpoint. */
    o_inexact |= key_cmp(lo, s, square, z) != 0;
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

/* x * y + z from the exact rational, with the sign rules of addition. A
   special z alone is the result, the product not rounding. */
static da o_fma(da dx, da dy, da dz) {
  uint64_t x = dx.r, y = dy.r, z = dz.r;
  if (mag(x) >= INF || mag(y) >= INF) return o_add(o_mult(dx, dy), dz);
  if (mag(z) >= INF) return dz;
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

/* x * y * 10^z from the exact rational, y being a positive zero when
   it is 0 */
static da o_mult_integer(da dx, int64_t y, int z) {
  uint64_t x = dx.r;
  if (is_nan(x)) return dx;
  int neg = ((x & SIGN) != 0) != (y < 0);
  if (is_inf(x)) return y ? signed_da(INF, neg) : DA_NAN;
  /* beyond these, a nonzero result is infinite or zero whatever x and y
     are, as it already is at them */
  if (z > 400) z = 400;
  if (z < -400) z = -400;
  mpz_t n;
  mpq_t q, t;
  mpz_init(n);
  mpq_inits(q, t, NULL);
  q_of(q, mag(x));
  set_u64(n, y < 0 ? -(uint64_t)y : (uint64_t)y);
  set_q(t, n, z);
  mpq_mul(q, q, t);
  da d = signed_da(nearest(q, 0), neg);
  mpz_clear(n);
  mpq_clears(q, t, NULL);
  return d;
}

/* the multiple of 10^e next to x in the direction of mode, then rounded */
static da o_quantize(da dx, int e, int mode) {
  uint64_t x = dx.r;
  int neg = (x & SIGN) != 0;
  /* the directed modes that round away from zero */
  int away = mode == DA_AWAY_FROM_ZERO
             || mode == (neg ? DA_TOWARD_NEGATIVE : DA_TOWARD_POSITIVE);
  if (mag(x) >= INF) return dx;
  /* beyond these, every value is a multiple of 10^e, or below 10^e / 2,
     and 10^e is beyond the largest finite value */
  if (e < -300) return dx;
  if (e > 300) {
    o_inexact |= mag(x) != 0;
    return (da){mag(x) && away ? x & SIGN | INF : x & SIGN};
  }
  mpq_t q;
  mpz_t n, r;
  mpq_init(q);
  mpz_inits(n, r, NULL);
  q_of(q, mag(x));
  if (e >= 0) mpz_mul(mpq_denref(q), mpq_denref(q), pow10z[e]);
  else mpz_mul(mpq_numref(q), mpq_numref(q), pow10z[-e]);
  mpq_canonicalize(q); // q is now |x| / 10^e
  mpz_fdiv_qr(n, r, mpq_numref(q), mpq_denref(q));
  o_inexact |= mpz_sgn(r) != 0;
  mpz_mul_2exp(r, r, 1);
  int c = mpz_cmp(r, mpq_denref(q));
  if (c == 0) ties++;
  int up;
  switch (mode) {
  case DA_TIES_TO_EVEN: up = c > 0 || c == 0 && mpz_odd_p(n); break;
  case DA_TIES_TO_AWAY: up = c >= 0; break;
  default: up = away && mpz_sgn(r) != 0;
  }
  if (up) mpz_add_ui(n, n, 1);
  set_q(q, n, e);
  da d = signed_da(nearest(q, 0), neg);
  mpq_clear(q);
  mpz_clears(n, r, NULL);
  return d;
}

/* ---- reporting ---- */

/* whether dec-alpha.c and da_printing.c were built with the inexact flag:
   main probes the library. If so, the flag must be raised exactly when the
   oracle raises its own, and otherwise it must never be touched. */
static int inexact_arith, inexact_printf;
static int flagged; /* set by ROUNDING for check() to compare the flags */

/* got, the result of op on x and on y and z when they are not null,
   must be want, with the inexact flag of the oracle in a rounding
   operation */
static void check(const char *op, da x, const da *y, const da *z,
                  da got, da want) {
  checks++;
  int want_flag = inexact_arith && o_inexact;
  int flag_ok = !flagged || da_inexact == want_flag;
  if (likely(got.r == want.r && flag_ok)) return;
  failure(op, got.r != want.r ? "wrong result" : "wrong inexact flag");
  show("x", x);
  if (y) show("y", *y);
  if (z) show("z", *z);
  show("got", got);
  show("want", want);
  if (!flag_ok)
    printf("  inexact flag %d, want %d\n", da_inexact, want_flag);
  stop();
}

static void check1(const char *op, da x, da got, da want) {
  check(op, x, NULL, NULL, got, want);
}

static void check2(const char *op, da x, da y, da got, da want) {
  check(op, x, &y, NULL, got, want);
}

static void check3(const char *op, da x, da y, da z, da got, da want) {
  check(op, x, &y, &z, got, want);
}

/* The check of an operation that rounds: both inexact flags are cleared
   before the library and the oracle run, in whichever order the
   arguments are evaluated, and check() compares them. */
#define ROUNDING(check_call) \
  (da_inexact = o_inexact = 0, flagged = 1, check_call, flagged = 0)

/* ---- random inputs ---- */

/* a significand at a decade edge, a round number or the boundary
   midpoint */
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
  case 0: /* odd */
    return sd | 1;
  case 1: /* trailing zero bits */
    return sd & ~(UINT64_C(0xffff) >> below(16));
  case 2: { /* trailing zero digits */
    uint64_t p = mpz_get_ui(pow10z[between(1, 15)]);
    sd -= sd % p;
    return sd < LO ? sd + p : sd;
  }
  default: /* a multiple of 5 */
    return sd - sd % 5 + 5 <= HI ? sd - sd % 5 + 5 : sd;
  }
}

/* a magnitude (no sign bit), finite, infinite or NaN */
static uint64_t mag_rand(void) {
  switch (below(8)) {
  case 0: return rnd() >> 1; /* anything, NaNs included */
  case 1: return below(INF + 1); /* uniform in representation */
  case 2: return below(LO); /* zero or subnormal */
  case 3: return enc(sd_edge(), exp_rand()).r;
  case 4: return enc(sd_rand(), between(120, 165)).r; /* 1e-22 .. 1e23 */
  case 5: return mk(1 + below(999), exp_rand()).r; /* 1 to 3 digits */
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
  return coin() ? (da){s[below(5)]}
                : signed_da(INF + 1 + below(1 << 20), coin());
}

/* Random biased exponents with e1 + e2 (sign 1) or e1 - e2 (sign -1) in
   [lo, hi] when the ranges allow. */
static void exps(int *e1, int *e2, int sign, int lo, int hi) {
  *e1 = exp_rand();
  int a = sign > 0 ? lo - *e1 : *e1 - hi;
  int b = sign > 0 ? hi - *e1 : *e1 - lo;
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
    case 1: v = coin() ? below(1000000) : rnd() >> below(64); break;
    case 2:
      v = 10 * (LO + below(UINT64_C(20000000000000000) - LO)) + 5;
      break;
    case 3: v = (HI + between(1, 9)) * mpz_get_ui(pow10z[below(3)]); break;
    default: v = sd_edge() * mpz_get_ui(pow10z[below(4)]); break;
    }
    int e = i % 3 == 0 ? exp_rand() : between(0, 2) * 127;
    ROUNDING(check2("from_integer_and_biased_exp", (da){v},
                    (da){(uint64_t)e},
                    da_from_integer_and_biased_exp(v, e), mk(v, e)));
    if (i % 4 == 0)
      ROUNDING(check1("from_integer", (da){v}, da_from_integer(v),
                      mk(v, BIAS)));
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
      y = signed_da(mk(coin() ? 5 : between(1, 9),
                       e - (coin() ? 1 : between(1, 4))).r, coin());
      break;
    case 3: /* around a decade boundary */
      e = between(1, 254);
      x = signed_da(enc(coin() ? HI : LO, e).r, coin());
      y = signed_da(mk(between(1, 9), e - coin()).r, coin());
      break;
    case 4: /* exponent gaps around the cutoff */
      e = between(20, 254);
      x = signed_da(enc(coin() ? sd_edge() : sd_rand(), e).r, coin());
      y = signed_da(enc(coin() ? sd_edge() : sd_rand(),
                        e - between(14, 19)).r, coin());
      break;
    case 5: /* subnormals and the lowest decades */
      x = signed_da(below(LO), coin());
      y = signed_da(coin() ? below(LO) : enc(sd_rand(), between(0, 2)).r,
                    coin());
      break;
    default: x = special_rand(); y = da_rand(); break;
    }
    ROUNDING(check2("add", x, y, da_add(x, y), o_add(x, y)));
    ROUNDING(check2("add", y, x, da_add(y, x), o_add(y, x)));
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
      x = signed_da(enc(2 * (LO + below(UINT64_C(20000000000000000) - LO))
                        + 1, e1).r, coin());
      y = signed_da(mk(5, e2).r, coin());
      break;
    case 2: /* decade boundaries: HI * m, LO * m, 2 * 20015998343868873 */
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
    ROUNDING(check2("mult", x, y, da_mult(x, y), o_mult(x, y)));
    ROUNDING(check2("mult", y, x, da_mult(y, x), o_mult(y, x)));
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
      uint64_t t =
        LO + below(UINT64_C(40000000000000000) / (2 << (k - 1)) - LO);
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
      y = signed_da(enc(coin() ? sd_edge() : sd_rand(), between(0, 254)).r,
                    coin());
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
    ROUNDING(check2("div", x, y, da_div(x, y), o_div(x, y)));
    ROUNDING(check2("div", y, x, da_div(y, x), o_div(y, x)));
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
      uint64_t a = coin() ? (uint64_t)between(63271633, 200079975)
                          : below(63271633);
      x = mk(a * a, exp_rand());
      break;
    }
    case 2: case 3: { /* the value nearest to the square of a midpoint
      (t+1/2) * 10^k, and its neighbors, at both exponent parities */
      uint64_t t = i % 6 == 2 ? sd_rand() : sd_edge();
      set_u64(z, 2 * t + 1);
      mpz_mul(z, z, z);
      set_q(q, z, 2 * between(0, 126) + coin() - BIAS);
      mpq_div_2exp(q, q, 2);
      x = (da){nearest(q, 0) + below(3) - 1};
      break;
    }
    case 4:
      x = (da){coin() ? below(LO) : enc(sd_rand(), between(0, 3)).r};
      break;
    default: x = coin() ? special_rand() : signed_da(mag_rand(), 1); break;
    }
    ROUNDING(check1("sqrt", x, da_sqrt(x), o_sqrt(x)));
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
   every digit kept, the value being digits * 10^(exp - fraction
   digits). */
static da o_strtoda(const char *str) {
  const char *s = str;
  char c = *s;
  int neg = c == '-';
  if (c == '-' || c == '+') s++;
  char digits[400] = "0";
  int nd = 0, frac = 0;
  long scale = 0;
  for (; c = *s; s++) {
    if (c == '.') { frac = 1; continue; }
    if (c < '0' || c > '9') break;
    if (nd || c != '0') digits[nd++] = c;
    scale -= frac;
  }
  if (nd) digits[nd] = 0;
  if (c == 'e' || c == 'E') scale += strtol(s + 1, NULL, 10);
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

/* a random number in the syntax strtoda accepts, built from a random
   value with a random layout: leading zeros, point position, exponent,
   and digits beyond the nineteen that are kept exactly */
static void random_numeral(char *buf) {
  char *p = buf;
  if (coin()) {
    *p = coin() ? '-' : '+';
    p++;
  }
  int lead = coin() ? 0 : between(0, 30);
  memset(p, '0', lead);
  p += lead;
  char mant[80];
  int n;
  switch (below(5)) {
  case 0: n = sprintf(mant, "%" PRIu64, rnd()); break;
  case 1: n = sprintf(mant, "%" PRIu64, sd_edge()); break;
  case 2: /* a midpoint */
    n = sprintf(mant, "%" PRIu64 "5", coin() ? sd_rand() : sd_edge());
    break;
  case 3: /* a midpoint followed by digits, decisive or not */
    n = sprintf(mant, "%" PRIu64 "5%0*d%d", coin() ? sd_rand() : sd_edge(),
                between(0, 30), 0, (int)below(2));
    break;
  default: n = sprintf(mant, "%" PRIu64 "%" PRIu64, rnd(), rnd()); break;
  }
  int point = coin() ? -1 : between(0, n);
  p += point < 0 ? sprintf(p, "%s", mant)
                 : sprintf(p, "%.*s.%s", point, mant, mant + point);
  if (coin()) {
    int e = coin() ? between(-160, 145) : between(-400, 400);
    p += sprintf(p, "%c%s%d", coin() ? 'e' : 'E',
                 e >= 0 && coin() ? "+" : "", e);
  }
  *p = 0;
}

static void test_strtoda(long n) {
  char buf[160];
  for (long i = 0; i < n; i++) {
    random_numeral(buf);
    char *end;
    da_inexact = o_inexact = 0;
    da got = strtoda(buf, &end);
    da want = o_strtoda(buf);
    int want_flag = inexact_arith && o_inexact;
    checks++;
    if (unlikely(got.r != want.r || *end || da_inexact != want_flag)) {
      failure("strtoda", got.r != want.r ? "wrong result"
                         : *end ? "numeral not consumed to the end"
                                : "wrong inexact flag");
      printf("  numeral \"%s\", consumed %d\n", buf, (int)(end - buf));
      show("got", got);
      show("want", want);
      printf("  inexact flag %d, want %d\n", da_inexact, want_flag);
      stop();
    }
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
      x = signed_da(enc(2 * (LO + below(UINT64_C(20000000000000000) - LO))
                        + 1, e1).r, coin());
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
      z = signed_da(coin() ? below(LO) : enc(sd_rand(), between(0, 20)).r,
                    coin());
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
    ROUNDING(check3("fma", x, y, z, da_fma(x, y, z), o_fma(x, y, z)));
    ROUNDING(check3("fma", y, x, z, da_fma(y, x, z), o_fma(y, x, z)));
  }
}

/* an integer of any number of bits up to 63, of either sign */
static int64_t y_rand(void) {
  int64_t a = (int64_t)(rnd() >> between(1, 63));
  return coin() ? a : -a;
}

/* the number of decimal digits of y, 0 for 0 */
static int digits(int64_t y) {
  int d = 0;
  for (; y; y /= 10) d++;
  return d;
}

static void test_mult_integer(long n) {
  for (long i = 0; i < n; i++) {
    da x;
    int64_t y = y_rand();
    int z, e = exp_rand();
    switch (i % 8) {
    case 0: x = da_rand(); z = between(-60, 60); break;
    case 1: { /* (2t+1) * 5 = 10t + 5, a midpoint, in every decade */
      int k = (int)below(19);
      x = signed_da(enc(2 * (LO + below(UINT64_C(20000000000000000) - LO))
                        + 1, e).r, coin());
      y = (int64_t)(5 * mpz_get_ui(pow10z[k])) * (coin() ? 1 : -1);
      z = between(-20, 260) - e - k;
      break;
    }
    case 2: /* decade boundaries: HI * m, LO * m, 2 * 20015998343868873 */
      x = signed_da(enc(sd_edge(), e).r, coin());
      y = between(-99, 99) * (int64_t)mpz_get_ui(pow10z[below(17)]);
      z = between(-3, 3);
      break;
    case 3: /* subnormal results and underflow */
      x = signed_da(enc(coin() ? sd_edge() : sd_rand(), e).r, coin());
      z = between(-20, 4) - e - digits(y);
      break;
    case 4: /* near overflow */
      x = signed_da(enc(coin() ? sd_edge() : sd_rand(), e).r, coin());
      z = 254 + between(-3, 3) - e - digits(y);
      break;
    case 5: /* a subnormal operand */
      x = signed_da(below(LO), coin());
      z = between(-20, 160);
      break;
    case 6: /* the product by a small integer */
      x = finite_rand();
      y = between(-1000, 1000);
      z = 0;
      break;
    default: { /* special values and the ends of the ranges */
      static const int64_t ys[] = {0, 1, -1, INT64_MIN, INT64_MAX};
      x = coin() ? special_rand() : da_rand();
      if (coin()) y = ys[below(5)];
      z = coin() ? between(-30000, 30000) : between(-1, 1) * 30000;
      break;
    }
    }
    ROUNDING(check3("mult_integer", x, (da){(uint64_t)y},
                    (da){(uint64_t)(int64_t)z}, da_mult_integer(x, y, z),
                    o_mult_integer(x, y, z)));
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
    case 2:
      e = coin() ? between(-2, 2) : between(-30000, 30000);
      break;
    default: e = coin() ? 30000 : -30000; break;
    }
    static const int modes[] = {
      DA_TIES_TO_EVEN, DA_TIES_TO_AWAY, DA_TOWARD_ZERO,
      DA_TOWARD_POSITIVE, DA_TOWARD_NEGATIVE, DA_AWAY_FROM_ZERO,
    };
    int mode = modes[i / 5 % 6];
    char op[20];
    snprintf(op, sizeof op, "quantize mode %d", mode);
    ROUNDING(check2(op, x, (da){(uint64_t)(int64_t)e},
                    da_quantize(x, e, mode), o_quantize(x, e, mode)));
  }
}

/* ---- main ---- */

/* da_to_string fits its bound, reports its length, is read back exactly by
   strtoda, and agrees with da_snprintf's .17G on finite values. None of
   this raises the inexact flag. */
static void test_to_string(long n) {
  for (long i = 0; i < n; i++) {
    da x = da_rand();
    char s[DA_STRING_SIZE], t[DA_STRING_SIZE];
    da_inexact = 0;
    int len = da_to_string(s, x);
    char *end;
    da back = strtoda(s, &end);
    int nan = (x.r & ~SIGN) > INF;
    uint64_t want = nan ? NAN_R | (x.r & SIGN) : x.r;
    checks++;
    int bad_len = len != (int)strlen(s) || len >= DA_STRING_SIZE;
    if (unlikely(bad_len || *end || back.r != want || da_inexact)) {
      failure("to_string", bad_len ? "wrong length"
                           : *end || back.r != want
                           ? "does not read back as the value"
                           : "inexact flag raised");
      show("x", x);
      printf("  string \"%s\", length %d\n", s, len);
      stop();
    }
    if ((x.r & ~SIGN) >= INF) continue;
    da_snprintf(t, sizeof t, ".17G", x);
    checks++;
    if (unlikely(strcmp(s, t) || da_inexact)) {
      failure("to_string", da_inexact ? "inexact flag raised"
                                      : "differs from .17G");
      show("x", x);
      printf("  string \"%s\", .17G \"%s\"\n", s, t);
      stop();
    }
  }
}

/* da_snprintf and da_asprintf against glibc's printf, which is exact on a
   double and rounds its ties to even. The values are exact both as doubles
   and as DEC α values: m * 2^e with m below 2^53 and the integer m * 2^e,
   or m * 5^-e when e is negative, at most 2^55. Zeros, infinities and NaNs
   too. The specifications are random, and so is the size of a truncated
   output, which must leave the rest of the buffer alone. The inexact flag
   is expected exactly when the output does not read back as the value. */
static void test_snprintf(long n) {
  mpq_t q, qd;
  mpq_inits(q, qd, NULL);
  for (long i = 0; i < n; i++) {
    double v;
    da x;
    if (below(16) == 0) {
      int c = (int)below(3);
      v = c == 0 ? 0 : c == 1 ? INFINITY : NAN;
      x = (da){c == 0 ? 0 : c == 1 ? INF : NAN_R};
    }
    else {
      int e = between(-23, 55);
      uint64_t p5 = 1;
      for (int j = e; j < 0; j++) p5 *= 5;
      uint64_t lim = (UINT64_C(1) << 55) / p5 >> (e > 0 ? e : 0);
      if (lim > UINT64_C(1) << 53) lim = UINT64_C(1) << 53;
      uint64_t top = lim >> below(53), m = top ? 1 + below(top) : 1;
      v = (double)m;
      for (int j = 0; j < e; j++) v *= 2;
      for (int j = e; j < 0; j++) v /= 2;
      x = e >= 0 ? da_from_integer(m << e)
        : da_from_integer_and_biased_exp(m * p5, BIAS + e);
      q_of(q, x.r);
      mpq_set_d(qd, v);
      if (unlikely(!mpq_equal(q, qd))) {
        checks++;
        failure("snprintf", "the test's double is not the value");
        printf("  double %.17g\n", v);
        show("x", x);
        stop();
      }
    }
    if (coin()) {
      v = -v;
      x.r |= SIGN;
    }
    char spec[40], *p = spec;
    for (int f = (int)below(4); f > 0; f--, p++) *p = "-+ #0"[below(5)];
    if (coin()) p += sprintf(p, "%d", (int)below(40));
    if (coin()) {
      int prec = (int)below(coin() ? 26 : 300);
      p += coin() ? sprintf(p, ".") : sprintf(p, ".%d", prec);
    }
    p[0] = "fFeEgG"[below(6)];
    p[1] = 0;
    char fmt[48], want[512], got[512], wt[512], gt[512], *s = NULL;
    snprintf(fmt, sizeof fmt, "%%%s", spec);
    int wn = snprintf(want, sizeof want, fmt, v);
    da_inexact = 0;
    int gn = da_snprintf(got, sizeof got, spec, x);
    int flag = da_inexact;
    da_inexact = 0;
    int an = da_asprintf(&s, spec, x);
    int aflag = da_inexact;
    size_t size = below((uint64_t)wn + 4);
    memset(wt, 'X', sizeof wt);
    memset(gt, 'X', sizeof gt);
    snprintf(wt, size, fmt, v);
    int tn = da_snprintf(gt, size, spec, x);
    int want_flag = inexact_printf && strtoda(want, NULL).r != x.r;
    checks++;
    if (unlikely(gn != wn || strcmp(got, want) || an != wn
                 || strcmp(s, want) || tn != wn
                 || memcmp(wt, gt, sizeof wt)
                 || flag != want_flag || aflag != want_flag)) {
      int flag_only = gn == wn && !strcmp(got, want) && an == wn
        && !strcmp(s, want) && tn == wn && !memcmp(wt, gt, sizeof wt);
      failure("snprintf", flag_only ? "wrong inexact flag"
                                    : "differs from printf");
      show("x", x);
      printf("  spec \"%s\": printf %d \"%s\"\n", spec, wn, want);
      printf("  da_snprintf %d \"%s\", da_asprintf %d \"%s\"\n", gn,
             got, an, an < 0 ? "" : s);
      printf("  size %zu: printf \"%.*s\", da_snprintf %d \"%.*s\"\n",
             size, (int)(size ? size - 1 : 0), wt, tn,
             (int)(size ? size - 1 : 0), gt);
      printf("  inexact flag %d and %d, want %d\n", flag, aflag,
             want_flag);
      stop();
    }
    free(s);
  }
  mpq_clears(q, qd, NULL);
}

static void section(const char *name, void (*f)(long), long n) {
  long c = checks, t = ties;
  f(n);
  printf("%-16s %8ld checks %6ld ties\n", name, checks - c, ties - t);
}

int main(int argc, char **argv) {
  long n = setup(argc, argv);
  /* a probe of each file: 1 / 3 and 0.5 printed with no decimals */
  da_inexact = 0;
  da_div(da_from_integer(1), da_from_integer(3));
  inexact_arith = da_inexact;
  char half[4];
  da_inexact = 0;
  da_snprintf(half, sizeof half, ".0f",
              da_from_integer_and_biased_exp(5, BIAS - 1));
  inexact_printf = da_inexact;
  printf("seed %" PRIu64 ", inexact flag %s in dec-alpha.c, %s in "
         "da_printing.c\n", seed, inexact_arith ? "on" : "off",
         inexact_printf ? "on" : "off");
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
  section("mult_integer", test_mult_integer, n);
  section("quantize", test_quantize, n);
  section("to_string", test_to_string, n);
  section("snprintf", test_snprintf, n);
  printf("random: %ld checks, all passed\n", checks);
  return 0;
}

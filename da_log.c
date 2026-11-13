/* Ten to the x and the logarithm in base ten, in fixed point.

   Base ten makes the reduction of the argument exact, in both
   directions. For 10^x, the integer part n of x is a shift of the
   decimal exponent, and what is left to compute is 10^f for the
   fraction f, between 1 and 10. For log10 x, the decimal exponent
   of x is the integer part of the result, and what is left is the
   logarithm of its significand. The results are exact where they can
   be: 10^x for an integer x, log10 of a power of ten, and nowhere
   else, 10^x being irrational for any other rational x.

   The kernels work in fixed point. A Qn integer stands for its
   quotient by 2^n: sums are exact, and each product is one
   64x64->128 multiplication, shifted down to the Q of its
   destination. The constants are rounded to their Q and the shifts
   truncate. Both polynomials have positive coefficients and an
   argument below one in Q64, so that a Horner step is an addition
   and the high word of a product.

   10^x. x is m 10^e. When it is 0.04 or more, x 10^17 is the integer
   m 10^(17+e), below 2^64 since 10^x is 0 or infinite from 143 on,
   and a division by the constant 10^17 gives the integer part and a
   remainder, of which F17 makes the fraction f in Q64. F17 is above
   10^-17, by 0.96 unit of its Q120: this excess makes up for the
   truncation of the product, half a unit of Q64 on average, when f
   is around 0.6 and 10^f next to 4, where the errors count most,
   and takes 0.0025 unit in the last place off the largest. Below
   0.04, f is m 10^-17, a Q64, divided by the power of ten that
   remains, at most 10^18: with one more, f is below 2^-64 and taken
   as 0, 10^x being then 1 within 1.3e-3 unit in the last place. For
   x below 0, -x is negated as the 128-bit integer n 2^64 + f: n is
   then the floor of x, and f is still between 0 and 1.
   With f = i/16 + d, the table has 10^(i/16 - 1), and (10^d - 1)/d
   is a polynomial of degree 7 in d, below 1/16: 10^(f-1) is
   V = P + P (10^d - 1), a fraction of the unit in Q64, of which
   10^17 or 10^16 times is the result in a decade, as a product
   whose high word is the significand and low word the fraction to
   round on. When the result is subnormal, a lower power of ten puts
   the same product in units of 10^-142. The errors on V are those
   of f, below 1.4 units of Q64 and multiplied by V ln 10; of P, half
   a unit; of the polynomial, fitted for the least error of 10^d
   relative to 10^d, 6e-19, which is that of V; of its evaluation in
   Q62, 1.1 units before the product by d, and of the truncations of
   the two products. When the significand is 10^17 V, V is below 0.4
   and they are within 5.6 units of Q64 together, 0.0303 unit in the
   last place; when it is 10^16 V, a unit of Q64 is a tenth of that. An
   integer x has an f and a d of 0, and V is then P[0], 0.1 within
   half a unit: the result is exact.

   log10 x. x is sd 10^e, the sd of a subnormal x being first scaled
   to a decade, and the result is e + 16 + log10(sd / 10^16). The
   width of sd in bits and its next two bits give its zone, a quarter
   of an octave, of which c is the middle, but for the zone of 10^16,
   where c is 10^16. With z = (sd - c) / (sd + c), below 0.0593,
     log10(sd / c) = 2 / ln 10 atanh z = z W(z^2)
   where W is a polynomial of degree 5 in z^2, and the table T has
   log10(c / 10^16), 0 for the zone of 10^16. sd + c fills one binade,
   that of the width of sd plus one, so that one 128-bit division
   gives its inverse to 63 bits at least, of which the product by
   |sd - c| is z, exact but for the error of the inverse.
   The sum e + 16 + T ± z W is taken in Q64. Its magnitude is 0.0454
   at least unless e + 16 and T are both 0: the logarithms of the
   ends of the zone of 10^16 are -0.0454 and 0.0515. It is then
   scaled by 10^14 to 10^17, the power of ten that puts it in a
   decade, chosen by comparisons, and rounded. The errors are those
   of T, a unit of Q64, and of z W, where z is below 0.06: with the
   truncations, and T as it is, 1.85 units of Q64 at most, or 0.01002
   unit in the last place when the scaling is by 10^17, and less
   otherwise.
   When e + 16 and T are both 0, x is in the zone around 1, the
   result is ± z W alone, and may be as small as 4.3e-17: |sd - c|
   is then scaled to a decade, exactly, before the product, so that
   the result is the product of a significand by the inverse and W,
   between 0.16 and 1.84, with the decimal exponent of |sd - c|. The
   errors are 2^-63 for the inverse, 7e-20 for W and 1.5 unit of
   Q64 on its 0.87, in relative terms, 2.7e-19 together or 0.011
   unit in the last place at worst, and as much for the truncations
   of the product. The truncations all make the result smaller, by
   0.0137 unit in the last place at most: the constant term of W is
   2 units of Q64 above its fit, 0.005 unit in the last place of a
   result at the top of a decade, which leaves the result within
   0.0091 of the exact one before its rounding.

   10^x is so within 0.531 unit in the last place of the exact value,
   and log10 x within 0.511. */
#include "da_internal.h"

/* Generated by gen_log.c: do not edit. */
#define F17 UINT64_C(13292279957849158730) // 10^-17 + 0.96 unit, Q120
// the least x such that 10^x rounds to infinity, and the
// least such that 10^-x rounds to zero
#define OVER UINT64_C(4624546259152595869)
#define UNDER UINT64_C(4625916121426954303)

// 10^(i/16 - 1), Q64
static const uint64_t P[16] = {
  UINT64_C(1844674407370955162),
  UINT64_C(2130196773249681684),
  UINT64_C(2459912857592347133),
  UINT64_C(2840663051853607126),
  UINT64_C(3280346516853521691),
  UINT64_C(3788085061201260954),
  UINT64_C(4374412385146479779),
  UINT64_C(5051492615969598450),
  UINT64_C(5833372668713515885),
  UINT64_C(6736273667810235103),
  UINT64_C(7778927475525239208),
  UINT64_C(8982965308942392352),
  UINT64_C(10373366507857047692),
  UINT64_C(11978976763854315511),
  UINT64_C(13833106561912589467),
  UINT64_C(15974222249986187368),
};

// (10^d - 1) / d for d up to 1/16, Q62
static const uint64_t EXPM1[8] = {
  UINT64_C(97055885781815522),
  UINT64_C(313225474589554969),
  UINT64_C(954648671879934482),
  UINT64_C(2487462950108582480),
  UINT64_C(5401461031276336551),
  UINT64_C(9383298815643982009),
  UINT64_C(12225344693612310234),
  UINT64_C(10618799479599962669),
};

// 2 / ln 10 atanh(z) / z in z^2, z up to 0.0592, Q64, the
// constant term 2 units above
static const uint64_t ATANH[6] = {
  UINT64_C(1469653432702205279),
  UINT64_C(1780241519058526166),
  UINT64_C(2288948425599829875),
  UINT64_C(3204527664039882903),
  UINT64_C(5340879440195737274),
  UINT64_C(16022638320587141526),
};

#define ZONE_E16 5 // the zone of 10^16
// log10 of the centers of the zones, Q63
static const int64_t T[14] = {
  INT64_C(-3453866433552345262),
  INT64_C(-2723548342913364688),
  INT64_C(-1919729849180680837),
  INT64_C(-1250568054547017009),
  INT64_C(-677354789290666696),
  INT64_C(0),
  INT64_C(856781795080997729),
  INT64_C(1525943589714661557),
  INT64_C(2099156854971011870),
  INT64_C(2829474945609992444),
  INT64_C(3633293439342676295),
  INT64_C(4302455233976340123),
  INT64_C(4875668499232690437),
  INT64_C(5605986589871671010),
};

/* r[0] u^(n-1) + ... + r[n-2] u + r[n-1] with the Q of r, for u in
   Q64 */
static uint64_t horner(const uint64_t *r, int n, uint64_t u) {
  uint64_t p = r[0];
  for (int k = 1; k < n; k++) p = r[k] + ((ulll)u * p >> 64);
  return p;
}

/* 10^x. Past the thresholds, the result is the infinity of an
   overflow or the zero of an underflow, inexact unless x is itself
   infinite, or x when it is NaN. Below them, x is n + f and the
   result V 10^(n+1) = V 10^k 10^(exp-142), k being 17 or 16 so that
   V 10^k is in a decade, or less when exp would be negative, which
   leaves a k of 0 for the least n, -143, where V is above 0.4999. */
da da_exp10(da dx) {
  uint64_t x = dx.r, pos = x & ~SIGN_MASK;
  if (pos >= (x == pos ? OVER : UNDER)) {
    INEXACT(pos < DA_INFINITY.r);
    return pos > DA_INFINITY.r ? dx : x == pos ? DA_INFINITY : DA_ZERO;
  }
  uint64_t m, ip = 0;
  int t = -17 - split(pos, &m); // x is m 10^-17 10^-t
  if (t <= 0) {                 // 0.04 or more: t is -3 at least
    m *= da_powers[-t];
    ip = m / E17;
    m -= ip * E17;
  }
  INEXACT(m != 0);
  uint64_t f = (ulll)m * F17 >> 56;
  if (t > 0) f = t < 19 ? f / da_powers[t] : 0;
  ulll fixed = (ulll)ip << 64 | f;
  if (x != pos) fixed = -fixed;
  int n = (int)(int64_t)(uint64_t)(fixed >> 64);
  f = (uint64_t)fixed;
  uint64_t d = f << 4 >> 4, p = P[f >> 60];
  uint64_t q = (ulll)d * horner(EXPM1, 8, d) >> 60; // 10^d - 1, Q66
  ulll v = p + ((ulll)p * q >> 66); // up to 2^64, within the errors
  int k = 16 + (v < VLO), exp = n + 143 - k;
  if (exp < 0) {
    k += exp;
    exp = 0;
  }
  return nearest(v * da_powers[k], exp);
}

// the least Q56 at or above DECADE_LO / p
#define DECADE(p) ((uint64_t)((((ulll)DECADE_LO << 56) + (p) - 1) / (p)))

/* The high 128 bits of the 192 of a b. */
static ulll high(ulll a, uint64_t b) {
  return (a >> 64) * b + ((ulll)(uint64_t)a * b >> 64);
}

/* -a when minus is 1, a when it is 0, without a branch. */
static ulll negate(ulll a, uint64_t minus) {
  return (a ^ -(ulll)minus) + minus;
}

/* log10 x: -inf for a zero, NaN for a negative x, x for +inf and NaN.
   Otherwise the result is ± M 2^-64 10^(exp-142), rounded as M 10^k
   with the exponent exp - k. M is the magnitude of the sum in Q64
   and exp is 142; or, when the sum is z W alone, M is the z W of
   |sd - c| scaled to a decade, and exp makes up for the scaling.
   A |sd - c| of 0 stays 0, with an exp of 17, and the k of an M of
   0 is 17: the log10 of 1 is +0. */
da da_log10(da dx) {
  uint64_t x = dx.r, pos = x & ~SIGN_MASK;
  if (x - 1 >= DA_INFINITY.r - 1)
    return !pos ? DA_MINUS_INFINITY
         : x == pos | pos > DA_INFINITY.r ? dx : DA_NAN;
  uint64_t sd;
  int e = split(x, &sd);
  for (; sd < DECADE_LO; e--) sd *= 10; // a subnormal x
  INEXACT(sd != E16);
  int w = bit_width(sd);        // 52 to 56
  uint64_t top = sd >> (w - 3); // 4 to 7
  int i = 4 * w + (int)top - 215, exp = 142;
  uint64_t c = i == ZONE_E16 ? E16 : (2 * top + 1) << (w - 4);
  uint64_t below = sd < c, a = below ? c - sd : sd - c;
  // 2^(64+w) / (sd + c), sd + c being between 2^w and 2^(w+1), and
  // |sd - c| 2^(62-w), below 2^59, or 2^64 once scaled to a decade
  uint64_t inv = ((ulll)(UINT64_C(1) << w) << 64) / (sd + c);
  uint64_t z = (ulll)(a << (62 - w)) * inv >> 58; // Q68
  uint64_t W = horner(ATANH, 6, (ulll)z * z >> 72);
  ulll base = ((ulll)(e + 16) << 64) + 2 * (ulll)T[i];
  if (!base) exp = split(da_from_integer_and_biased_exp(a, 125).r, &a)
                 + 159;
  ulll rho = high((ulll)(a << (62 - w)) * inv, W) >> 62; // z W, Q64
  ulll r = base + negate(rho, below);
  uint64_t minus = r >> 127;
  ulll M = negate(r, minus);
  uint64_t h = M >> 8; // Q56
  int k = 14 + (h < DECADE(E14)) + (h < DECADE(E15))
        + (h < DECADE(E16));
  return (da){nearest(M * da_powers[k], exp - k).r | minus << 63};
}

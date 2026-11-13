/* Sine, cosine and tangent of angles in degrees, in fixed point.

   Degrees make the reduction of the argument exact. The remainder of
   x by 360 is one 64-bit remainder of the significand, scaled so that
   360 is an integer: for decimal exponents of 3 and more, 10^e is 280
   modulo 360, so that every value of magnitude 4e18 or more is a
   multiple of 40 degrees and its remainder is 40 (7 sd mod 9). The
   folds 360 - x, 180 - x and 90 - x are then subtractions of integers
   in femtodegrees, units of 1e-15 degrees, exact because the result is
   below x. The kernels take 0 to 45 degrees.

   The kernels work in fixed point. A Qn integer stands for its
   quotient by 2^n, the n of each quantity being, mostly, the one that
   fills 64 bits with its largest value: sums are exact, and each
   product is one 64x64->128 multiplication, shifted down to the Q of
   its destination. The constants are rounded to their Q and the shifts
   truncate, by less than a unit of the destination.

   From 4.0032 degrees, the start of a decade, to 45, the table has
   sin t and cos t for t at every 2^52 femtodegrees, 4.5036 degrees,
   less an offset: the high bits of r plus the offset are the index
   of t, a shift, and the low bits are d = r - t, below 4.5036
   degrees, in the range of the polynomials below. Then
     sin r = S + C sin d - S (1 - cos d),
     cos r = C - S sin d - C (1 - cos d),
   one function of (a, b) = (S, C) or (C, S) and of the sign of its
   middle term. sin d is taken in Q67 and 1 - cos d in Q72, the sum in
   Q128, exact, then truncated to Q64, a fraction V of the unit: the
   result is V 10^17 or V 10^16, whichever has its integer part in a
   decade, a product whose high word is the significand and low word
   the fraction to round on. The truncations to Q67 and Q72, the 0.1
   unit of the polynomial of 1 - cos d and the truncation of the sum
   leave V between 1.2 units of Q64 below and 0.3 above what the
   table makes it. A unit of Q64 is 0.0054 unit in the last place of
   the sine in its lowest decade, from sin 4 to 0.4, and a tenth of
   that elsewhere: so S is the sine plus 0.44 unit, the middle of
   these, and the offset, 0.5004 degrees, is the one that puts the
   five sines below 0.4, so raised, within 0.05 unit of a Q64, of
   the 100000 least that keep 4.0032 degrees in the first slice. V
   is there within 0.73 unit of the exact value, 0.0040 unit in the
   last place; elsewhere, with S and C half a unit from what they
   stand for, within 1.7 units.

   Below 4.0032 degrees, sin r = r K (1 - g(θ²)) with θ = r K, K being
   π/180, and g(θ²) = 1 - sin θ/θ, below 8.2e-4: the product is taken
   on the significand of r, exact, and carries the decimal exponent of
   r, which keeps the relative precision and covers the subnormal
   arguments and results, including sin(1e-142) = 0. The only errors
   are those of K (1 - g), a Q69 fraction, in which the one of g is
   negligible, so the result is within 2^-69/K, 1e-19, of the exact
   one in relative terms, 0.004 unit in the last place at worst.
   cos r = 1 - (1 - cos θ), a Q72 fraction subtracted from one in
   Q128, with no error to speak of. θ comes from the significand and
   a table of π/180 times powers of ten, in Q118, down to 4e-9
   degrees, below which θ² is under 5e-21 and the terms in it under
   1e-4 unit of the results, so θ is taken as 0 there.

   1 - sin θ/θ and 1 - cos θ are polynomials of degree 4 in θ², θ²
   times one of degree 3 fitted by Remez's exchange for θ up to
   0.0786, 4.5036 degrees: their errors are below 5.0e-22 and
   5.5e-21, 0.009 and 0.10 unit of Q64. θ² is a Q70 and each Horner
   step shifts by 76, so the coefficients go down by six in Q from
   the one of the highest degree. The sine and cosine are so within
   0.504 unit in the last place of the exact values, and never, by
   Niven's theorem, exact for a nonzero r other than sin 30.

   The tangent is the quotient of the sine and the cosine in fixed
   point, before their rounding, or of the cosine and the sine after
   the fold at 45 degrees: one 128-bit division, with neither a table
   nor a polynomial of its own. The relative errors of the two add up:
   in the table, 0.7 unit of Q64 on a sine of 0.0698 at least and
   1.7 on the cosine cost, with the truncation of the quotient,
   0.0102 unit in the last place at worst, and below 4.0032 degrees
   the errors of K tan θ/θ and the 60 bits kept of the divisor of
   the inverse cost 0.0185. The tangent is so within 0.519 unit in
   the last place of the exact value; tan 45 is 1, the sum of the
   errors there being 0.003 unit.

   da_sincos gives the sine and the cosine of one angle, each as
   da_sin and da_cos round it: the reduction, θ and the polynomials
   serve both, the second one costing the turn that the tangent
   divides by, or the other formula below 4.0032 degrees, and its own
   rounding. */
#include "da_internal.h"

#define E15Q14 (E15 << 14) // 10^15 in Q14
#define DEG(n) (UINT64_C(n) * E15) // n degrees in femtodegrees

/* Generated by gen_sincos.c: do not edit. */
#define K69 UINT64_C(10302605451487463598) // pi/180, Q69

// pi/180 10^-15-j, Q118: the radians of 10^-15-j degrees
static const uint64_t T[10] = {
  UINT64_C(5799851259033022721),
  UINT64_C(579985125903302272),
  UINT64_C(57998512590330227),
  UINT64_C(5799851259033023),
  UINT64_C(579985125903302),
  UINT64_C(57998512590330),
  UINT64_C(5799851259033),
  UINT64_C(579985125903),
  UINT64_C(57998512590),
  UINT64_C(5799851259),
};

// (1 - sin θ/θ) / θ² and (1 - cos θ) / θ² as polynomials in
// θ² up to (4.5036 degrees)², by Remez's exchange: the
// magnitudes of their coefficients, of alternating signs,
// highest degree first, in Q82, 76, 70, 64 and Q79, 73, 67, 61
static const uint64_t G[4] = {
  UINT64_C(13324077758823916114),
  UINT64_C(14991639480207337971),
  UINT64_C(9838263505973698265),
  UINT64_C(3074457345618258556),
};

static const uint64_t V[4] = {
  UINT64_C(14989131475181373736),
  UINT64_C(13117684471209535854),
  UINT64_C(6148914691230014587),
  UINT64_C(1152921504606846911),
};

// the table has t = i 2^SHIFT - OFFSET femtodegrees, for i from 1 to 10
#define SHIFT 52
#define OFFSET UINT64_C(500399958639162)

// sin t + 0.44 2^-64 and cos t, Q64: the offset is the one
// whose sines below 0.4 are the closest to their Q64
static const uint64_t table[10][2] = {
  {UINT64_C(1287807461123257437), UINT64_C(18401736843679015432)},
  {UINT64_C(2728767391502399541), UINT64_C(18243798821627354637)},
  {UINT64_C(4152876651378210427), UINT64_C(17973201785975034369)},
  {UINT64_C(5551341088499516407), UINT64_C(17591616726158953802)},
  {UINT64_C(6915524912394054736), UINT64_C(17101400004297766996)},
  {UINT64_C(8237004022057831475), UINT64_C(16505578804196524474)},
  {UINT64_C(9507618026420752652), UINT64_C(15807832437896652243)},
  {UINT64_C(10719520636352014202), UINT64_C(15012469625206965659)},
  {UINT64_C(11865228117024795555), UINT64_C(14124401886519042544)},
  {UINT64_C(12937665501437461099), UINT64_C(13149113213211506596)},
};

/* θ, the angle m 10^e degrees in radians, Q67, which holds it up to
   7 degrees; 0 below 4e-9 degrees. */
static uint64_t theta(uint64_t m, int e) {
  int j = -15 - e;
  return j < 10 ? (ulll)m * T[j] >> 51 : 0;
}

/* r[3] - u (r[2] - u (r[1] - u r[0])) with the Q of r[3] for u = θ²
   in Q70, each step shifting by 76 */
static uint64_t horner(const uint64_t r[4], uint64_t u) {
  uint64_t p = r[0];
  for (int k = 1; k < 4; k++) p = r[k] - ((ulll)u * p >> 76);
  return p;
}

/* 1 - sin θ/θ in Q73, and 1 - cos θ in Q72, for u = θ² in Q70 */
static uint64_t g(uint64_t u) { return (ulll)u * horner(G, u) >> 61; }
static uint64_t versine(uint64_t u) {
  return (ulll)u * horner(V, u) >> 59;
}

/* a cos d + b sin d in Q64, or a cos d - b sin d when minus is set,
   for s = sin d in Q67 and v = 1 - cos d in Q72: with (a, b) the
   sine and cosine of t, or its cosine and sine with the minus, the
   sine or the cosine of t + d. */
static uint64_t turn(uint64_t a, uint64_t b, uint64_t s, uint64_t v,
                     int minus) {
  ulll w = ((ulll)a << 64) - ((ulll)a * v >> 8), bs = (ulll)b * s >> 3;
  return (minus ? w - bs : w + bs) >> 64;
}

/* The operations, and the bits of the result of the reduction: bit
   0 is set when the sine and the cosine are swapped, which turns SIN
   into COS and TAN into COT, the inverse of the tangent, and bit 2
   when the sine changes sign, bit 1 when the cosine does, unless it
   is zero. PAIR is the sine then the cosine: its bit 0 is SIN's. */
enum { SIN, COS, TAN, COT, PAIR };

/* Reduces the angle of representation pos, finite and positive, to
   m 10^e degrees, at most 45: either the angle itself, when it is
   below 40.032, or with e at -15 for m in femtodegrees from 4.0032
   degrees, or m and e split from less than that. Returns the
   bits above. */
static int reduce(uint64_t pos, uint64_t *pm, int *pe) {
  uint64_t m;
  int e = split(pos, &m), folds = 0;
  if (e >= -14) { // 40.032 or more: reduce to femtodegrees, up to 45e15
    if (e >= 3) { // 10^e is 280 modulo 360: x is a multiple of 40
      m = 40 * (7 * m % 9);
      e = 0;
    }
    for (; e > 0; e--) m *= 10;
    m = m % (360 * da_powers[-e]) * da_powers[e + 15];
    if (m >= DEG(180)) { // sin(x - 180) = -sin x, and likewise cos
      m -= DEG(180);
      folds = 6;
    }
    if (m >= DEG(90)) { // sin(180 - x) = sin x, cos(180 - x) = -cos x
      m = DEG(180) - m;
      folds ^= 2;
    }
    if (m >= DEG(45)) { // sin(90 - x) = cos x, cos(90 - x) = sin x
      m = DEG(90) - m;
      folds |= 1;
    }
    e = -15;
    // below 4.0032 degrees, back to a significand and its exponent
    if (m < DECADE_LO)
      e = split(da_from_integer_and_biased_exp(m, 127).r, &m);
  }
  *pm = m;
  *pe = e;
  return folds;
}

/* n 2^-64 10^(exp-142) scaled to a decade, rounded, with its sign.
   The loop runs at most twice: the sine is 0.0698 at least in the
   table, m K is 7e13 at least for a normal m, and a tangent is
   0.0699 at least. */
static inline da finish(ulll n, int exp, uint64_t sign) {
  for (; n >> 64 < DECADE_LO & exp > 0; exp--) n *= 10;
  return (da){nearest(n, exp).r | sign};
}

/* The op of dx, SIN, COS, TAN or PAIR, as the first member of the
   result, PAIR having the cosine as the second. Every case ends with
   n and exp such that the result is n 2^-64 10^(exp-142) before
   rounding, and with n2 and exp2 for the second of PAIR.

   In the table, the sine and the cosine are a fraction V of the
   unit in Q64, and the result is V 10^17 or V 10^16. For the
   tangent, they are the two Q64 values a and b, and a 10^15 2^14 / b
   is their quotient times 10^15, in Q14: the scaling by at most 100
   leaves it within 0.007 unit of the quotient. Below 4.0032 degrees,
   K sin θ/θ is divided by cos θ, a Q63 here so that it fits when it
   is 1, and the product by m is the sine's. The inverse of that,
   2^69 10^-e / (m k), is only asked of a normal m with e from -31 to
   -16, or of 0: with b = m k 2^-55, of 60 bits at least, it is
   10^-e-30 times 10^30 2^28 / b, again a Q14.

   Below 4.0032 degrees the sine and the cosine are both computed
   whatever the op, the one that is not asked for with its polynomial
   at 0: a branch around its multiplications costs as much as they
   do. */
static da_pair trig(da dx, int op) {
  uint64_t x = dx.r, pos = x & ~SIGN_MASK;
  if (pos >= DA_INFINITY.r) {
    da r = pos == DA_INFINITY.r ? DA_NAN : dx;
    return (da_pair){r, r};
  }
  uint64_t m;
  int e, folds = reduce(pos, &m, &e), tangent = op == TAN;
  int co = (op ^ folds) & 1, nz = m != 0;
  // The sine is odd and the cosine even, which also gives the sign
  // of a zero result: that of x for the sine, + for the cosine, as
  // IEEE 754's sinPi and cosPi. The tangent has the sign of their
  // quotient, as tanPi: both flips when it is finite and nonzero,
  // and when m is 0, the flip of the one that is not zero, which is
  // the flip of the sine either way, the cosine's being the same at
  // 180 degrees.
  int flip = tangent ? folds >> 2 ^ (nz & folds >> 1)
                     : (nz | co) & folds >> (2 - (op & 1));
  uint64_t sign = (uint64_t)(op != COS & x != pos ^ flip & 1) << 63;
  // By Niven's theorem, the sine of a rational number of degrees is
  // irrational but for 0, 1/2 and 1, and its tangent but for 0 and
  // 1: the result is inexact unless r is 0, or 30 for the sine alone,
  // or 45 for the tangent.
  INEXACT(nz & (e != -15 | (tangent ? m != DEG(45)
                                    : op == PAIR | co | m != DEG(30))));
  // In the table, r = t + d, t being i 2^SHIFT - OFFSET for the
  // index i, the high bits of r + OFFSET, and d its low bits.
  uint64_t i = 0, d = m;
  if (e == -15) {
    d += OFFSET;
    i = d >> SHIFT;
    d &= (UINT64_C(1) << SHIFT) - 1;
  }
  uint64_t th = theta(d, e), u = (ulll)th * th >> 64;
  // the table, the tangent and the pair take both polynomials
  int both = e == -15 | op >= TAN;
  uint64_t gu = both | !co ? g(u) : 0, v = both | co ? versine(u) : 0;
  ulll n, n2 = 0;
  int exp = 126, exp2 = 126;
  if (e == -15) {
    const uint64_t *sc = table[i - 1];
    uint64_t s = th - ((ulll)th * gu >> 73); // sin d, Q67
    uint64_t a = turn(sc[co], sc[!co], s, v, co);
    int low = a < VLO;
    n = (ulll)a * (low ? E17 : E16);
    exp = 126 - low;
    if (op >= TAN) { // the other of the sine and the cosine
      uint64_t b = turn(sc[!co], sc[co], s, v, !co);
      if (tangent) {
        n = (ulll)a * E15Q14 / b << 50;
        exp = 127;
      } else {
        low = b < VLO;
        n2 = (ulll)b * (low ? E17 : E16);
        exp2 = 126 - low;
      }
    }
  } else {
    ulll c = ((ulll)E16 << 64) - ((ulll)v * E16 >> 8); // cos θ
    uint64_t k = K69 - ((ulll)K69 * gu >> 73); // K sin θ/θ, Q69
    if (tangent) k = ((ulll)k << 63) / (HALF - (v >> 9));
    n = (ulll)m * k >> 5;
    exp = e + 142;
    n2 = c;
    if (co > tangent) { // the cosine first, not the inverted tangent
      n2 = n;
      exp2 = exp;
      n = c;
      exp = 126;
    }
    if (tangent & co) {
      uint64_t b = n >> 50;
      n = (ulll)DECADE_LO << 64; // the infinity of 90 degrees
      exp = 255;
      if (m) {
        n = (ulll)E15Q14 * E15Q14 / b << 50;
        exp = 112 - e;
      }
    }
  }
  da_pair r = {finish(n, exp, sign), DA_ZERO};
  if (op == PAIR) // the cosine: the other fold bit, and co inverted
    r.cos = finish(n2, exp2,
                   (uint64_t)((nz | !co) & folds >> 1 & 1) << 63);
  return r;
}

da da_sin(da x) {
  return trig(x, SIN).sin;
}

da da_cos(da x) {
  return trig(x, COS).sin;
}

da da_tan(da x) {
  return trig(x, TAN).sin;
}

da_pair da_sincos(da x) {
  return trig(x, PAIR);
}

/* x radians in degrees: x times the constant 180/π, to 19 digits. The
   constant is 5.6e-20 above 180/π in relative terms, 0.0023 ULP of a
   result at the top of a decade and less elsewhere.

   The constant is also 8 times an integer above DECADE_HI with no
   factor 2 or 5, so the product by any nonzero finite da raises the
   inexact flag, which happens to match how exactly the da returned by
   the function is x*180/π. */
da da_degrees_of_radians(da x) {
  return da_mult_integer(x, 5729577951308232088, -17);
}

#include <math.h>
#include <string.h>
#include "da_internal.h"

/* The inexact flag, which the INEXACT of da_internal.h raises: */
_Thread_local int da_inexact;

/* 10^n for n up to 19, the largest that fits in 64 bits: */
const uint64_t da_powers[20]= {
  1,
  10,
  1e2,
  1e3,
  1e4,
  1e5,
  1e6,
  1e7,
  1e8,
  1e9,
  1e10,
  1e11,
  1e12,
  1e13,
  1e14,
  1e15,
  1e16,
  1e17,
  1e18,
  1e19,
};

/* The decade of m: the j such that m * 10^-j is in a decade. Each bit
   width holds one start of a decade at most, 2 being less than 10, so
   the decade of the smallest m of that width, 2^(w-1), is the answer or
   one below it. That decade is floor((w-1) log10(2) - log10(DECADE_LO)),
   that is floor((1233 w - 65140.4) / 4096) within 2^-12, and 65141
   gives it exactly for every width up to 119. m reaches the start of
   the decade above, DECADE_LO * 10^(j+1), when m * 10^-(j+1) >=
   DECADE_LO for j below 0, and when m >= 10 * DECADE_LO * 10^j above,
   10^20 not fitting in 64 bits.
   Its steps depend on one another, costing more than a loop that
   scales by 10 once or twice: the operations whose operands span a few
   decades keep their loops. */
/*@ requires 0 < m < DECADE_LO * 10^20; ensures -16 <= \result <= 19; */
static inline int decade(ulll m) {
  uint64_t hi = m >> 64;
  int w = hi ? 64 + bit_width(hi) : bit_width((uint64_t)m);
  /* the shift below is one of the little portability trade-offs:
     `>>` on a negative first operand is implementation-defined.
     I don't know of any compiler that doesn't generate an arithmetic
     shift. Much less for the 64-bit platforms that this library is for. */
  int j = (1233 * w - 65141) >> 12;
  int up = j >= 0 ? m >= (ulll)(10 * DECADE_LO) * da_powers[j]
                  : (uint64_t)m * da_powers[~j] >= DECADE_LO;
  return j + up;
}

static char *copy(char *restrict p, const char *restrict s, int n) {
  memcpy(p, s, (size_t)n);
  return p + n;
}

static char *fill(char *p, char c, int n) {
  memset(p, c, (size_t)n);
  return p + n;
}

/* Writes the exact value of d to buf in the style of C's %g with 17
   significant digits: without trailing zeros, in positional notation when
   the leading digit has a decimal exponent between -4 and 16, and as
   d.dddE+dd otherwise. The longest output, a sign, 17 digits, a point and
   a three-digit exponent with its sign, has DA_STRING_SIZE - 1 characters.
   Returns the length. */
int da_to_string(char buf[DA_STRING_SIZE], da d) {
  char *p = buf;
  uint64_t a = d.r & ~SIGN_MASK;
  if (a != d.r) {
    *p = '-';
    p++;
  }
  int64_t o = (int64_t)a - (int64_t)DECADE_LO;
  uint64_t sd;
  int k; // the value is sd * 10^k
  if (o < 0) { // subnormal or zero
    sd = a;
    k = EXP_MIN;
  }
  else {
    int e = o >> EXP_SHIFT;
    sd = DECADE_LO + (o & SD_MASK);
    if (e == EXP_INFNAN) {
      p = copy(p, sd == DECADE_LO ? "inf" : "NaN", 3);
      *p = 0;
      return (int)(p - buf);
    }
    k = EXP_MIN + e;
  }
  if (sd == 0) {
    p[0] = '0';
    p[1] = 0;
    return (int)(p + 1 - buf);
  }
  while (sd % 10 == 0) {
    sd /= 10;
    k++;
  }
  char digits[17], *q = digits + 17;
  for (uint64_t m = sd; m; m /= 10) {
    q--;
    *q = '0' + m % 10;
  }
  int len = (int)(digits + 17 - q);
  int x = len - 1 + k; // the decimal exponent of the leading digit
  if (k >= 0 && x < 17) { // an integer
    p = copy(p, q, len);
    p = fill(p, '0', k);
  }
  else if (k < 0 && x >= 0) { // a fraction with an integer part
    p = copy(p, q, x + 1);
    *p = '.';
    p = copy(p + 1, q + x + 1, len - x - 1);
  }
  else if (k < 0 && x >= -4) { // a fraction below 1
    p = copy(p, "0.", 2);
    p = fill(p, '0', -x - 1);
    p = copy(p, q, len);
  }
  else {
    *p = *q;
    p++;
    if (len > 1) {
      *p = '.';
      p = copy(p + 1, q + 1, len - 1);
    }
    p[0] = 'E';
    p[1] = x < 0 ? '-' : '+';
    p += 2;
    int ax = x < 0 ? -x : x;
    if (ax >= 100) {
      *p = '0' + ax / 100;
      p++;
    }
    p[0] = '0' + ax / 10 % 10;
    p[1] = '0' + ax % 10;
    p += 2;
  }
  *p = 0;
  return (int)(p - buf);
}

typedef struct { uint64_t sd; int exp; } da_parts;

/* Split a positive finite da into significand and biased exponent, so that
   its value is sd * 10^(exp-142). Subnormals and zero have exp 0, like
   the first normal decade, whose scale they share. */
/*@ requires 0 <= r < DA_INFINITY.r; */
static da_parts da_split(uint64_t r) {
  int64_t o = (int64_t)r - (int64_t)DECADE_LO;
  if (o < 0) return (da_parts){r, 0}; // subnormal or zero
  return (da_parts){DECADE_LO + (o & SD_MASK), o >> EXP_SHIFT};
}

/* The da sd * 10^(exp-142), or infinity when exp is too large. */
/*@
  requires 0 <= exp;
  requires DECADE_LO <= sd <= DECADE_HI || exp == 0 && sd < DECADE_LO;
*/
static da da_wrap(uint64_t sd, int exp) {
  if (exp >= EXP_INFNAN) {
    INEXACT(1); // overflow
    return DA_INFINITY;
  }
  return WRAP(sd, exp);
}

/* Round (m / p) * 10^(exp-142) to the nearest da, ties to even. */
/*@
  requires 0 <= exp;
  requires DECADE_LO <= m / p < 10 * DECADE_LO
        || exp == 0 && m / p < DECADE_LO;
*/
static da da_round(ulll m, ulll p, int exp) {
  uint64_t sd = m / p;
  ulll rem = m - (ulll)sd * p;
  INEXACT(rem != 0);
  if (sd >= DECADE_HI) {
    // the only candidates are DECADE_HI and the DECADE_LO of the next
    // decade, 8 units apart. On the exact midpoint, DECADE_HI is the even
    // one.
    INEXACT(sd != DECADE_HI);
    if (m > (ulll)(DECADE_HI + 4) * p) {
      exp++;
      sd = DECADE_LO;
    }
    else
      sd = DECADE_HI;
  }
  else
    sd += 2 * rem + (sd & 1) > p; // ties to even, without a branch
  return da_wrap(sd, exp);
}

/* Same as da_round, but m / p may be below DECADE_LO, m being then
   multiplied by 10 until it is not, and exp may be negative, denoting a
   subnormal or zero result. */
/*@
  requires 0 < m; requires m / p < 10 * DECADE_LO;
  requires exp < 0 ==> p * 10^-exp < 2^128;
*/
static da da_round_any_exp(ulll m, ulll p, int exp) {
  for (ulll t = (ulll)DECADE_LO * p; m < t; m *= 10) exp--;
  if (exp < 0) {
    if (exp < -16) {
      INEXACT(1); // underflow to zero
      return DA_ZERO;
    }
    p *= da_powers[-exp];
    exp = 0;
  }
  return da_round(m, p, exp);
}

/* Round m * 10^(exp-142) to the nearest da for any m and any exp, the
   result being infinite or zero when out of range. fma passes exp down
   to -34, and strtoda, clamping its decimal exponent, down to -159: m
   has at most 20 digits, so any exp below -35 underflows to zero.
   da_mult_integer passes the exponent it is given, from -30000 to
   30254: the decade of its m is 19 at most and -16 at least, so any exp
   below -35 underflows as well, and any above 270 overflows. */
/*@ requires 0 < m < DECADE_LO * 10^20; */
static da da_round_wide(ulll m, int exp) {
  // the power of ten that brings m into a decade, or exp up to 0 for a
  // subnormal result
  int j = decade(m);
  if (j < -exp) {
    // m / 10^-exp is below 0.41, rounding to zero
    if (j < -exp - 16) {
      INEXACT(1); // underflow to zero
      return DA_ZERO;
    }
    j = -exp;
  }
  // with no digit to drop, the result is exact, unless m is in the holes
  // at the top of a decade. m * 10^-j, a multiple of 10 for a negative j,
  // or below DECADE_LO when j was raised, never is: j is then 0.
  if (j <= 0) {
    uint64_t sd = (uint64_t)m * da_powers[-j];
    if (sd <= DECADE_HI) return da_wrap(sd, exp + j);
  }
  // 10^j, beyond 64 bits only for a subnormal result
  ulll p = j < 20 ? da_powers[j] : (ulll)da_powers[j - 17] * da_powers[17];
  return da_round(m, p, exp + j);
}

/* Round m * 10^(exp-142) to the nearest da, m being in decade j or the
   one above. */
/*@
  requires 0 <= j <= 17; requires 0 <= exp;
  requires DECADE_LO * 10^j <= m < DECADE_LO * 10^(j+2);
*/
static da da_round_narrow(ulll m, int j, int exp) {
  j += m >= (ulll)DECADE_LO * da_powers[j + 1];
  return da_round(m, da_powers[j], exp + j);
}

/*@ requires 0 <= exp < EXP_INFNAN; */
da da_from_integer_and_biased_exp(uint64_t i, int exp) {
  if (i == 0) return DA_ZERO;
  if (i < DECADE_LO) {
    // The largest power of ten that keeps every integer of the bit
    // width w of i at most DECADE_HI, the holes above it holding no
    // multiple of ten, is floor(log10(10 * DECADE_LO) - w log10(2)),
    // that is floor((68003 - 1233 w) / 4096) within 2^-12, and 68003
    // gives it exactly for every width up to 52. It leaves i at most one
    // factor of ten short of the decade, implemented to suggest
    // branchless code to the compiler.
    // Both scalings stop at exp 0, where the result is subnormal.
    int k = (68003 - 1233 * bit_width(i)) >> 12;
    if (k > exp) k = exp;
    uint64_t m = i * da_powers[k];
    int more = m < DECADE_LO & k < exp;
    exp -= k + more;
    i = m * (1 + 9 * more);
  }
  // This expression is the correct one for the normalized case.
  // It works by miracle for the denormalized case (despite
  // i - DECADE_LO underflowing to 0xffff… in this case) because exp is
  // also 0 in this case.
  if (i <= DECADE_HI) return WRAP(i, exp);
  // i has up to 20 digits, that is up to 3 more than fit in a decade
  int j = (i >= DECADE_LO * 10) + (i >= DECADE_LO * 100)
        + (i >= DECADE_LO * 1000);
  return da_round(i, da_powers[j], exp + j);
}

da da_from_integer(uint64_t i) {
  return da_from_integer_and_biased_exp(i, 142);
}

/* Does s start with word, ignoring case? word is lowercase. */
static int prefix(const char *s, const char *word) {
  char c;
  for (; c = *word; s++, word++)
    if ((*s | 0x20) != c) return 0;
  return 1;
}

da strtoda(const char *nptr, char **endptr) {
  const char *s = nptr;
  char c;
  for (c = *s; c == ' ' || c >= '\t' && c <= '\r'; c = *s) s++;
  uint64_t sign = 0;
  if (c == '+' || c == '-') {
    sign = c == '-' ? SIGN_MASK : 0;
    s++;
  }
  if (prefix(s, "inf")) {
    s += 3;
    if (prefix(s, "inity")) s += 5;
    if (endptr) *endptr = (char *)s;
    return (da){DA_INFINITY.r | sign};
  }
  if (prefix(s, "nan")) {
    s += 3;
    if (*s == '(') { // nan(n-char-sequence)
      const char *t = s + 1;
      for (c = *t;; t++, c = *t) {
        if (c >= '0' && c <= '9' || c == '_') continue;
        char lower = c | 0x20;
        if (lower < 'a' || lower > 'z') break;
      }
      if (c == ')') s = t + 1;
    }
    if (endptr) *endptr = (char *)s;
    return (da){DA_NAN.r | sign};
  }
  /* The significant digits go into m, 19 at most. A nonzero digit beyond
     these sets sticky, which is later appended as a twentieth digit 1: it
     leaves the quotient by a power of ten unchanged and breaks ties
     upward, which is all that a nonzero remainder below one unit can
     do. */
  uint64_t m = 0;
  int sticky = 0, digits = 0, frac = 0, seen = 0;
  long scale = 0; // the value is m * 10^scale, plus sticky
  for (;; s++) {
    c = *s;
    int d = c - '0';
    if (d < 0 || d > 9) {
      if (c == '.' && !frac) { frac = 1; continue; }
      break;
    }
    seen = 1;
    if (m == 0 && d == 0) scale -= frac;
    else if (digits < 19) { m = 10 * m + d; digits++; scale -= frac; }
    else { sticky |= d != 0; scale += !frac; }
  }
  if (!seen) { // nothing to convert: +0, nptr unconsumed
    s = nptr;
    sign = 0;
  }
  else if (c == 'e' || c == 'E') {
    const char *t = s + 1;
    c = *t;
    int eneg = c == '-';
    if (c == '+' || c == '-') {
      t++;
      c = *t;
    }
    if (c >= '0' && c <= '9') {
      long e = 0;
      for (; c >= '0' && c <= '9'; t++, c = *t)
        if (e < 1000000000) e = 10 * e + (c - '0');
      scale += eneg ? -e : e;
      s = t;
    }
  }
  if (endptr) *endptr = (char *)s;
  if (m == 0) return (da){sign};
  // beyond these bounds, the result is infinite or zero whatever m is
  if (scale > 300) scale = 300;
  if (scale < -300) scale = -300;
  // with sticky, m has 19 digits, and the appended one is dropped
  da r = da_round_wide((ulll)m * 10 + sticky, (int)scale + 141);
  return (da){r.r | sign};
}

/* add two positive normal, subnormal or zero das */
/*@
  requires 0 <= dx.r < DA_INFINITY.r;
  requires 0 <= dy.r < DA_INFINITY.r;
*/
static da da_add_pos_pos(da dx, da dy) {
  uint64_t l = dx.r, s = dy.r;
  if (l < s) {
    l = dy.r;
    s = dx.r;
  }
  da_parts lp = da_split(l), sp = da_split(s);
  int d = lp.exp - sp.exp;
  // s is then less than 0.41 units in the last place of l and cannot
  // change it
  if (d > 16) {
    INEXACT(s != 0);
    return (da){l};
  }
  // the exact sum, in units of 10^(sp.exp-142)
  ulll m = (ulll)lp.sd * da_powers[d] + sp.sd;
  // m / 10^d may have overflowed the decade
  return da_round_narrow(m, d, sp.exp);
}

/* subtract two positive normal, subnormal or zero das, dy being at most
   dx */
/*@
  requires 0 <= dy.r <= dx.r < DA_INFINITY.r;
*/
static da da_sub_pos_pos(da dx, da dy) {
  da_parts xp = da_split(dx.r), yp = da_split(dy.r);
  int d = xp.exp - yp.exp;
  // y is then less than 0.05 units in the last place of x and cannot
  // change it. (The value below DECADE_LO is 0.8 unit away, so 0.4 would
  // do, but 17 decades below x, y can still weigh 0.4003.)
  if (d > 17) {
    INEXACT(dy.r != 0);
    return dx;
  }
  // the exact difference fits in 64 bits, and may need normalizing after
  // cancellation
  if (d <= 1)
    return da_from_integer_and_biased_exp(xp.sd * da_powers[d] - yp.sd,
                                          yp.exp);
  // no cancellation: the exact difference, in units of 10^(yp.exp-142),
  // is in x's decade or the one below
  ulll m = (ulll)xp.sd * da_powers[d] - yp.sd;
  return da_round_narrow(m, d - 1, yp.exp);
}

da da_neg(da x) {
  return (da){x.r ^ UINT64_C(0x8000000000000000)};
}

da da_add(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  uint64_t sx = x & SIGN_MASK, sy = y & SIGN_MASK;
  uint64_t posx = x & ~SIGN_MASK, posy = y & ~SIGN_MASK;
  if (posx < DA_INFINITY.r && posy < DA_INFINITY.r) {
    if (sx == sy)
      return (da){sx | da_add_pos_pos((da){posx}, (da){posy}).r};
    // opposite signs, addition to be transformed into subtraction. The
    // result takes the sign of the operand of greater magnitude, and is +0
    // when the magnitudes are equal.
    if (posx == posy) return DA_ZERO;
    uint64_t s = sx, greater = posx, lower = posy;
    if (posx < posy) {
      s = sy;
      greater = posy;
      lower = posx;
    }
    return (da){s | da_sub_pos_pos((da){greater}, (da){lower}).r};
  }
  if (posx > DA_INFINITY.r || posy < DA_INFINITY.r) return dx;
  if (posy > DA_INFINITY.r || posx < DA_INFINITY.r) return dy;
  /* There remains only the cases where both arguments are inf. */
  if (x != y) return DA_NAN;
  return dy;
}
/* multiply two positive normal, subnormal or zero das */
/*@
  requires 0 <= dx.r < DA_INFINITY.r;
  requires 0 <= dy.r < DA_INFINITY.r;
*/
static da da_mult_pos_pos(da dx, da dy) {
  da_parts xp = da_split(dx.r), yp = da_split(dy.r);
  int exp = xp.exp + yp.exp - 125;
  ulll m = (ulll)xp.sd * yp.sd;

  if (m == 0)
    return DA_ZERO;
  return da_round_any_exp(m, (ulll)1e17, exp);
}

/* multiply two das */
da da_mult(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  uint64_t sx = x & SIGN_MASK, sy = y & SIGN_MASK;
  uint64_t posx = x & ~SIGN_MASK, posy = y & ~SIGN_MASK;
  uint64_t s = sx ^ sy;
  uint64_t pos;
  if (posx < DA_INFINITY.r && posy < DA_INFINITY.r)
    pos = da_mult_pos_pos((da){posx}, (da){posy}).r;
  else {
    if (posx > DA_INFINITY.r) return dx;
    if (posy > DA_INFINITY.r) return dy;
    /* There remains only the cases where one argument is inf and the
       other is not Nan. */
    if (posx == 0 || posy == 0)
       return DA_NAN;
    // There remains only inf * finite
    pos = DA_INFINITY.r;
  }
  return (da){pos | s};
}

/* x * y * 10^z with a single rounding. The product of the significand
   by the magnitude of y is exact in 128 bits and may be in any decade
   from 1 to DECADE_HI * 2^63, which is below DECADE_LO * 10^20: one
   lookup of its decade, then at most one multiplication or one division
   by a power of ten, as in fma. y is a positive zero when it is 0. */
/*@ requires -30000 <= z <= 30000; */
da da_mult_integer(da dx, int64_t y, int z) {
  uint64_t x = dx.r, posx = x & ~SIGN_MASK;
  uint64_t s = (x ^ (uint64_t)y) & SIGN_MASK;
  if (posx >= DA_INFINITY.r) {
    if (posx > DA_INFINITY.r) return dx;
    // inf * 0
    if (y == 0) return DA_NAN;
    return (da){s | DA_INFINITY.r};
  }
  da_parts xp = da_split(posx);
  ulll m = (ulll)xp.sd * (y < 0 ? -(uint64_t)y : (uint64_t)y);
  if (m == 0) return (da){s};
  return (da){s | da_round_wide(m, xp.exp + z).r};
}

/* divide two positive normal or subnormal das, neither of which is zero */
/*@
  requires 0 < dx.r < DA_INFINITY.r;
  requires 0 < dy.r < DA_INFINITY.r;
*/
static da da_div_pos_pos(da dx, da dy) {
  da_parts xp = da_split(dx.r), yp = da_split(dy.r);
  // a subnormal divisor is normalized (its biased exponent going negative)
  // so that the quotient of the significands is less than 10
  while (yp.sd < DECADE_LO) {
    yp.sd *= UINT64_C(10);
    yp.exp--;
  }
  // the exact quotient is (m / yp.sd) * 10^(exp-142), m being
  // xp.sd * 1e15. m / yp.sd is below 1e16 < 10 * DECADE_LO, and
  // da_round_any_exp scales it up to DECADE_LO: at most twice when x is
  // normal, as its significand then exceeds yp.sd / 10
  int exp = xp.exp - yp.exp + 127;
  return da_round_any_exp((ulll)xp.sd * (ulll)1e15, yp.sd, exp);
}

/* divide two das */
da da_div(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  uint64_t sx = x & SIGN_MASK, sy = y & SIGN_MASK;
  uint64_t posx = x & ~SIGN_MASK, posy = y & ~SIGN_MASK;
  uint64_t s = sx ^ sy;
  uint64_t pos;
  if (0 < posx && posx < DA_INFINITY.r && 0 < posy && posy < DA_INFINITY.r)
    pos = da_div_pos_pos((da){posx}, (da){posy}).r;
  else {
    if (posx > DA_INFINITY.r) return dx;
    if (posy > DA_INFINITY.r) return dy;
    /* There remains only the cases where an argument is zero or inf. The
       result is then inf, zero or NaN according to the comparison of the
       magnitudes: inf/finite, finite/inf, nonzero/0, 0/nonzero, and
       inf/inf and 0/0. */
    if (posx == posy) return DA_NAN;
    pos = posx > posy ? DA_INFINITY.r : 0;
  }
  return (da){pos | s};
}

/* square root of a positive normal or subnormal da, not zero */
/*@ requires 0 < dx.r < DA_INFINITY.r; */
static da da_sqrt_pos(da dx) {
  da_parts xp = da_split(dx.r);
  // sqrt(sd * 10^(exp-142)) is sqrt(sd * 10^j) * 10^((exp-j)/2 - 71) for
  // j of the parity of exp. j is chosen so that the root has 16 or 17
  // digits: 16 always works for an even exp, 15 or 17 for an odd one. The
  // root is below DECADE_LO exactly when M is below its square.
  int j = 16 - (xp.exp & 1);
  ulll M = (ulll)xp.sd * da_powers[j];
  // at most once when x is normal
  while (M < (ulll)DECADE_LO * DECADE_LO) {
    M *= (ulll)100;
    j += 2;
  }
  int exp = (xp.exp - j) / 2 + 71;
  // M, between 2^103 and 2^112, is converted from its top 47 bits or
  // more, which keeps it in the range of a signed conversion and the
  // binary root within a thousand units of sqrt(M). From there, one
  // Newton step lands on floor(sqrt(M)), or one above it when M is
  // within a million of the next perfect square
  uint64_t r = (int64_t)sqrt((double)(int64_t)(M >> 56) * 0x1p56);
  r = (r + (uint64_t)(M / r)) / 2;
  // the nearest integer n to sqrt(M) is such that n(n-1) < M <= n(n+1). It
  // is never a tie, as that would require M = n^2 + n + 1/4. r is never
  // above n: it exceeds floor(sqrt(M)) only when sqrt(M) is within 2e-10
  // of the integer above, which is then the nearest one.
  ulll sq = (ulll)r * r;
  int up = M > sq + r;
  r += up;
  // the root is exact when M is the square of the final r: sq, or
  // sq + 2r - 1 after the increment. Such an r is never above DECADE_HI:
  // M is a multiple of 10^15, so r would be one of 10^8, and no multiple
  // of 10^8 lies in DECADE_HI + 1 .. DECADE_HI + 8.
  INEXACT(M != sq + up * (2 * r - 1));
  // above DECADE_HI, the candidates are DECADE_HI and the DECADE_LO of the
  // next decade, whose representation is the next one, and the midpoint is
  // DECADE_HI + 4. sqrt(M) is above it only if r was above DECADE_HI.
  if (r > DECADE_HI) r = DECADE_HI;
  return (da){WRAP(r, exp).r
              + (M > (ulll)(DECADE_HI + 4) * (DECADE_HI + 4))};
}

/* square root of a da */
da da_sqrt(da dx) {
  uint64_t x = dx.r;
  if (0 < x && x < DA_INFINITY.r) return da_sqrt_pos(dx);
  uint64_t posx = x & ~SIGN_MASK;
  /* +0, +inf, -0 and NaN are returned unchanged. There remains the
     negative numbers, including -inf. */
  if (x <= DA_INFINITY.r || posx == 0 || posx > DA_INFINITY.r) return dx;
  return DA_NAN;
}

/* The modes are bit sets: bit 2 marks the directed ones, in which bit 0
   rounds positive values away from zero and bit 1 negative ones, and in
   the modes to nearest, bit 0 breaks ties away from zero. */
da da_quantize(da dx, int e, int mode) {
  uint64_t x = dx.r, s = x & SIGN_MASK, pos = x & ~SIGN_MASK;
  // zeros, infinities and NaN are unchanged
  if (pos - 1 >= DA_INFINITY.r - 1) return dx;
  da_parts xp = da_split(pos);
  // the number of low digits of the significand that 10^e does not resolve
  int d = e + 142 - xp.exp;
  if (d <= 0) return dx; // x is a multiple of 10^e already
  // whether a directed mode rounds x away from zero
  int away = mode >> 2 & mode >> (s >> 63) & 1;
  if (d > 16) {
    // the significand, below 5e16, is below 10^e / 2: the result is zero,
    // or 10^e away from zero. 10^16 is a significand, and the biased
    // exponent that goes with it, e + 126, is at least 1.
    INEXACT(1);
    if (!away) return (da){s};
    return (da){s | da_wrap(UINT64_C(10000000000000000),
                            d + xp.exp - 16).r};
  }
  uint64_t p = da_powers[d], n = xp.sd / p, rem = xp.sd - n * p;
  INEXACT(rem != 0);
  int up = mode & 4 ? rem != 0 & away : 2 * rem + (mode | n & 1) > p;
  uint64_t m = xp.sd - rem + (up ? p : 0);
  if (m == 0) return (da){s};
  /* m, a multiple of 10 at the scale of x, is exact with one step at
     most. Above DECADE_HI it is 10 * DECADE_LO or more, the holes holding
     no multiple of 10, and its tenth is in the next decade. Below
     DECADE_LO, x being normal, it is above DECADE_LO / 10, and ten times
     it is in the decade below. Overflow only follows from rounding away
     from zero, where infinity is the result in every mode. */
  int exp = xp.exp;
  if (m > DECADE_HI) {
    m /= 10;
    exp++;
  }
  else if (m < DECADE_LO && exp > 0) {
    m *= 10;
    exp--;
  }
  return (da){s | da_wrap(m, exp).r};
}

da da_fma(da dx, da dy, da dz) {
  uint64_t x = dx.r, y = dy.r, z = dz.r;
  uint64_t posx = x & ~SIGN_MASK, posy = y & ~SIGN_MASK,
    posz = z & ~SIGN_MASK;
  // with an infinite or NaN x or y, neither operation rounds, and with
  // an infinite or NaN z alone, the result is z whatever the product
  if (posx >= DA_INFINITY.r || posy >= DA_INFINITY.r)
    return da_add(da_mult(dx, dy), dz);
  if (posz >= DA_INFINITY.r) return dz;
  da_parts xp = da_split(posx), yp = da_split(posy), zp = da_split(posz);
  /* The product a * 10^ea, exact in 128 bits, and the addend b * 10^eb.
     A zero term takes the unit of the other. The one with the coarser
     unit becomes a: it is scaled to the unit of the other, but not beyond
     decade 17, after which either the units are equal and the sum is
     exact, or a is so large that the part of b below its unit can only
     decide ties, and is folded into a tenth of a unit. a is then above
     DECADE_LO * 10^17, and b / 10 below DECADE_HI^2 / 10, about 0.4 of
     it. */
  ulll a = (ulll)xp.sd * yp.sd, b = zp.sd;
  int ea = xp.exp + yp.exp - 284, eb = zp.exp - 142;
  uint64_t sa = (x ^ y) & SIGN_MASK, sb = z & SIGN_MASK;
  if (a == 0) ea = eb;
  if (b == 0) eb = ea;
  if (ea < eb) {
    ulll t = a; a = b; b = t;
    int u = ea; ea = eb; eb = u;
    uint64_t v = sa; sa = sb; sb = v;
  }
  if (ea > eb) {
    int d = ea - eb, k = 17 - decade(a);
    if (k > d) k = d;
    // k exceeds 19 only for a subnormal addend: a product with a normal
    // factor is DECADE_LO or more, and one of two subnormals is never
    // the coarser term
    ea -= k;
    if (k > 19) {
      a *= da_powers[17];
      k -= 17;
    }
    a *= da_powers[k];
  }
  ulll m;
  uint64_t s = sa;
  if (ea == eb) {
    if (sa == sb) m = a + b;
    else if (a >= b) m = a - b;
    else { m = b - a; s = sb; }
  }
  else {
    /* q is 10^(ea-eb), but 10^17 at most, which keeps it in 64 bits.
       Beyond, a is the addend scaled by 10^17 or more, since an addend b
       would be below q, and 10 * a is a multiple of 10^18. Any nonzero
       10 * bq + sticky below 4 * 10^17 then rounds the same, 4 units of
       10^17 being the margin from the start of a decade to the middle
       of the holes below it, and b / 10^17 is below
       DECADE_HI^2 / 10^17, 1.6 * 10^16. */
    int d = ea - eb;
    uint64_t q = da_powers[d < 17 ? d : 17];
    ulll bq = b / q, sticky = b != bq * q;
    m = sa == sb ? 10 * (a + bq) + sticky : 10 * (a - bq) - sticky;
    ea--;
  }
  if (m == 0) return (da){sa & sb}; // -0 only when both terms are -0
  return (da){s | da_round_wide(m, ea + 142).r};
}

da da_succ(da dx) {
  uint64_t x = dx.r;
  // +0 and positive finite values, the next being one representation up
  if (x < DA_INFINITY.r) return (da){x + 1};
  // -0, followed like +0 by the smallest subnormal
  if (x == SIGN_MASK) return (da){1};
  // -inf and negative finite values, going toward zero one representation
  // down. The smallest negative subnormal is followed by -0.
  if (SIGN_MASK < x && x <= DA_MINUS_INFINITY.r) return (da){x - 1};
  // +inf and NaN are returned unchanged
  return dx;
}

da da_pred(da dx) {
  return da_neg(da_succ(da_neg(dx)));
}

/* The representation transformed so that unsigned comparison follows the
   total order: complemented when negative, which reverses the order of the
   negative values and puts them below the positive ones, whose sign bit is
   set instead. */
static uint64_t total_key(uint64_t r) {
  return r ^ (-(r >> 63) | SIGN_MASK);
}

int da_total_order(da x, da y) {
  uint64_t kx = total_key(x.r), ky = total_key(y.r);
  return (kx > ky) - (kx < ky);
}

int da_compare(da x, da y) {
  uint64_t posx = x.r & ~SIGN_MASK, posy = y.r & ~SIGN_MASK;
  if (posx > DA_INFINITY.r || posy > DA_INFINITY.r) return DA_UNORDERED;
  if ((posx | posy) == 0) return 0;
  return da_total_order(x, y);
}

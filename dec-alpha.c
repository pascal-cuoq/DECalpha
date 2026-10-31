#include <math.h>
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
#error "dec-alpha.c needs a 128-bit unsigned integer type"
#endif

#define DECADE_LO DA_DECADE_LO
#define DECADE_HI DA_DECADE_HI

/* After subtracting DECADE_LO from the representation of a normal da,
   shift by EXP_SHIFT to obtain the biased exponent: */
#define EXP_SHIFT 55
#define SIGN_MASK UINT64_C(0x8000000000000000)
#define SD_MASK ((UINT64_C(1)<<EXP_SHIFT)-1)

#define WRAP(sd, exp) \
  (da){DECADE_LO + ((sd - DECADE_LO) | ((uint64_t)exp << EXP_SHIFT))}

/* The minimum unbiased exponent: */
#define EXP_MIN (-142)

/* The biased exponent of inf and NaN: */
#define EXP_INFNAN 255

/* The inexact flag, raised where results are rounded when this file is
   compiled with DA_INEXACT defined, and untouched otherwise: */
_Thread_local int da_inexact;

#ifdef DA_INEXACT
#define INEXACT(cond) (da_inexact |= (cond))
#else
#define INEXACT(cond) ((void)0)
#endif

const uint64_t da_powers[18]= {
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
};

static char *copy(char *p, const char *s, int n) {
  for (int i = 0; i < n; i++) p[i] = s[i];
  return p + n;
}

static char *fill(char *p, char c, int n) {
  for (int i = 0; i < n; i++) p[i] = c;
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
   its value is sd * 10^(exp-142). Subnormals and zero have exp 0. */
/*@ requires 0 <= r < DA_INFINITY.r; */
static da_parts da_split(uint64_t r) {
  int64_t o = (int64_t)r - (int64_t)DECADE_LO;
  if (o < 0) return (da_parts){r, 0}; // subnormal or zero
  return (da_parts){DECADE_LO + (o & SD_MASK), o >> EXP_SHIFT};
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
  else if (2 * rem > p || 2 * rem == p && (sd & 1))
    sd++;
  if (exp >= EXP_INFNAN) {
    INEXACT(1); // overflow
    return DA_INFINITY;
  }
  return WRAP(sd, exp);
}

/* Same as da_round, but exp may be negative, denoting a subnormal or zero
   result. */
/*@
  requires DECADE_LO <= m / p < 10 * DECADE_LO;
  requires exp < 0 ==> p * 10^-exp < 2^128;
*/
static da da_round_any_exp(ulll m, ulll p, int exp) {
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
   result being infinite or zero when out of range. */
/*@ requires m != 0; */
static da da_round_wide(ulll m, int exp) {
  while (exp > 0 && m < DECADE_LO) {
    exp--;
    m *= (ulll)10;
  }
  // p is the power of ten that brings m down to a decade
  ulll p = 1;
  int j = 0;
  for (ulll t = m; t >= (ulll)DECADE_LO * 10; t /= 10) {
    p *= 10;
    j++;
  }
  return da_round_any_exp(m, p, exp + j);
}

/*@ requires 0 <= exp < EXP_INFNAN; */
da da_from_integer_and_biased_exp(uint64_t i, int exp) {
  if (i == 0) return DA_ZERO;
  while (exp > 0 && i < DECADE_LO) {
    exp--;
    i *= UINT64_C(10);
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
  if (!seen) {
    if (endptr) *endptr = (char *)nptr;
    return DA_ZERO;
  }
  if (c == 'e' || c == 'E') {
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
  int exp = (int)scale + 142;
  while (exp > 0 && m < DECADE_LO) {
    exp--;
    m *= UINT64_C(10);
  }
  // m has at most 19 digits, up to 3 more than fit in a decade
  int j = (m >= DECADE_LO * 10) + (m >= DECADE_LO * 100)
        + (m >= DECADE_LO * 1000);
  da r = da_round_any_exp((ulll)m * 10 + sticky, da_powers[j + 1],
                          exp + j);
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
  // m / 10^d may have overflowed the decade; if so, divide by one more 10
  int j = d + (m >= (ulll)DECADE_LO * da_powers[d + 1]);
  return da_round(m, da_powers[j], sp.exp + j);
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
  int j = d - (m < (ulll)DECADE_LO * da_powers[d]);
  return da_round(m, da_powers[j], yp.exp + j);
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
  while (m < (ulll)DECADE_LO * (ulll)1e17) {
    m *= (ulll)10;
    exp -= 1;
  }
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
  // the exact quotient is (m / yp.sd) * 10^(exp-142). m / yp.sd starts
  // below 1e16 < 10 * DECADE_LO, and is scaled up until it reaches
  // DECADE_LO: at most twice when x is normal, as its significand then
  // exceeds yp.sd / 10
  int exp = xp.exp - yp.exp + 127;
  ulll m = (ulll)xp.sd * (ulll)1e15, t = (ulll)DECADE_LO * yp.sd;
  while (m < t) {
    m *= (ulll)10;
    exp--;
  }
  return da_round_any_exp(m, yp.sd, exp);
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
  // the binary floating-point root is within a dozen units of sqrt(M),
  // from where one Newton step lands on floor(sqrt(M)), or one above it
  // when M is within a few hundred of the next perfect square
  uint64_t r = sqrt((double)M);
  r = (r + (uint64_t)(M / r)) / 2;
  // the nearest integer n to sqrt(M) is such that n(n-1) < M <= n(n+1). It
  // is never a tie, as that would require M = n^2 + n + 1/4. r is never
  // above n: it exceeds floor(sqrt(M)) only when sqrt(M) is within 1e-13
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

da da_quantize(da dx, int e) {
  uint64_t x = dx.r, s = x & SIGN_MASK, pos = x & ~SIGN_MASK;
  if (pos >= DA_INFINITY.r) return dx;
  da_parts xp = da_split(pos);
  // the number of low digits of the significand that 10^e does not resolve
  int64_t d = (int64_t)e + 142 - xp.exp;
  if (d <= 0) return dx; // x is a multiple of 10^e already
  // the significand, below 5e16, is then below 10^e / 2
  if (d > 16) {
    INEXACT(pos != 0);
    return (da){s};
  }
  uint64_t p = da_powers[d], n = xp.sd / p, rem = xp.sd - n * p;
  INEXACT(rem != 0);
  n += 2 * rem > p || 2 * rem == p && (n & 1);
  if (n == 0) return (da){s};
  return (da){s | da_round_wide(n, e + 142).r};
}

#define LIMIT ((ulll)1 << 120)

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
     The one with the coarser unit becomes a: it is scaled to the unit of
     the other as long as it fits, after which either the units are equal
     and the sum is exact, or a is so large that the part of b below its
     unit can only decide ties, and is folded into a tenth of a unit. */
  ulll a = (ulll)xp.sd * yp.sd, b = zp.sd;
  int ea = xp.exp + yp.exp - 284, eb = zp.exp - 142;
  uint64_t sa = (x ^ y) & SIGN_MASK, sb = z & SIGN_MASK;
  if (ea < eb) {
    ulll t = a; a = b; b = t;
    int u = ea; ea = eb; eb = u;
    uint64_t v = sa; sa = sb; sb = v;
  }
  while (ea > eb && a < LIMIT) {
    a *= (ulll)10;
    ea--;
  }
  ulll m;
  uint64_t s = sa;
  if (ea == eb) {
    if (sa == sb) m = a + b;
    else if (a >= b) m = a - b;
    else { m = b - a; s = sb; }
  }
  else {
    // q is 10^(ea-eb), or any larger power of ten when b is below it
    // anyway
    ulll q = 1;
    for (int d = ea - eb; d > 0 && q <= b; d--) q *= 10;
    ulll bq = b / q, sticky = b % q != 0;
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

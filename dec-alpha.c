#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>

typedef struct { uint64_t r;} da;

typedef __uint128_t ulll;
  /* needed for access to 64x64->128 multiplication and 128/64->64 division
     that the host processor hopefully provides. */

// Decades range from DECADE_LO to DECADE_HI
#define DECADE_LO UINT64_C(4003199668773775)
#define DECADE_HI UINT64_C(40031996687737742)


/* After subtracting DECADE_LO from the representation of a normal da,
   shift by EXP_SHIFT to obtain the biased exponent: */
#define EXP_SHIFT 55
#define SIGN_MASK UINT64_C(0x8000000000000000)
#define SD_MASK ((UINT64_C(1)<<EXP_SHIFT)-1)

#define WRAP(sd, exp) \
  (da){DECADE_LO + ((sd - DECADE_LO) | ((uint64_t)exp << EXP_SHIFT))}

/* The minimum unbiased exponent: */
#define EXP_MIN (-140)

/* The biased exponent of inf and NaN: */
#define EXP_INFNAN 255

static const da INFINITY = {UINT64_C(0x7f80000000000000)+DECADE_LO};
static const da NAN = {UINT64_C(0x7f80000000000000)+DECADE_LO+1};
static const da POS_ZERO = {0};

static uint64_t powers[17]= {
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
};

// Prints a DEC alpha in somewhat human-readable form
void da_print(da d) {
  uint64_t n = d.r;
  uint64_t a = n & ~SIGN_MASK;
  if (a != n) printf("-");
  int64_t o = (int64_t)a - (int64_t)DECADE_LO;
  if (o < 0) { // subnormal or zero
      printf("%" PRIu64 "E%d", a, EXP_MIN);
      return;
    }
  int e = o >> EXP_SHIFT;
  uint64_t sd = o & SD_MASK;
  if (e == EXP_INFNAN) {
      if (sd) {
          printf("NaN");
        }
      else {
          printf("inf");
        }
      return;
    }
  sd += DECADE_LO;
  printf("%" PRIu64 "E%d", sd, EXP_MIN+e);
}

// Returns the closest DEC alpha representation of i * 10^(exp-140)
/*@ requires 0 <= exp <= 0x7ffffff0; */
da da_from_integer_and_biased_exp(uint64_t i, int exp) {
  if (i > DECADE_HI) {
    uint64_t factor, tenth;
    if (i > DECADE_HI * UINT64_C(10)) {
      factor = 100;
      tenth = 10;
      exp += 2;
    }
    else {
      factor = 10;
      tenth = 1;
      exp++;
    }
    uint64_t candidate = i / factor;
    uint64_t remainder = i % factor;
    uint64_t half;
    if (candidate == DECADE_HI) {
      half = 4 * tenth;
      if (remainder > half) { // DECADE_LO is odd
        candidate = DECADE_LO;
        exp++;
      }
    }
    else {
      half = 5 * tenth;
      if (remainder > half || (remainder == half && (candidate & UINT64_C(1))))
        candidate++;
    }
    if (exp >= EXP_INFNAN)
      return INFINITY;
    else
      return WRAP(candidate, exp);
  }
  else {
    while (exp > 0 && i < DECADE_LO) {
      exp--;
      i *= UINT64_C(10);
    }
    // This expression is the correct one for the normalized case.
    // It works by miracle for the denormalized case (despite
    // i - DECADE_LO underflowing to 0xffff… in this case) because exp is
    // also 0 in this case.
    return WRAP(i, exp);
  }
}

da da_from_integer(uint64_t i) {
  return da_from_integer_and_biased_exp(i, 140);
}

// Returns the closest DEC alpha representation of i * 10^(exp-140)
// When set, extra requires rounding up if the value is halfway
/*@
  requires 0 <= exp <= 0x7ffffff0;
  requires i > DECADE_HI;
*/
da da_from_large_integer_and_biased_exp(uint64_t i, int exp, _Bool extra) {
  uint64_t factor, tenth, candidate, remainder;
  if (i > DECADE_HI * UINT64_C(10)) {
    factor = 100;
    candidate = i / 100;
    tenth = 10;
    exp += 2;
  }
  else {
    factor = 10;
    candidate = i / 10;
    tenth = 1;
    exp++;
  }
  remainder = i - candidate*factor;
  uint64_t half;
  if (candidate == DECADE_HI) {
    half = 4 * tenth;
    if (remainder > half || (remainder == half && extra)) {
      candidate = DECADE_LO;
      exp++;
    }
  }
  else {
    half = 5 * tenth;
    _Bool above = remainder > half;
    _Bool halfway = remainder == half;
    if (above || (halfway && (extra || (candidate & UINT64_C(1)))))
      candidate++;
  }
  if (exp >= EXP_INFNAN)
    return INFINITY;
  else
    return WRAP(candidate, exp);
}

/* add two positive normal, subnormal or zero das */
/*@
  requires 0 <= dx.r < INFINITY.r;
  requires 0 <= dy.r < INFINITY.r;
*/
da da_add_pos_pos(da dx, da dy) {
  uint64_t l, s, lsd, ssd, x = dx.r, y = dy.r;
  int lexp, sexp;
  if (x > y) {
    l = x;
    s = y;
  }
  else {
    l = y;
    s = x;
  }
  int64_t lo = (int64_t)l - (int64_t)DECADE_LO;
  if (lo < 0) { // subnormal or zero
    lexp = 0;
    lsd = l;
  }
  else {
    lexp = lo >> EXP_SHIFT;
    lsd = DECADE_LO + (lo & SD_MASK);
  }
  int64_t so = (int64_t)s - (int64_t)DECADE_LO;
  if (so < 0) { // subnormal or zero
    sexp = 0;
    ssd = s;
  }
  else {
    sexp = so >> EXP_SHIFT;
    ssd = DECADE_LO + (so & SD_MASK);
  }

  if (lexp == sexp) {
    return da_from_integer_and_biased_exp(lsd + ssd, lexp);
  }
  if (lexp - sexp >= 17) {
    return (da){l};
  }

  lexp--;
  lsd *= UINT64_C(10);
  uint64_t power_diff = powers[lexp - sexp];
  uint64_t d = ssd / power_diff;
  uint64_t r = ssd % power_diff;
  _Bool extra = (r != 0);

  return da_from_large_integer_and_biased_exp(lsd + d, lexp, extra);
}

/* subtract two positive normal, subnormal or zero das,
   y being less than x. */
/*@
  requires 0 <= dx.r < INFINITY.r;
  requires 0 <= dy.r < INFINITY.r;
  requires y <= x;
*/
da da_sub_pos_pos(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  int64_t xo = (int64_t)x - (int64_t)DECADE_LO;
  uint64_t xsd;
  int xexp;
  if (xo < 0) { // subnormal or zero
    xexp = 0;
    xsd = x;
  }
  else {
    xexp = xo >> EXP_SHIFT;
    xsd = DECADE_LO + (xo & SD_MASK);
  }
  int64_t yo = (int64_t)y - (int64_t)DECADE_LO;
  uint64_t ysd;
  int yexp;
  if (yo < 0) { // subnormal or zero
    yexp = 0;
    ysd = y;
  }
  else {
    yexp = yo >> EXP_SHIFT;
    ysd = DECADE_LO + (yo & SD_MASK);
  }
  if (xexp - yexp >= 18) {
    return (da){x};
  }
  _Bool one_decade_above = (xexp == yexp + 1);
  if (one_decade_above) {
    xsd *= UINT64_C(10);
  }
  if (one_decade_above || xexp == yexp) {
    return da_from_integer_and_biased_exp(xsd - ysd, yexp);
  }
  xexp-=2;
  xsd *= UINT64_C(100);

  uint64_t power_diff = powers[xexp - yexp];
  uint64_t d = ysd / power_diff;
  uint64_t r = ysd % power_diff;
  _Bool extra = (r != 0);
  // if the initial y was slightly more than d * 10^xexp, then
  // compute (x - (d+1)*10^xexp) + extra, which gives the same end result
  d += extra;
  return da_from_large_integer_and_biased_exp(xsd - d, xexp, extra);
}

da da_neg(da x) {
  return (da){x.r ^ UINT64_C(0x8000000000000000)};
}

da da_add(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  uint64_t sx = x & SIGN_MASK, sy = y & SIGN_MASK;
  uint64_t posx = x & ~SIGN_MASK, posy = y & ~SIGN_MASK;
  if (posx < INFINITY.r && posy < INFINITY.r) {
    if (sx == sy)
      return (da){sx | da_add_pos_pos((da){posx}, (da){posy}).r};
    // opposite signs, addition to be transformed into subtraction
    uint64_t greater, lower;
    uint64_t s;
    if (posx >= posy) {
      s = sx;
      greater = posx;
      lower = posy;
    }
    else {
      s = sy;
      greater = posy;
      lower = posx;
    }
    return (da){s | (da_sub_pos_pos((da){greater}, (da){lower})).r};
  }
  if (posx > INFINITY.r || posy < INFINITY.r) return dx;
  if (posy > INFINITY.r || posx < INFINITY.r) return dy;
  /* There remains only the cases where both arguments are inf. */
  if (x != y) return NAN;
  return dy;
}
/* multiply two positive normal, subnormal or zero das */
/*@
  requires 0 <= dx.r < INFINITY.r;
  requires 0 <= dy.r < INFINITY.r;
*/
da da_mult_pos_pos(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  int64_t xo = (int64_t)x - (int64_t)DECADE_LO;
  uint64_t xsd;
  int xexp;
  if (xo < 0) { // subnormal or zero
    xexp = 0;
    xsd = x;
  }
  else {
    xexp = xo >> EXP_SHIFT;
    xsd = DECADE_LO + (xo & SD_MASK);
  }
  int64_t yo = (int64_t)y - (int64_t)DECADE_LO;
  uint64_t ysd;
  int yexp;
  if (yo < 0) { // subnormal or zero
    yexp = 0;
    ysd = y;
  }
  else {
    yexp = yo >> EXP_SHIFT;
    ysd = DECADE_LO + (yo & SD_MASK);
  }
  int exp = xexp + yexp - 123;
  ulll m = (ulll)xsd * (ulll)ysd;

  if (m == 0)
    return POS_ZERO;
  while (m < (ulll)DECADE_LO * (ulll)1e17) {
    m *= (ulll)10;
    exp -= 1;
  }

  uint64_t sd;
  uint64_t rem;
  sd = m / (uint64_t)1e17;
  rem = m % (uint64_t)1e17;
  if (exp < 0) {
    if (exp < -16) return POS_ZERO;
    uint64_t p = powers[-exp];
    uint64_t rsd = sd / p;
    uint64_t rrem = sd % p;
    uint64_t half = p >> 1;
    if (rrem > half || rrem == half && (rem || (sd & 1)))
      rsd++;
    return (da){rsd}; // exponent is 0
  }

  if (sd >= DECADE_HI + 4 ||
      sd == DECADE_HI + 4 && rem > 0) { // DECADE_LO is odd
    exp++;
    sd = DECADE_LO;
  }
  else if (sd >= DECADE_HI - 5) { // DECADE_HI is even
    sd = DECADE_HI;
  }
  else if (rem > (uint64_t)5e16 || rem == (uint64_t)5e16 && (sd & 1))
    sd++;
  if (exp >= EXP_INFNAN) return INFINITY;
  return WRAP(sd, exp);
}

/* multiply two das */
da da_mult(da dx, da dy) {
  uint64_t x = dx.r, y = dy.r;
  uint64_t sx = x & SIGN_MASK, sy = y & SIGN_MASK;
  uint64_t posx = x & ~SIGN_MASK, posy = y & ~SIGN_MASK;
  uint64_t s = sx ^ sy;
  uint64_t pos;
  if (posx < INFINITY.r && posy < INFINITY.r)
    pos = da_mult_pos_pos((da){posx}, (da){posy}).r;
  else {
    if (posx > INFINITY.r) return dx;
    if (posy > INFINITY.r) return dy;
    /* There remains only the cases where one argument is inf and the other is
       not Nan. */
    if (posx == 0 || posy == 0)
       return NAN;
    // There remains only inf * finite
    pos = INFINITY.r;
  }
  return (da){pos | s};
}

// TODO: make work for negative values and corner cases
da da_pred(da x) {
  return (da){x.r - 1};
}
da da_succ(da x) {
  return (da){x.r + 1};
}

int main(void)
{
  da_print((da){0});puts("");
  da_print((da){1});puts("");
  da_print((da){2});puts("");
  puts("...");
  da_print((da){DECADE_LO-2});puts("");
  da_print((da){DECADE_LO-1});puts("");
  da_print((da){DECADE_LO});puts("");
  da_print((da){DECADE_LO+1});puts("");
  da_print((da){DECADE_LO+2});puts("");
  puts("...");
  da_print((da){DECADE_HI-2});puts("");
  da_print((da){DECADE_HI-1});puts("");
  da_print((da){DECADE_HI});puts("");
  da_print((da){DECADE_HI+1});puts("");
  da_print((da){DECADE_HI+2});puts("");
  puts("...");
  da one = da_from_integer(1);
  da_print(da_pred(one));puts("");
  da_print(one);puts("");
  da_print(da_succ(one));puts("");
  puts("...");
  da two = da_add(one, one);
  da_print(two);puts("");
  puts("...");
  da three = da_add(two, one);
  da_print(three);puts(" (2+1)");
  puts("...");
  da five = da_add(two, three);
  da_print(five);puts(" (2+3)");
  puts("...");
  da eight = da_add(five, three);
  da_print(eight);puts(" (5+3))");
  puts("...");
  da eleven = da_add(eight, three);
  da_print(eleven);puts(" (8+3)");
  puts("...");
  da_print((da){0x4000000000000000});puts("\n...");
  da DA_MAX=da_pred(INFINITY);
  da_print(da_pred(DA_MAX));puts("");
  da_print(DA_MAX);puts(" DA_MAX");
  da_print(INFINITY);puts("");
  da_print(da_succ(INFINITY));puts("\n\nCountdown:");
  da x = eleven;
  for (int i = 11; i>0; i--) {
    x = i&1 ? da_sub_pos_pos(x, one) : da_add(x, da_neg(one));
    da_print(x);puts("");
  }
  puts("\nMultiplication:");
  x = da_mult(five, eight);
  da_print(x);puts(" (8*5)");
  x = da_mult(eight, eight);
  da_print(x);puts(" (8*8)");
  x = da_mult(five, five);
  da_print(x);puts(" (5*5)");
  da third = da_from_integer_and_biased_exp(333333333333333333,122);
  da_print(da_mult(third, three));puts(" (3*.333...)");
  da ninth = da_mult(third, third);
  da_print(ninth);puts(" (.333...*.333...)");
  da_print(da_mult(ninth, eleven));puts(" (11*.111...)");
  puts("\nMultiplication of subnormal operand:");
  da_print(da_mult((da){1}, DA_MAX));puts(" (1E-140*DA_MAX)");
  da_print(da_mult((da){9}, DA_MAX));puts(" (9E-140*DA_MAX)");
  da_print(da_mult((da){987654321}, DA_MAX));
  puts(" (987654321E-140*DA_MAX)");
  puts("\nSubnormal result of multiplication:");
  da_print(da_mult((da){1001}, da_from_integer(999)));
  puts(" (1001E-140*999)");
  da_print(da_mult(da_from_integer_and_biased_exp(99999,70),da_from_integer_and_biased_exp(10000001,70)));
  puts(" (99999E-70*10000001E-70)");
  da_print(da_mult(da_from_integer_and_biased_exp(1234567899999,70),da_from_integer_and_biased_exp(1001,70)));
  puts(" (1234567899999E-70*1001E-70)");
  da_print(da_mult(da_from_integer_and_biased_exp(123456,69),da_from_integer_and_biased_exp(10000001,60)));
  puts(" (123456E-69*10000001E-60)");
  da_print(da_mult(da_from_integer_and_biased_exp(523456,68),da_from_integer_and_biased_exp(10000001,59)));
  puts(" (523456E-68*10000001E-59)");
  da_print(da_mult(da_from_integer_and_biased_exp(423456,68),da_neg(da_from_integer_and_biased_exp(10000001,59))));
  puts(" (423456E-68*(-10000001E-59))");
}

#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>

typedef struct { uint64_t r;} decalpha;

typedef __uint128_t ulll;
  /* needed for access to 64x64->128 multiplication and 128/64->64 division
     that the host processor hopefully provides. */

// Decades range from DECADE_LO to DECADE_HI
#define DECADE_LO UINT64_C(4003199668773775)
#define DECADE_HI UINT64_C(40031996687737742)

/* After subtracting DECADE_LO from the representation of a normal decalpha,
   shift by EXP_SHIFT to obtain the biased exponent: */
#define EXP_SHIFT 55

#define SIGN_MASK UINT64_C(0x8000000000000000)
#define SD_MASK UINT64_C(0x7fffffffffffff)

#define WRAP(sd, exp) \
  (decalpha){DECADE_LO + ((sd - DECADE_LO) | ((uint64_t)exp << EXP_SHIFT))}

/* The minimum unbiased exponent: */
#define EXP_MIN (-140)

/* The biased exponent of inf and NaN: */
#define EXP_INFNAN 255

static const decalpha INFINITY = {UINT64_C(0x7f80000000000000)+DECADE_LO};
static const decalpha NAN = {UINT64_C(0x7f80000000000000)+DECADE_LO+1};
static const decalpha POS_ZERO = {0};

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
void print(decalpha d) {
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
decalpha from_integer_and_biased_exp(uint64_t i, int exp) {
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

// Returns the closest DEC alpha representation of i * 10^(exp-140)
// When set, extra requires rounding up if the value is halfway
/*@
  requires 0 <= exp <= 0x7ffffff0;
  requires i > DECADE_HI;
*/
decalpha from_large_integer_and_biased_exp(uint64_t i, int exp, _Bool extra) {
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

/* add two positive normal, subnormal or zero decalpha numbers */
decalpha add_pos_pos(decalpha dx, decalpha dy) {
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
    return from_integer_and_biased_exp(lsd + ssd, lexp);
  }
  if (lexp - sexp >= 17) {
    return (decalpha){l};
  }

  lexp--;
  lsd *= UINT64_C(10);
  uint64_t power_diff = powers[lexp - sexp];
  uint64_t d = ssd / power_diff;
  uint64_t r = ssd % power_diff;
  _Bool extra = (r != 0);

  return from_large_integer_and_biased_exp(lsd + d, lexp, extra);
}

/* subtract two positive normal, subnormal or zero decalpha numbers,
   y being less than x. */
decalpha sub_pos_pos(decalpha dx, decalpha dy) {
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
    return (decalpha){x};
  }
  _Bool one_decade_above = (xexp == yexp + 1);
  if (one_decade_above) {
    xsd *= UINT64_C(10);
  }
  if (one_decade_above || xexp == yexp) {
    return from_integer_and_biased_exp(xsd - ysd, yexp);
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
  return from_large_integer_and_biased_exp(xsd - d, xexp, extra);
}

decalpha neg(decalpha x) {
  return (decalpha){x.r ^ UINT64_C(0x8000000000000000)};
}

/* multiply two positive normal, subnormal or zero decalpha numbers */
decalpha mult_pos_pos(decalpha dx, decalpha dy) {
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
    return (decalpha){rsd}; // exponent is 0
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

/* multiply two decalpha numbers */
decalpha mult(decalpha dx, decalpha dy) {
  uint64_t x = dx.r, y = dy.r;
  uint64_t sx = x & SIGN_MASK, sy = y & SIGN_MASK;
  uint64_t posx = x & ~SIGN_MASK, posy = y & ~SIGN_MASK;
  uint64_t s = sx ^ sy;
  uint64_t pos;
  if (posx < INFINITY.r && posy < INFINITY.r)
    pos = mult_pos_pos((decalpha){posx}, (decalpha){posy}).r;
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
  return (decalpha){pos | s};
}

// TODO: make work for negative values and corner cases
decalpha pred(decalpha x) {
  return (decalpha){x.r - 1};
}
decalpha succ(decalpha x) {
  return (decalpha){x.r + 1};
}

int main(void)
{
  print((decalpha){0});puts("");
  print((decalpha){1});puts("");
  print((decalpha){2});puts("");
  puts("...");
  print((decalpha){DECADE_LO-2});puts("");
  print((decalpha){DECADE_LO-1});puts("");
  print((decalpha){DECADE_LO});puts("");
  print((decalpha){DECADE_LO+1});puts("");
  print((decalpha){DECADE_LO+2});puts("");
  puts("...");
  print((decalpha){DECADE_HI-2});puts("");
  print((decalpha){DECADE_HI-1});puts("");
  print((decalpha){DECADE_HI});puts("");
  print((decalpha){DECADE_HI+1});puts("");
  print((decalpha){DECADE_HI+2});puts("");
  puts("...");
  decalpha one = from_integer_and_biased_exp(1,140);
  print(pred(one));puts("");
  print(one);puts("");
  print(succ(one));puts("");
  puts("...");
  decalpha two = add_pos_pos(one, one);
  print(two);puts("");
  puts("...");
  decalpha three = add_pos_pos(two, one);
  print(three);puts(" (2+1)");
  puts("...");
  decalpha five = add_pos_pos(two, three);
  print(five);puts(" (2+3)");
  puts("...");
  decalpha eight = add_pos_pos(five, three);
  print(eight);puts(" (5+3))");
  puts("...");
  decalpha eleven = add_pos_pos(eight, three);
  print(eleven);puts(" (8+3)");
  puts("...");
  print((decalpha){0x4000000000000000});puts("\n...");
  decalpha DA_MAX=pred(INFINITY);
  print(pred(DA_MAX));puts("");
  print(DA_MAX);puts(" DA_MAX");
  print(INFINITY);puts("");
  print(succ(INFINITY));puts("\n\nCountdown:");
  decalpha x = eleven;
  for (int i = 11; i>0; i--) {
    x = sub_pos_pos(x, one);
    print(x);puts("");
  }
  puts("\nMultiplication:");
  x = mult_pos_pos(five, eight);
  print(x);puts(" (8*5)");
  x = mult_pos_pos(eight, eight);
  print(x);puts(" (8*8)");
  x = mult_pos_pos(five, five);
  print(x);puts(" (5*5)");
  decalpha third = from_integer_and_biased_exp(333333333333333333,122);
  print(mult_pos_pos(third, three));puts(" (3*.333...)");
  decalpha ninth = mult_pos_pos(third, third);
  print(ninth);puts(" (.333...*.333...)");
  print(mult_pos_pos(ninth, eleven));puts(" (11*.111...)");
  puts("\nMultiplication of subnormal operand:");
  print(mult_pos_pos((decalpha){1}, DA_MAX));puts(" (1E-140*DA_MAX)");
  print(mult_pos_pos((decalpha){9}, DA_MAX));puts(" (9E-140*DA_MAX)");
  print(mult_pos_pos((decalpha){987654321}, DA_MAX));
  puts(" (987654321E-140*DA_MAX)");
  puts("\nSubnormal result of multiplication:");
  print(mult_pos_pos((decalpha){1001}, from_integer_and_biased_exp(999,140)));
  puts(" (1001E-140*999)");
  print(mult_pos_pos(from_integer_and_biased_exp(99999,70),from_integer_and_biased_exp(10000001,70)));
  puts(" (99999E-70*10000001E-70)");
  print(mult_pos_pos(from_integer_and_biased_exp(1234567899999,70),from_integer_and_biased_exp(1001,70)));
  puts(" (1234567899999E-70*1001E-70)");
  print(mult_pos_pos(from_integer_and_biased_exp(123456,69),from_integer_and_biased_exp(10000001,60)));
  puts(" (123456E-69*10000001E-60)");
  print(mult_pos_pos(from_integer_and_biased_exp(523456,68),from_integer_and_biased_exp(10000001,59)));
  puts(" (523456E-68*10000001E-59)");
  print(mult_pos_pos(from_integer_and_biased_exp(423456,68),from_integer_and_biased_exp(10000001,59)));
  puts(" (423456E-68*10000001E-59)");
}

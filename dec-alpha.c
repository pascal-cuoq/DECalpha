#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>

typedef uint64_t decalpha;

// Decades range from DECADE_LO to DECADE_HI
#define DECADE_LO UINT64_C(4003199668773775)
#define DECADE_HI UINT64_C(40031996687737742)

#define EXP_MIN (-140)

// The DEC alpha value +inf
#define INFINITY (UINT64_C(0x7f80000000000000)+DECADE_LO)

uint64_t powers[16]= {
  1,
  10,
  1e2,
  1e3,
  1e4,
  1e5,
  1e7,
  1e8,
  1e9,
  1e10,
  1e11,
  1e12,
  1e13,
  1e14,
  1e15,
};

// Prints a DEC alpha in somehwat human-readable form
void print(decalpha n) {
  uint64_t a = n & UINT64_C(0x7fffffffffffffff);
  if (a != n) printf("-");
  int64_t o = (int64_t)a - (int64_t)DECADE_LO;
  if (o < 0) // subnormal or zero
    {
      printf("%" PRIu64 "E%d", a, EXP_MIN);
      return;
    }
  int e = o >> 55;
  uint64_t sd = o & UINT64_C(0x7fffffffffffff);
  if (e == 0xff) { // infinity or NaN
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
      if (remainder > half) {
        candidate = DECADE_LO;
        exp++;
      }
    }
    else {
      half = 5 * tenth;
      if (remainder > half || (remainder == half && (candidate & UINT64_C(1))))
        candidate++;
    }
    if (exp >= 255)
      return INFINITY;
    else
      return DECADE_LO + ((candidate - DECADE_LO)| ((uint64_t)exp << 55));
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
    return DECADE_LO + ((i - DECADE_LO) | ((uint64_t)exp << 55));
  }
}

// Returns the closest DEC alpha representation of i * 10^(exp-140)
// When set, extra requires rounding up if the value is halfway
/*@
  requires 0 <= exp <= 0x7ffffff0;
  requires i > DECADE_HI;
*/
decalpha from_large_integer_and_biased_exp(uint64_t i, int exp, _Bool extra) {
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
  if (exp >= 255)
    return INFINITY;
  else
    return DECADE_LO + ((candidate - DECADE_LO)| ((uint64_t)exp << 55));
}

/* add two positive normal, subnormal or zero decalpha numbers */
decalpha add_pos_pos(decalpha x, decalpha y) {
  uint64_t l, s, lsd, ssd;
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
    lexp = lo >> 55;
    lsd = DECADE_LO + (lo & UINT64_C(0x7fffffffffffff));
  }
  int64_t so = (int64_t)s - (int64_t)DECADE_LO;
  if (so < 0) { // subnormal or zero
    sexp = 0;
    ssd = s;
  }
  else {
    sexp = so >> 55;
    ssd = DECADE_LO + (so & UINT64_C(0x7fffffffffffff));
  }

  if (lexp == sexp) {
    return from_integer_and_biased_exp(lsd + ssd, lexp);
  }
  if (lexp - sexp >= 17) {
    return l;
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
decalpha sub_pos_pos(decalpha x, decalpha y) {
  int64_t xo = (int64_t)x - (int64_t)DECADE_LO;
  uint64_t xsd;
  int xexp;
  if (xo < 0) { // subnormal or zero
    xexp = 0;
    xsd = x;
  }
  else {
    xexp = xo >> 55;
    xsd = DECADE_LO + (xo & UINT64_C(0x7fffffffffffff));
  }
  int64_t yo = (int64_t)y - (int64_t)DECADE_LO;
  uint64_t ysd;
  int yexp;
  if (yo < 0) { // subnormal or zero
    yexp = 0;
    ysd = y;
  }
  else {
    yexp = yo >> 55;
    ysd = DECADE_LO + (yo & UINT64_C(0x7fffffffffffff));
  }
  if (xexp - yexp >= 18) {
    return x;
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
  return x ^ UINT64_C(0x8000000000000000);
}

int main(void)
{
  print(0);puts("");
  print(1);puts("");
  print(2);puts("");
  puts("...");
  print(DECADE_LO-2);puts("");
  print(DECADE_LO-1);puts("");
  print(DECADE_LO);puts("");
  print(DECADE_LO+1);puts("");
  print(DECADE_LO+2);puts("");
  puts("...");
  print(DECADE_HI-2);puts("");
  print(DECADE_HI-1);puts("");
  print(DECADE_HI);puts("");
  print(DECADE_HI+1);puts("");
  print(DECADE_HI+2);puts("");
  puts("...");
  decalpha one = from_integer_and_biased_exp(1,140);
  print(one - 1);puts("");
  print(one);puts("");
  print(one + 1);puts("");
  puts("...");
  decalpha two = add_pos_pos(one, one);
  print(two);puts("");
  puts("...");
  decalpha three = add_pos_pos(two, one);
  print(three);puts("");
  puts("...");
  decalpha five = add_pos_pos(two, three);
  print(five);puts("");
  puts("...");
  decalpha eight = add_pos_pos(five, three);
  print(eight);puts("");
  puts("...");
  print(0x4000000000000000);puts("");
  print(INFINITY - 2);puts("");
  print(INFINITY - 1);puts("");
  print(INFINITY);puts("");
  print(INFINITY + 1);puts("\n");
  decalpha x = eight;
  for (int i = 8; i>0; i--) {
    x = sub_pos_pos(x, one);
    print(x);puts("");
  }
}

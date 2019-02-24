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
  uint64_t significand = o & UINT64_C(0x7fffffffffffff);
  if (e == 0xff) { // infinity or NaN
      if (significand) {
          printf("NaN");
        }
      else {
          printf("inf");
        }
      return;
    }
  significand += DECADE_LO;
  printf("%" PRIu64 "E%d", significand, EXP_MIN+e);
}

// Returns the closest DEC alpha representation of i * 10^(exp-140)
/*@ requires 0 <= exp <= 0x7ffffff0; */
decalpha from_integer_and_biased_exp(uint64_t i, int exp) {
  if (i > DECADE_HI) {
    uint64_t factor, tenth;
    if (i > DECADE_HI * 10) {
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
      return DECADE_LO + ((candidate - DECADE_LO)| (exp << 55));
  }
  else {
    while (exp > 0 && i < DECADE_LO) {
      exp--;
      i *= UINT64_C(10);
    }
    if (i < DECADE_LO)
      return i;
    else
      return DECADE_LO + ((i - DECADE_LO) | ((uint64_t)exp << 55));
  }
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
  print(from_integer_and_biased_exp(1,140));puts("");
  print(0x4000000000000000);puts("");
  print(INFINITY - 2);puts("");
  print(INFINITY - 1);puts("");
  print(INFINITY);puts("");
  print(INFINITY + 1);puts("");
}

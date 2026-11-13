/* Fixed tests of dec-alpha.c: documented behaviors and hand-checked cases,
   with expected results written down rather than computed. They need
   neither a seed nor GMP; the random tests are in test-random.c.

   Build: cc -std=c11 test-fixed.c dec-alpha.o da_printing.o
          with either build of the library: the inexact flag is checked
          when the library was built with it, and checked to stay clear
          otherwise
   Usage: ./test-fixed [print | strings]       (see print_strings) */

#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dec-alpha.h"

#define SIGN UINT64_C(0x8000000000000000)
#define INF (UINT64_C(0x7f80000000000000) + DA_DECADE_LO)
#define NAN_R (INF + 1)
#define BIAS 142

static long checks, failures;

static void show(const char *what, da d) {
  printf("  %4s = 0x%016" PRIx64 " = ", what, d.r);
  da_print(d);
  puts("");
}

static void expect(const char *what, da got, da want) {
  checks++;
  if (got.r == want.r) return;
  failures++;
  printf("FAIL %s\n", what);
  show("got", got);
  show("want", want);
}

/* ---- strtoda: syntax, special values, endptr, and rounding of long
   numerals. The expected value is m * 10^(e-142), or the representation m
   itself when e is -1. ---- */

static const struct {
  const char *in; uint64_t m; int e, end;
} numerals[] = {
  {"", 0, -1, 0}, {".", 0, -1, 0}, {"-", 0, -1, 0}, {"e5", 0, -1, 0},
  {"+.e5", 0, -1, 0}, {" \t\n-0", SIGN, -1, 5}, {"1e", 1, BIAS, 1},
  {"1e+", 1, BIAS, 1}, {"1.e-x", 1, BIAS, 2}, {"5.", 5, BIAS, 2},
  {".5", 5, BIAS - 1, 2}, {"inf", INF, -1, 3},
  {"-INFINITY", INF | SIGN, -1, 9}, {"infinit", INF, -1, 3},
  {"nan", NAN_R, -1, 3},
  {"-nan(a_1)x", NAN_R | SIGN, -1, 9}, {"nan(a-", NAN_R, -1, 3},
  {"NaN()", NAN_R, -1, 5}, {"0x10", 0, -1, 1}, {"1_000", 1, BIAS, 1},
  {"1e999999999999", INF, -1, 14}, {"1e-999999999999", 0, -1, 15},
  {"-0e5", SIGN, -1, 4}, {"123.45E67", 12345, BIAS + 65, 9},
  /* 10^47 */
  {"100000000000000000000000000000000000000000000000", 1, BIAS + 47, 48},
  /* rounded up on the digit after the 17th */
  {"123456789123456789123456789123456789", UINT64_C(12345678912345679),
   BIAS + 19, 36},
  /* 17 digits, then a tie broken upward by a distant 1 */
  {"12345678912345678500000000000000000000000000001",
   UINT64_C(12345678912345679), BIAS + 30, 47},
  /* 16 digits (a 17th would exceed DECADE_HI) followed by 4999..., rounded
     down */
  {"9876543219876543499999999999999", UINT64_C(9876543219876543),
   BIAS + 15, 31},
  /* 16 digits followed by an exact tie, rounded to the even
     9876543219876544 */
  {"98765432198765435000000000000000000", UINT64_C(9876543219876544),
   BIAS + 19, 35},
  /* between DECADE_HI and the next decade, below the midpoint 4003...746:
     down to DECADE_HI */
  {"40031996687737745999999999999", DA_DECADE_HI, BIAS + 12, 29},
  /* exactly on that midpoint: to DECADE_HI, the even one */
  {"400319966877377460000000", DA_DECADE_HI, BIAS + 7, 24},
  /* just above it: up to DECADE_LO of the next decade */
  {"4003199668773774600000000000000001", DA_DECADE_LO, BIAS + 18, 34},
  /* half the smallest subnormal: to the even 0; above it by a distant
     1: up to it */
  {"5e-143", 0, -1, 6}, {"50000000000000000000001e-165", 1, -1, 28},
  /* a subnormal tie between 1e-142 and 2e-142, to the even one */
  {"15e-143", 2, -1, 7},
};

static void test_numerals(void) {
  for (unsigned i = 0; i < sizeof numerals / sizeof *numerals; i++) {
    char *end;
    da got = strtoda(numerals[i].in, &end);
    da want = numerals[i].e < 0 ? (da){numerals[i].m}
      : da_from_integer_and_biased_exp(numerals[i].m, numerals[i].e);
    expect(numerals[i].in, got, want);
    checks++;
    if (end - numerals[i].in != numerals[i].end) {
      failures++;
      printf("FAIL strtoda endptr on \"%s\": consumed %d\n",
             numerals[i].in, (int)(end - numerals[i].in));
    }
  }
}

/* ---- operations on values written as numerals: signs of zero, special
   values, ties inside a decade and at its ends, the overflow threshold,
   subnormals ---- */

static da val(const char *s) { return strtoda(s, NULL); }

static const struct { const char *op, *x, *y, *z, *want; } cases[] = {
  {"+", "1", "-1", NULL, "0"},
  {"+", "-0", "-0", NULL, "-0"},
  {"+", "-0", "0", NULL, "0"},
  {"+", "0", "-0", NULL, "0"},
  {"+", "inf", "-inf", NULL, "nan"},
  {"+", "inf", "inf", NULL, "inf"},
  {"+", "1", "inf", NULL, "inf"},
  {"+", "-inf", "1", NULL, "-inf"},
  {"+", "40031996687737742e112", "4e112", NULL, "40031996687737742e112"},
  {"+", "40031996687737742e112", "5e112", NULL, "inf"},
  {"+", "40031996687737742", "4", NULL, "40031996687737742"},
  {"+", "40031996687737742", "5", NULL, "40031996687737750"},
  {"+", "40031996687737750", "-4", NULL, "40031996687737742"},
  {"+", "40031996687737750", "-5", NULL, "40031996687737742"},
  {"+", "40031996687737750", "-3", NULL, "40031996687737750"},
  {"+", "1", "5e-17", NULL, "1"},
  {"+", "1.0000000000000001", "5e-17", NULL, "1.0000000000000002"},
  {"+", "1", "-5e-17", NULL, "1"},
  {"+", "1", "-6e-17", NULL, "0.9999999999999999"},
  {"+", "1e-142", "1e-142", NULL, "2e-142"},
  {"+", "1e-142", "-1e-142", NULL, "0"},
  {"+", "4003199668773775e-142", "-1e-142", NULL, "4003199668773774e-142"},
  {"+", "1e16", "1e-1", NULL, "1e16"},
  {"+", "1e16", "0.5", NULL, "1e16"},
  {"+", "1e16", "0.51", NULL, "10000000000000001"},
  {"*", "20015998343868873", "2", NULL, "40031996687737742"},
  {"*", "20015998343868874", "2", NULL, "40031996687737750"},
  {"*", "inf", "0", NULL, "nan"},
  {"*", "-0", "5", NULL, "-0"},
  {"*", "-inf", "-2", NULL, "inf"},
  {"*", "1e-142", "0.4", NULL, "0"},
  {"*", "1e-142", "0.5", NULL, "0"},
  {"*", "1e-142", "0.6", NULL, "1e-142"},
  {"*", "3e-142", "0.5", NULL, "2e-142"},
  {"*", "-3e-142", "0.4", NULL, "-1e-142"},
  {"*", "1e-142", "1e-142", NULL, "0"},
  {"*", "-1e-142", "1e-142", NULL, "-0"},
  {"*", "40031996687737742e112", "1", NULL, "40031996687737742e112"},
  {"*", "40031996687737742e112", "1.0000000000000001", NULL, "inf"},
  {"*", "333333333333333333e-18", "3", NULL, "1"},
  {"/", "20015998343868873", "5", NULL, "4003199668773774.2"},
  {"/", "20015998343868874", "5", NULL, "4003199668773775"},
  {"/", "1", "0", NULL, "inf"},
  {"/", "-1", "0", NULL, "-inf"},
  {"/", "0", "0", NULL, "nan"},
  {"/", "inf", "inf", NULL, "nan"},
  {"/", "1", "-inf", NULL, "-0"},
  {"/", "-0", "-1", NULL, "0"},
  {"/", "inf", "-0", NULL, "-inf"},
  {"/", "1", "3", NULL, "0.33333333333333333"},
  {"/", "2", "3", NULL, "0.6666666666666667"},
  {"/", "1", "1e-142", NULL, "1e142"},
  {"/", "1e-142", "3", NULL, "0"},
  {"/", "2e-142", "3", NULL, "1e-142"},
  {"/", "1", "40031996687737742e112", NULL, "24980018054066e-142"},
  {"/", "1", "4003199668773775e-142", NULL, "24980018054066017e110"},
  {"sqrt", "-0", NULL, NULL, "-0"},
  {"sqrt", "0", NULL, NULL, "0"},
  {"sqrt", "-1", NULL, NULL, "nan"},
  {"sqrt", "inf", NULL, NULL, "inf"},
  {"sqrt", "-inf", NULL, NULL, "nan"},
  {"sqrt", "4", NULL, NULL, "2"},
  {"sqrt", "2", NULL, NULL, "1.4142135623730950"},
  {"sqrt", "4e-142", NULL, NULL, "2e-71"},
  {"sqrt", "2e-142", NULL, NULL, "1.414213562373095e-71"},
  {"sqrt", "1e-142", NULL, NULL, "1e-71"},
  {"sqrt", "16025607588070461e1", NULL, NULL, "4003199668773775e-7"},
  {"sqrt", "40031996687737742e112", NULL, NULL, "20007997572905126e48"},
  {"fma", "1e16", "1e16", "1", "1e32"},
  {"fma", "2", "0.5", "-1", "0"},
  {"fma", "-2", "0.5", "1", "0"},
  {"fma", "-0", "1", "-0", "-0"},
  {"fma", "0", "1", "-0", "0"},
  {"fma", "-0", "1", "0", "0"},
  {"fma", "20015998343868873", "5", "0", "100079991719344360"},
  {"fma", "20015998343868873", "5", "1e-142", "100079991719344370"},
  {"fma", "20015998343868873", "5", "-1e-142", "100079991719344360"},
  {"fma", "1.0000000000000001", "1.0000000000000001", "-1",
   "2.0000000000000001e-16"},
  {"fma", "inf", "0", "1", "nan"},
  {"fma", "inf", "1", "-inf", "nan"},
  {"fma", "1", "1", "nan", "nan"},
  {"fma", "40031996687737742e112", "1", "4e112", "40031996687737742e112"},
  {"fma", "40031996687737742e112", "1", "5e112", "inf"},
  {"fma", "1e-142", "0.5", "0", "0"},
  {"fma", "1e-142", "0.5", "1e-142", "2e-142"},
  /* a zero addend, the product rounded alone, with the product's sign
     even when it rounds to zero */
  {"fma", "40031996687737742", "40031996687737742", "0",
   "1.6025607588070455e33"},
  {"fma", "-40031996687737742", "40031996687737742", "0",
   "-1.6025607588070455e33"},
  {"fma", "-4003199668773775e-142", "4003199668773775e-142", "0", "-0"},
  /* the addend coarser, the product's digits beyond its unit deciding a
     tie, or not */
  {"fma", "1.0000000000000001", "5e-17", "1", "1.0000000000000001"},
  {"fma", "-1.0000000000000001", "5e-17", "1", "0.9999999999999999"},
  /* the product 24 or 25 decades below the scaled addend, divided by
     that power of ten, beyond 64 bits, and 40 decades below, all sticky.
     Subtracted from the start of a decade, it leaves a value in the holes
     below, rounded back up. */
  {"fma", "-1", "1e-25", "1", "1"},
  {"fma", "-1", "1e-25", "4.003199668773775", "4.003199668773775"},
  {"fma", "-1", "1e-40", "4.003199668773775", "4.003199668773775"},
  /* a product beyond the largest value, brought back by the addend */
  {"fma", "40031996687737742e112", "2", "-40031996687737742e112",
   "40031996687737742e112"},
  {"succ", "0", NULL, NULL, "1e-142"},
  {"succ", "-0", NULL, NULL, "1e-142"},
  {"pred", "0", NULL, NULL, "-1e-142"},
  {"pred", "-0", NULL, NULL, "-1e-142"},
  {"succ", "-1e-142", NULL, NULL, "-0"},
  {"pred", "1e-142", NULL, NULL, "0"},
  {"succ", "40031996687737742e112", NULL, NULL, "inf"},
  {"pred", "inf", NULL, NULL, "40031996687737742e112"},
  {"succ", "-inf", NULL, NULL, "-40031996687737742e112"},
  {"pred", "-inf", NULL, NULL, "-inf"},
  {"succ", "inf", NULL, NULL, "inf"},
  {"succ", "1", NULL, NULL, "1.0000000000000001"},
  {"pred", "1", NULL, NULL, "0.9999999999999999"},
  {"pred", "40031996687737750", NULL, NULL, "40031996687737742"},
  {"succ", "40031996687737742", NULL, NULL, "40031996687737750"},
  {"succ", "nan", NULL, NULL, "nan"},
  {"pred", "-nan", NULL, NULL, "-nan"},
  {"neg", "0", NULL, NULL, "-0"},
  {"neg", "nan", NULL, NULL, "-nan"},
  /* sine and cosine: exact angles, signs of zero results as sinPi and
     cosPi, special values, underflow, and 1e128, a multiple of 40
     degrees like every value of magnitude 4e18 or more: 280 here */
  {"sin", "0", NULL, NULL, "0"}, {"sin", "-0", NULL, NULL, "-0"},
  {"sin", "30", NULL, NULL, "0.5"}, {"sin", "90", NULL, NULL, "1"},
  {"sin", "180", NULL, NULL, "0"}, {"sin", "-180", NULL, NULL, "-0"},
  {"sin", "270", NULL, NULL, "-1"}, {"sin", "-360", NULL, NULL, "-0"},
  {"sin", "inf", NULL, NULL, "nan"}, {"sin", "-nan", NULL, NULL, "-nan"},
  {"cos", "-0", NULL, NULL, "1"}, {"cos", "60", NULL, NULL, "0.5"},
  {"cos", "90", NULL, NULL, "0"}, {"cos", "-90", NULL, NULL, "0"},
  {"cos", "270", NULL, NULL, "0"}, {"cos", "180", NULL, NULL, "-1"},
  {"cos", "-inf", NULL, NULL, "nan"},
  {"sin", "1e-142", NULL, NULL, "0"}, {"sin", "-1e-142", NULL, NULL, "-0"},
  {"sin", "45", NULL, NULL, "0.7071067811865475"},
  {"sin", "10", NULL, NULL, "0.17364817766693035"},
  {"cos", "4.5", NULL, NULL, "0.996917333733128"},
  {"sin", "1e128", NULL, NULL, "-0.9848077530122081"},
  {"cos", "1e128", NULL, NULL, "0.17364817766693035"},
  /* tangent: the signs of zeros and infinities are those of the
     quotient of the sine by the cosine, as tanPi */
  {"tan", "0", NULL, NULL, "0"}, {"tan", "-0", NULL, NULL, "-0"},
  {"tan", "45", NULL, NULL, "1"}, {"tan", "135", NULL, NULL, "-1"},
  {"tan", "-45", NULL, NULL, "-1"}, {"tan", "225", NULL, NULL, "1"},
  {"tan", "180", NULL, NULL, "-0"}, {"tan", "-180", NULL, NULL, "0"},
  {"tan", "360", NULL, NULL, "0"}, {"tan", "-360", NULL, NULL, "-0"},
  {"tan", "90", NULL, NULL, "inf"}, {"tan", "-90", NULL, NULL, "-inf"},
  {"tan", "270", NULL, NULL, "-inf"}, {"tan", "-270", NULL, NULL, "inf"},
  {"tan", "inf", NULL, NULL, "nan"}, {"tan", "nan", NULL, NULL, "nan"},
  {"tan", "1e-142", NULL, NULL, "0"}, {"tan", "-1e-142", NULL, NULL, "-0"},
  {"tan", "60", NULL, NULL, "1.7320508075688773"},
  {"tan", "10", NULL, NULL, "0.17632698070846497"},
  {"tan", "1", NULL, NULL, "0.017455064928217586"},
  {"tan", "89", NULL, NULL, "57.289961630759424"},
  {"tan", "89.99999999999999", NULL, NULL, "5729577951308232"},
  {"tan", "1e128", NULL, NULL, "-5.6712818196177096"},
  /* radians to degrees: the special values unchanged, pi and its
     fractions, a subnormal argument, and both sides of the threshold
     of overflow */
  {"degrees", "0", NULL, NULL, "0"}, {"degrees", "-0", NULL, NULL, "-0"},
  {"degrees", "inf", NULL, NULL, "inf"},
  {"degrees", "-inf", NULL, NULL, "-inf"},
  {"degrees", "nan", NULL, NULL, "nan"},
  {"degrees", "-nan", NULL, NULL, "-nan"},
  {"degrees", "3.1415926535897932", NULL, NULL, "180"},
  {"degrees", "-1.5707963267948966", NULL, NULL, "-90"},
  {"degrees", "0.5235987755982989", NULL, NULL, "30.000000000000002"},
  {"degrees", "1", NULL, NULL, "57.29577951308232"},
  {"degrees", "1e-142", NULL, NULL, "57e-142"},
  {"degrees", "-6e-142", NULL, NULL, "-344e-142"},
  {"degrees", "6.986e126", NULL, NULL, "40026831567839309e112"},
  {"degrees", "6.987e126", NULL, NULL, "inf"},
  /* ten to the x: exact for the integers, overflow and underflow at
     their thresholds, subnormal results, and arguments too small to
     move the result from 1 */
  {"exp10", "0", NULL, NULL, "1"}, {"exp10", "-0", NULL, NULL, "1"},
  {"exp10", "1", NULL, NULL, "10"}, {"exp10", "-1", NULL, NULL, "0.1"},
  {"exp10", "128", NULL, NULL, "1e128"},
  {"exp10", "-142", NULL, NULL, "1e-142"},
  {"exp10", "-143", NULL, NULL, "0"},
  {"exp10", "0.5", NULL, NULL, "3.1622776601683793"},
  {"exp10", "-0.5", NULL, NULL, "0.31622776601683793"},
  {"exp10", "3.5", NULL, NULL, "3162.2776601683793"},
  {"exp10", "0.001", NULL, NULL, "1.0023052380778997"},
  {"exp10", "-0.001", NULL, NULL, "0.9977000638225533"},
  {"exp10", "0.3010299956639812", NULL, NULL, "2"},
  {"exp10", "1e-16", NULL, NULL, "1.0000000000000002"},
  {"exp10", "1e-17", NULL, NULL, "1"},
  {"exp10", "-1e-30", NULL, NULL, "1"},
  {"exp10", "128.60240716181945", NULL, NULL, "4.003198836781788e128"},
  {"exp10", "128.7", NULL, NULL, "inf"},
  {"exp10", "-127.5", NULL, NULL, "3.16227766016838e-128"},
  {"exp10", "-141.5", NULL, NULL, "3e-142"},
  {"exp10", "-142.3", NULL, NULL, "1e-142"},
  {"exp10", "-142.4", NULL, NULL, "0"},
  {"exp10", "inf", NULL, NULL, "inf"}, {"exp10", "-inf", NULL, NULL, "0"},
  {"exp10", "nan", NULL, NULL, "nan"},
  {"exp10", "-nan", NULL, NULL, "-nan"},
  /* logarithm: exact for the powers of ten, the subnormal one
     included, next to 1 on both sides, at both ends of the zone
     around 1, and the special values */
  {"log10", "1", NULL, NULL, "0"}, {"log10", "10", NULL, NULL, "1"},
  {"log10", "0.001", NULL, NULL, "-3"},
  {"log10", "1e128", NULL, NULL, "128"},
  {"log10", "1e-142", NULL, NULL, "-142"},
  {"log10", "3e-142", NULL, NULL, "-141.52287874528034"},
  {"log10", "2", NULL, NULL, "0.3010299956639812"},
  {"log10", "0.5", NULL, NULL, "-0.3010299956639812"},
  {"log10", "40031996687737742e112", NULL, NULL, "128.60240725207964"},
  {"log10", "1.0000000000000001", NULL, NULL, "4.342944819032518e-17"},
  {"log10", "0.9999999999999999", NULL, NULL,
   "-4.342944819032518e-17"},
  {"log10", "1.1", NULL, NULL, "0.04139268515822504"},
  {"log10", "1.126", NULL, NULL, "0.05153839051532742"},
  {"log10", "0.9007199254740992", NULL, NULL, "-0.04541022980899665"},
  {"log10", "0.9007199254740991", NULL, NULL, "-0.0454102298089967"},
  {"log10", "0", NULL, NULL, "-inf"}, {"log10", "-0", NULL, NULL, "-inf"},
  {"log10", "-1", NULL, NULL, "nan"}, {"log10", "inf", NULL, NULL, "inf"},
  {"log10", "-inf", NULL, NULL, "nan"},
  {"log10", "nan", NULL, NULL, "nan"},
  {"log10", "-nan", NULL, NULL, "-nan"},
  /* results next to a midpoint: the exact value of each is within
     0.033 unit in the last place of the middle of two values. A
     directed search found them as the results the furthest from
     their exact value, before the constants of the sine, of ten to
     the x and of the logarithm were centred on their truncations:
     the nearest value is now returned, but by the tangent, 0.518
     unit off, still its furthest known. */
  {"sin", "20.000002326099886", NULL, NULL, "0.34202018147540508"},
  {"cos", "69.99985387402882", NULL, NULL, "0.3420225398971834"},
  {"tan", "88.56894477291725", NULL, NULL, "40.029108327406578"},
  {"exp10", "1.5987025164455447", NULL, NULL, "39.69195738858039"},
  {"log10", "1.0000092103453737", NULL, NULL, "3.9999837516334096e-6"},
};

static da apply(const char *op, da x, da y, da z) {
  switch (op[0]) {
  case '+': return da_add(x, y);
  case '*': return da_mult(x, y);
  case '/': return da_div(x, y);
  case 'f': return da_fma(x, y, z);
  case 'c': return da_cos(x);
  case 'd': return da_degrees_of_radians(x);
  case 'e': return da_exp10(x);
  case 'l': return da_log10(x);
  case 'n': return da_neg(x);
  case 'p': return da_pred(x);
  case 't': return da_tan(x);
  default: return op[1] == 'q' ? da_sqrt(x) : op[1] == 'i' ? da_sin(x)
                                                           : da_succ(x);
  }
}

static void test_cases(void) {
  char what[200];
  for (unsigned i = 0; i < sizeof cases / sizeof *cases; i++) {
    const char *y = cases[i].y ? cases[i].y : "";
    const char *z = cases[i].z ? cases[i].z : "";
    snprintf(what, sizeof what, "%s %s %s %s", cases[i].op, cases[i].x,
             y, z);
    da x = val(cases[i].x), want = val(cases[i].want);
    expect(what, apply(cases[i].op, x, val(y), val(z)), want);
    /* da_sincos must return the same sine and the same cosine */
    if (!strcmp(cases[i].op, "sin")) expect(what, da_sincos(x).sin, want);
    if (!strcmp(cases[i].op, "cos")) expect(what, da_sincos(x).cos, want);
  }
}

/* ---- quantize ---- */

/* the modes, short */
#define EVEN DA_TIES_TO_EVEN
#define TAWAY DA_TIES_TO_AWAY
#define ZERO DA_TOWARD_ZERO
#define POS DA_TOWARD_POSITIVE
#define NEG DA_TOWARD_NEGATIVE
#define AWAY DA_AWAY_FROM_ZERO

static const struct {
  const char *x; int e, mode; const char *want;
} quantized[] = {
  {"2.5", 0, EVEN, "2"},
  {"3.5", 0, EVEN, "4"},
  {"-2.5", 0, EVEN, "-2"},
  {"1.005", -2, EVEN, "1"},
  {"1.015", -2, EVEN, "1.02"},
  {"123.456", -2, EVEN, "123.46"},
  {"123.456", 2, EVEN, "100"},
  {"0.4", 0, EVEN, "0"},
  {"-0.5", 0, EVEN, "-0"},
  {"0.5", 0, EVEN, "0"},
  {"1.5", 0, EVEN, "2"},
  {"1e20", -2, EVEN, "1e20"},
  {"1e20", -200, EVEN, "1e20"},
  {"inf", 0, EVEN, "inf"},
  {"-inf", 3, EVEN, "-inf"},
  {"nan", 5, EVEN, "nan"},
  {"40031996687737742e112", 130, EVEN, "0"},
  {"40031996687737742e112", 120, EVEN, "inf"},
  {"40031996687737742e112", 112, EVEN, "40031996687737742e112"},
  {"40031996687737742e112", 113, EVEN, "40031996687737740e112"},
  {"1e-142", -142, EVEN, "1e-142"},
  {"1e-142", -141, EVEN, "0"},
  {"5e-142", -141, EVEN, "0"},
  {"15e-142", -141, EVEN, "2e-141"},
  {"4003199668773775", 1, EVEN, "4003199668773780"},
  {"4003199668773775", 0, EVEN, "4003199668773775"},
  {"2.5", 0, TAWAY, "3"},
  {"-2.5", 0, TAWAY, "-3"},
  {"2.4", 0, TAWAY, "2"},
  {"-0.5", 0, TAWAY, "-1"},
  {"1.005", -2, TAWAY, "1.01"},
  {"2.9", 0, ZERO, "2"},
  {"-2.9", 0, ZERO, "-2"},
  {"-0.5", 0, ZERO, "-0"},
  {"2.1", 0, POS, "3"},
  {"-2.9", 0, POS, "-2"},
  {"-0.5", 0, POS, "-0"},
  {"0.5", 0, POS, "1"},
  {"1e-142", -141, POS, "1e-141"},
  {"2.9", 0, NEG, "2"},
  {"-2.1", 0, NEG, "-3"},
  {"0.5", 0, NEG, "0"},
  {"2.1", 0, AWAY, "3"},
  {"-2.1", 0, AWAY, "-3"},
  {"2", 0, AWAY, "2"},
  {"0", 5, AWAY, "0"},
  {"-0", 5, POS, "-0"},
  {"1e-100", 3, AWAY, "1000"},
  {"-1e-100", 128, AWAY, "-1e128"},
  {"1e-100", 129, AWAY, "inf"},
  {"-1e-100", 30000, AWAY, "-inf"},
  {"1e-100", 3, POS, "1000"},
  {"1e-100", 3, NEG, "0"},
  {"-1e-100", 3, NEG, "-1000"},
  {"40031996687737742e112", 113, POS, "inf"},
  {"40031996687737742e112", 113, NEG, "40031996687737740e112"},
  {"-40031996687737742e112", 113, ZERO, "-40031996687737740e112"},
  {"-40031996687737742e112", 113, AWAY, "-inf"},
  {"40031996687737742", 1, POS, "40031996687737750"},
  {"4003199668773775", 1, NEG, "4003199668773770"},
  {"4003199668773775e-141", -140, NEG, "4003199668773770e-141"},
  {"4003199668773775e-142", -141, NEG, "4003199668773770e-142"},
};

static void test_quantize(void) {
  char what[100];
  for (unsigned i = 0; i < sizeof quantized / sizeof *quantized; i++) {
    snprintf(what, sizeof what, "quantize %s %d mode %d", quantized[i].x,
             quantized[i].e, quantized[i].mode);
    expect(what, da_quantize(val(quantized[i].x), quantized[i].e,
                             quantized[i].mode),
           val(quantized[i].want));
  }
}

/* ---- mult_integer: x * y * 10^z, with the inexact flag of each case: the
   product by an integer, the signs of zero, y being a positive zero when
   0, the special values, ties inside a decade and at its top, the
   conversions between radians and degrees, the ends of y, overflow,
   subnormal results and underflow ---- */

static const struct {
  const char *x; int64_t y; int z; const char *want; int inexact;
} multiplied[] = {
  {"1", 3, 0, "3", 0}, {"0.1", 3, 0, "0.3", 0},
  {"-1.5", 7, 2, "-1050", 0}, {"1.5", -7, -2, "-0.105", 0},
  {"-1.5", -7, 0, "10.5", 0},
  {"0", -5, 0, "-0", 0}, {"-0", -5, 0, "0", 0}, {"-0", 5, 3, "-0", 0},
  {"-3", 0, 0, "-0", 0}, {"3", 0, 5, "0", 0}, {"0", 0, 0, "0", 0},
  {"inf", -2, 0, "-inf", 0}, {"-inf", INT64_MIN, -30000, "inf", 0},
  {"inf", 0, 0, "nan", 0}, {"-inf", 0, 7, "nan", 0},
  {"nan", 0, 0, "nan", 0},
  {"20015998343868871", 5, 0, "100079991719344360", 1},
  {"20015998343868873", 5, 0, "100079991719344360", 1},
  {"20015998343868873", 2, 0, "40031996687737742", 1},
  {"20015998343868871", 2, 0, "40031996687737742", 0},
  {"3.1415926535897932", 5729577951308232088, -17, "180", 1},
  {"0.5235987755982989", 5729577951308232088, -17,
   "30.000000000000002", 1},
  {"180", 1745329251994329577, -20, "3.1415926535897932", 1},
  {"90", 1745329251994329577, -20, "1.5707963267948966", 1},
  {"1", INT64_MIN, 0, "-9223372036854776000", 1},
  {"1e-142", INT64_MAX, 0, "9223372036854776e-139", 1},
  {"40031996687737742", INT64_MIN, 0, "-36922999882914330e19", 1},
  {"1e128", 4, 0, "4e128", 0}, {"1e128", 5, 0, "inf", 1},
  {"1", 40031996687737746, 112, "40031996687737742e112", 1},
  {"1", 40031996687737747, 112, "inf", 1},
  {"-1e-142", 1, 30000, "-inf", 1},
  {"1e-10", 1, -132, "1e-142", 0}, {"1e-10", 1, -133, "0", 1},
  {"7", 1, -142, "7e-142", 0}, {"7", -1, -143, "-1e-142", 1},
  {"1e-142", 5, -1, "0", 1}, {"1e-142", 6, -1, "1e-142", 1},
  {"1e-142", 15, -1, "2e-142", 1},
  {"4003199668773775e-142", 9, -1, "3602879701896398e-142", 1},
  {"1e-142", 123456789012345678, -17, "1e-142", 1},
  {"1e128", -1, -30000, "-0", 1},
};

static void test_mult_integer(void) {
  char what[100];
  for (unsigned i = 0; i < sizeof multiplied / sizeof *multiplied; i++) {
    snprintf(what, sizeof what, "mult_integer %s %" PRId64 " %d",
             multiplied[i].x, multiplied[i].y, multiplied[i].z);
    expect(what, da_mult_integer(val(multiplied[i].x), multiplied[i].y,
                                 multiplied[i].z),
           val(multiplied[i].want));
  }
}

/* ---- comparisons: -0 equals +0 numerically and precedes it in the total
   order; NaNs are unordered numerically and at the ends of the total order
   ---- */

static const struct { const char *x, *y; int cmp, total; } ordered[] = {
  {"1", "2", -1, -1}, {"2", "1", 1, 1}, {"1", "1", 0, 0},
  {"0", "-0", 0, 1}, {"-0", "0", 0, -1}, {"-1", "-2", 1, 1},
  {"-inf", "inf", -1, -1},
  {"inf", "inf", 0, 0}, {"1e-142", "0", 1, 1}, {"-1e-142", "-0", -1, -1},
  {"nan", "1", DA_UNORDERED, 1}, {"1", "nan", DA_UNORDERED, -1},
  {"nan", "nan", DA_UNORDERED, 0}, {"nan", "inf", DA_UNORDERED, 1},
  {"-nan", "-inf", DA_UNORDERED, -1}, {"-nan", "nan", DA_UNORDERED, -1},
  {"40031996687737742e112", "inf", -1, -1},
};

static void test_ordering(void) {
  char what[100];
  for (unsigned i = 0; i < sizeof ordered / sizeof *ordered; i++) {
    da x = val(ordered[i].x), y = val(ordered[i].y);
    snprintf(what, sizeof what, "compare %s %s", ordered[i].x,
             ordered[i].y);
    expect(what, (da){(uint64_t)da_compare(x, y)},
           (da){(uint64_t)ordered[i].cmp});
    snprintf(what, sizeof what, "total_order %s %s", ordered[i].x,
             ordered[i].y);
    expect(what, (da){(uint64_t)da_total_order(x, y)},
           (da){(uint64_t)ordered[i].total});
  }
  /* NaNs of different payloads: the total order follows the
     representation, reversed on the negative side */
  da a = {NAN_R + 5}, b = {NAN_R + 9};
  expect("total_order nan payloads", (da){(uint64_t)da_total_order(a, b)},
         (da){(uint64_t)-1});
  expect("total_order -nan payloads",
         (da){(uint64_t)da_total_order(da_neg(a), da_neg(b))}, (da){1});
}

/* ---- NaN propagation: the first NaN operand is returned unchanged,
   payload and sign included; an invalid operation on non-NaN operands
   gives DA_NAN ---- */

static void test_nan(void) {
  da a = {NAN_R + 5}, b = {(NAN_R + 9) | SIGN}, one = val("1");
  expect("add nan first", da_add(a, b), a);
  expect("add nan second", da_add(b, a), b);
  expect("add nan with number", da_add(one, b), b);
  expect("mult nan first", da_mult(a, b), a);
  expect("mult nan second", da_mult(b, a), b);
  expect("div nan first", da_div(a, b), a);
  expect("div nan second", da_div(one, b), b);
  expect("sqrt nan", da_sqrt(b), b);
  expect("fma nan x", da_fma(a, one, b), a);
  expect("fma nan y", da_fma(one, a, b), a);
  expect("fma nan z", da_fma(one, one, b), b);
  expect("fma inf*0 before nan z", da_fma(DA_INFINITY, DA_ZERO, b),
         DA_NAN);
  expect("quantize nan", da_quantize(b, 3, AWAY), b);
  expect("mult_integer nan", da_mult_integer(b, -3, 2), b);
  expect("mult_integer nan by 0", da_mult_integer(a, 0, 0), a);
  expect("succ nan", da_succ(b), b);
  expect("neg nan", da_neg(b), (da){b.r ^ SIGN});
}

/* ---- da_snprintf and da_asprintf: the conversions of printf on exact
   decimals, with ties to even, truncation and invalid specifications.
   ---- */

static const struct { const char *spec, *in, *out; } prints[] = {
  {"f", "1", "1.000000"}, {".2f", "0.125", "0.12"},
  {".2f", "0.375", "0.38"},
  {".0f", "0.5", "0"}, {".0f", "1.5", "2"}, {".0f", "2.5", "2"},
  {".0f", "-2.5", "-2"}, {".3f", "-0", "-0.000"}, {"+.1f", "0", "+0.0"},
  {" .1f", "0", " 0.0"}, {"#.0f", "5", "5."}, {".f", "0.5", "0"},
  {"8.2f", "3.14159", "    3.14"}, {"-8.2f|", NULL, NULL},
  {"-8.2f", "3.14159", "3.14    "}, {"08.2f", "-3.14159", "-0003.14"},
  {"-08.2f", "3.14159", "3.14    "}, {"+08.2f", "3.14159", "+0003.14"},
  {".20f", "1e-20", "0.00000000000000000001"},
  {".19f", "5e-20", "0.0000000000000000000"},
  {".19f", "15e-20", "0.0000000000000000002"},
  {"f", "4.0031996687737742E128",
   "400319966877377420000000000000000000000000000000000000000000000000"
   "000000000000000000000000000000000000000000000000000000000000000.00"
   "0000"},
  {".144f", "1E-142",
   "0.0000000000000000000000000000000000000000000000000000000000000000"
   "000000000000000000000000000000000000000000000000000000000000000000"
   "00000000000100"},
  {"e", "0", "0.000000e+00"}, {"E", "-0", "-0.000000E+00"},
  {"e", "1", "1.000000e+00"}, {".2e", "1.125", "1.12e+00"},
  {".2e", "1.135", "1.14e+00"}, {".2e", "9.995", "1.00e+01"},
  {".0e", "5", "5e+00"}, {"#.0e", "5", "5.e+00"},
  {".0e", "-9.5", "-1e+01"},
  {"e", "1E-142", "1.000000e-142"}, {".3E", "4.0031996687737742E128",
   "4.003E+128"}, {"12.3e", "123456", "   1.235e+05"},
  {"012.3e", "-123456", "-001.235e+05"}, {".16e", "40031996687737742E-7",
   "4.0031996687737742e+09"}, {".15e", "40031996687737742E-7",
   "4.003199668773774e+09"}, {".15e", "40031996687737745E-7",
   "4.003199668773774e+09"}, {".15e", "40031996687737755E-7",
   "4.003199668773776e+09"},
  {"g", "0", "0"}, {"#g", "0", "0.00000"}, {"g", "-0", "-0"},
  {"g", "1", "1"}, {"#g", "1", "1.00000"}, {"g", "100000", "100000"},
  {"g", "1000000", "1e+06"}, {"g", "999999.5", "1e+06"},
  {"g", "999999.4", "999999"}, {"g", "0.0001", "0.0001"},
  {"g", "0.00001", "1e-05"}, {"g", "0.000123456789", "0.000123457"},
  {"g", "1234567", "1.23457e+06"}, {"G", "1234567", "1.23457E+06"},
  {".3g", "9.995", "10"}, {".3g", "9.985", "9.98"},
  {".3g", "9.9851", "9.99"},
  {".0g", "123", "1e+02"}, {".1g", "0.000099", "0.0001"},
  {".1g", "0.00009", "9e-05"}, {"#.3g", "1.5", "1.50"},
  {".3g", "1.5", "1.5"},
  {".17g", "4.0031996687737742E128", "4.0031996687737742e+128"},
  {".20g", "4.0031996687737742E128", "4.0031996687737742e+128"},
  {"#.20g", "4.0031996687737742E128", "4.0031996687737742000e+128"},
  {"g", "1E-142", "1e-142"}, {"10g", "1E-142", "    1e-142"},
  {"-10g", "-1E-142", "-1e-142   "}, {"010g", "-1E-142", "-0001e-142"},
  {"f", "inf", "inf"}, {"F", "-inf", "-INF"}, {"+e", "inf", "+inf"},
  {" g", "inf", " inf"}, {"06f", "inf", "   inf"},
  {"-6G", "-inf", "-INF  "},
  {"f", "nan", "nan"}, {"E", "-nan", "-NAN"}, {"+g", "nan", "+nan"},
  {"#08.3g", "nan", "     nan"},
  /* precisions of g without # beyond 129, and outputs beyond INT_MAX */
  {".999999999999999999999999999999999999999999999999999999999999999g",
   "1", "1"},
  {".999999999999g", "1E128",
   "1000000000000000000000000000000000000000000000000000000000000000"
   "0000000000000000000000000000000000000000000000000000000000000000"
   "0"},
  {".999999999999g", "1.5E-5", "1.5e-05"},
  /* from a precision of 142 on, only zeros are appended */
  {".145f", "1E-142",
   "0.00000000000000000000000000000000000000000000000000000000000000"
   "0000000000000000000000000000000000000000000000000000000000000000"
   "0000000000000001000"},
  {"#.140g", "1E128",
   "1000000000000000000000000000000000000000000000000000000000000000"
   "0000000000000000000000000000000000000000000000000000000000000000"
   "0.00000000000"},
  {"#.999999999999g", "1", NULL}, {".2147483642e", "1", NULL},
  {".2147483646f", "0", NULL}, {"2147483648f", "1", NULL},
  {"99999999999999999999f", "1", NULL},
  /* not a specification */
  {"", "1", NULL}, {"%f", "1", NULL}, {"f ", "1", NULL}, {"5", "1", NULL},
  {"*f", "1", NULL}, {"lf", "1", NULL}, {"a", "1", NULL}, {"d", "1", NULL},
};

static void test_printing(void) {
  for (size_t i = 0; i < sizeof prints / sizeof *prints; i++) {
    const char *spec = prints[i].spec, *in = prints[i].in,
      *out = prints[i].out;
    if (!in) continue;
    da d = strtoda(in, NULL);
    char buf[256];
    if (out && (d.r & ~SIGN) < INF) { // .17G is da_to_string when finite
      char s[DA_STRING_SIZE];
      da_to_string(s, d);
      da_snprintf(buf, sizeof buf, ".17G", d);
      checks++;
      if (strcmp(s, buf)) {
        failures++;
        printf("FAIL to_string \"%s\" differs from .17G \"%s\"\n", s, buf);
      }
    }
    int n = da_snprintf(buf, sizeof buf, spec, d);
    char *s = NULL;
    int m = da_asprintf(&s, spec, d);
    checks++;
    if (!out ? n == -1 && m == -1
        : n == (int)strlen(out) && !strcmp(buf, out) && m == n
          && !strcmp(s, out)) {
      free(s);
      continue;
    }
    failures++;
    printf("FAIL \"%s\" of %s: want %s, snprintf %d \"%s\", asprintf %d "
           "\"%s\"\n", spec, in, out ? out : "an error", n, buf, m,
           m < 0 ? "" : s);
    free(s);
  }
  /* truncation: the length of the whole output is returned, size - 1
     characters are stored and terminated, and a size of 0 stores
     nothing */
  da pi = strtoda("3.14159", NULL);
  char buf[8] = "XXXXXXX";
  int n = da_snprintf(buf, 4, ".3f", pi);
  checks++;
  if (n != 5 || strcmp(buf, "3.1") || buf[4] != 'X') {
    failures++;
    printf("FAIL truncation to 4: %d \"%s\"\n", n, buf);
  }
  n = da_snprintf(buf, 0, ".3f", pi);
  checks++;
  if (n != 5 || buf[0] != '3') {
    failures++;
    printf("FAIL size 0: %d \"%s\"\n", n, buf);
  }
  n = da_snprintf(NULL, 0, "12.3e", pi);
  checks++;
  if (n != 12) {
    failures++;
    printf("FAIL NULL, 0: %d\n", n);
  }
  /* errors set errno and write nothing */
  strcpy(buf, "XXXXXXX");
  errno = 0;
  n = da_snprintf(buf, sizeof buf, "2147483648f", pi);
  checks++;
  if (n != -1 || errno != EOVERFLOW || strcmp(buf, "XXXXXXX")) {
    failures++;
    printf("FAIL too long: %d, errno %d, \"%s\"\n", n, errno, buf);
  }
  errno = 0;
  n = da_snprintf(buf, sizeof buf, "d", pi);
  checks++;
  if (n != -1 || errno != EINVAL || strcmp(buf, "XXXXXXX")) {
    failures++;
    printf("FAIL invalid: %d, errno %d, \"%s\"\n", n, errno, buf);
  }
}

/* ---- da_to_string: the canonical text of a value, its length, its bound,
   and its round trip through strtoda. ---- */

static const struct { const char *in, *out; } strings[] = {
  {"0", "0"}, {"-0", "-0"}, {"1", "1"}, {"-1", "-1"}, {"0.1", "0.1"},
  {"1000", "1000"}, {"1e16", "10000000000000000"}, {"1e17", "1E+17"},
  {"12345678901234567", "12345678901234567"},
  {"123456789012345678", "1.2345678901234568E+17"},
  {"123.456", "123.456"}, {"1234567.5", "1234567.5"}, {"0.0001", "0.0001"},
  {"0.000123", "0.000123"}, {"0.00001", "1E-05"}, {"2.5e-5", "2.5E-05"},
  {"1.5e20", "1.5E+20"}, {"1e100", "1E+100"}, {"1e-100", "1E-100"},
  {"1e-142", "1E-142"}, {"-1e-142", "-1E-142"},
  // the largest subnormal, and a rounding to the subnormal step of 1E-142
  {"4.003199668773774E-127", "4.003199668773774E-127"},
  {"4.0031996687737742E-142", "4E-142"},
  {"4.0031996687737742E128", "4.0031996687737742E+128"},
  /* the longest outputs: 24 and 23 characters */
  {"-4.0031996687737742E128", "-4.0031996687737742E+128"},
  {"-4.0031996687737742E-4", "-0.00040031996687737742"},
  {"inf", "inf"}, {"-inf", "-inf"}, {"nan", "NaN"}, {"-nan", "-NaN"},
};

static void test_to_string(void) {
  for (size_t i = 0; i < sizeof strings / sizeof *strings; i++) {
    const char *in = strings[i].in, *out = strings[i].out;
    da d = strtoda(in, NULL);
    char buf[DA_STRING_SIZE];
    int n = da_to_string(buf, d);
    char *end;
    da back = strtoda(buf, &end);
    checks++;
    if (!strcmp(buf, out) && n == (int)strlen(out) && n < DA_STRING_SIZE
        && back.r == d.r && !*end)
      continue;
    failures++;
    printf("FAIL to_string of %s: want %s, got %d \"%s\"\n", in, out, n,
           buf);
  }
}

/* With an argument, the lines that make check compares with cmp: the value
   of each of the strings above by da_print, or the text it should be. */
/* ---- the inexact flag: raised on every rounded result and on no other
   when the library was built with DA_INEXACT, in dec-alpha.c, and
   DA_INEXACT_PRINTF, in da_printing.c, and never touched otherwise. A
   probe of each file tells which build this is. ---- */

static const struct {
  const char *op, *x, *y, *z; int inexact;
} flagged[] = {
  {"/", "1", "3", NULL, 1}, {"/", "1", "10", NULL, 0},
  {"/", "inf", "3", NULL, 0}, {"/", "1", "0", NULL, 0},
  {"/", "1e-142", "10", NULL, 1},
  {"+", "1", "3", NULL, 0}, {"+", "nan", "3", NULL, 0},
  {"+", "1", "1e-17", NULL, 1}, {"+", "1", "-1e-18", NULL, 1},
  {"+", "1e128", "0", NULL, 0}, {"+", "1e128", "-1", NULL, 1},
  {"+", "40031996687737742e112", "5e112", NULL, 1},
  {"*", "1e128", "1e128", NULL, 1}, {"*", "1e-142", "1e-142", NULL, 1},
  {"*", "1e-142", "1", NULL, 0}, {"*", "1e-142", "0.1", NULL, 1},
  {"*", "20015998343868871", "2", NULL, 0},
  {"*", "20015998343868873", "2", NULL, 1},
  {"*", "7", "1.1111111111111111", NULL, 1},
  {"sqrt", "4", NULL, NULL, 0}, {"sqrt", "2", NULL, NULL, 1},
  {"sqrt", "0.04", NULL, NULL, 0}, {"sqrt", "0.4", NULL, NULL, 1},
  {"sqrt", "-1", NULL, NULL, 0}, {"sqrt", "inf", NULL, NULL, 0},
  {"fma", "1", "3", "1", 0}, {"fma", "0.1", "0.1", "1e128", 1},
  {"fma", "7", "1.1111111111111111", "inf", 0},
  {"neg", "0.1", NULL, NULL, 0}, {"succ", "1", NULL, NULL, 0},
  {"pred", "1", NULL, NULL, 0},
  {"sin", "0", NULL, NULL, 0}, {"sin", "30", NULL, NULL, 0},
  {"cos", "60", NULL, NULL, 0}, {"cos", "30", NULL, NULL, 1},
  {"cos", "90", NULL, NULL, 0}, {"sin", "1e-142", NULL, NULL, 1},
  {"cos", "1e-142", NULL, NULL, 1},
  {"tan", "0", NULL, NULL, 0}, {"tan", "45", NULL, NULL, 0},
  {"tan", "-135", NULL, NULL, 0}, {"tan", "90", NULL, NULL, 0},
  {"tan", "180", NULL, NULL, 0}, {"tan", "30", NULL, NULL, 1},
  {"tan", "44", NULL, NULL, 1}, {"tan", "1e-142", NULL, NULL, 1},
  {"exp10", "0", NULL, NULL, 0}, {"exp10", "-142", NULL, NULL, 0},
  {"exp10", "128", NULL, NULL, 0}, {"exp10", "0.5", NULL, NULL, 1},
  {"exp10", "1e-30", NULL, NULL, 1}, {"exp10", "-143", NULL, NULL, 1},
  {"exp10", "129", NULL, NULL, 1}, {"exp10", "inf", NULL, NULL, 0},
  {"exp10", "-inf", NULL, NULL, 0}, {"exp10", "nan", NULL, NULL, 0},
  {"log10", "1", NULL, NULL, 0}, {"log10", "1e-142", NULL, NULL, 0},
  {"log10", "1000", NULL, NULL, 0}, {"log10", "2", NULL, NULL, 1},
  {"log10", "0", NULL, NULL, 0}, {"log10", "-1", NULL, NULL, 0},
  {"log10", "inf", NULL, NULL, 0},
  {"degrees", "0", NULL, NULL, 0}, {"degrees", "-inf", NULL, NULL, 0},
  {"degrees", "nan", NULL, NULL, 0}, {"degrees", "1", NULL, NULL, 1},
  {"degrees", "3.1415926535897932", NULL, NULL, 1},
  {"degrees", "1e-142", NULL, NULL, 1},
  {"degrees", "1e128", NULL, NULL, 1},
};

static const struct {
  const char *x; int e, mode, inexact;
} flagged_q[] = {
  {"0.333", -2, EVEN, 1}, {"1.25", -2, EVEN, 0}, {"1.25", 2, EVEN, 1},
  {"0", 2, EVEN, 0}, {"-1.5", 0, EVEN, 1}, {"1e128", 130, EVEN, 1},
  {"4e128", 128, EVEN, 0}, {"inf", 0, EVEN, 0}, {"0.333", -2, ZERO, 1},
  {"1.25", -2, AWAY, 0}, {"1e-100", 3, AWAY, 1}, {"0", 3, AWAY, 0},
  {"4e128", 127, POS, 0}, {"4e128", 128, AWAY, 0}, {"1e128", 129, NEG, 1},
};

static const struct { const char *in; int inexact; } flagged_n[] = {
  {"0.1", 0}, {"0.12345678901234567890", 1}, {"40031996687737745", 1},
  {"40031996687737742", 0}, {"40031996687737750", 0}, {"1e-200", 1},
  {"1e999999999999", 1}, {"1e-999999999999", 1}, {"-0e5", 0},
  {"nan", 0}, {"12345678901234567890123", 1},
  {"1000000000000000000000", 0},
};

static const struct { const char *spec, *in; int inexact; } flagged_p[] = {
  {".2f", "0.125", 1}, {".3f", "0.125", 0}, {".0f", "2.5", 1},
  {".0f", "2", 0}, {".2e", "1.23e5", 0}, {".1e", "1.23e5", 1},
  {"g", "0.1", 0}, {"g", "1234567", 1}, {".0f", "1e-142", 1},
  {"f", "inf", 0}, {"#.0f", "5", 0}, {".0e", "9.9e127", 1},
  {".17g", "0.1", 0}, {"e", "nan", 0},
};

static void expect_flag(const char *what, int want) {
  checks++;
  if (da_inexact == want) return;
  failures++;
  printf("FAIL %s: inexact flag %d, want %d\n", what, da_inexact, want);
}

static void test_inexact(void) {
  char what[200], buf[32];
  da_inexact = 0;
  da_div(val("1"), val("3"));
  int arith = da_inexact;
  da_inexact = 0;
  da_snprintf(buf, sizeof buf, ".0f", val("0.5"));
  int print = da_inexact;
  printf("inexact flag %s in dec-alpha.c, %s in da_printing.c\n",
         arith ? "on" : "off", print ? "on" : "off");
  for (size_t i = 0; i < sizeof flagged / sizeof *flagged; i++) {
    const char *y = flagged[i].y ? flagged[i].y : "";
    const char *z = flagged[i].z ? flagged[i].z : "";
    da dx = val(flagged[i].x), dy = val(y), dz = val(z);
    snprintf(what, sizeof what, "%s %s %s %s", flagged[i].op,
             flagged[i].x, y, z);
    da_inexact = 0;
    apply(flagged[i].op, dx, dy, dz);
    expect_flag(what, arith && flagged[i].inexact);
  }
  for (size_t i = 0; i < sizeof flagged_q / sizeof *flagged_q; i++) {
    da x = val(flagged_q[i].x);
    snprintf(what, sizeof what, "quantize %s %d mode %d", flagged_q[i].x,
             flagged_q[i].e, flagged_q[i].mode);
    da_inexact = 0;
    da_quantize(x, flagged_q[i].e, flagged_q[i].mode);
    expect_flag(what, arith && flagged_q[i].inexact);
  }
  for (size_t i = 0; i < sizeof multiplied / sizeof *multiplied; i++) {
    da x = val(multiplied[i].x);
    snprintf(what, sizeof what, "mult_integer %s %" PRId64 " %d",
             multiplied[i].x, multiplied[i].y, multiplied[i].z);
    da_inexact = 0;
    da_mult_integer(x, multiplied[i].y, multiplied[i].z);
    expect_flag(what, arith && multiplied[i].inexact);
  }
  for (size_t i = 0; i < sizeof flagged_n / sizeof *flagged_n; i++) {
    da_inexact = 0;
    strtoda(flagged_n[i].in, NULL);
    expect_flag(flagged_n[i].in, arith && flagged_n[i].inexact);
  }
  for (size_t i = 0; i < sizeof flagged_p / sizeof *flagged_p; i++) {
    da x = val(flagged_p[i].in);
    snprintf(what, sizeof what, "%s of %s", flagged_p[i].spec,
             flagged_p[i].in);
    da_inexact = 0;
    da_snprintf(buf, sizeof buf, flagged_p[i].spec, x);
    expect_flag(what, print && flagged_p[i].inexact);
  }
}

static int print_strings(const char *what) {
  int print = !strcmp(what, "print");
  if (!print && strcmp(what, "strings")) {
    fputs("usage: test-fixed [print | strings]\n", stderr);
    return 2;
  }
  for (size_t i = 0; i < sizeof strings / sizeof *strings; i++) {
    if (print)
      da_print(strtoda(strings[i].in, NULL));
    else
      fputs(strings[i].out, stdout);
    putchar('\n');
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc > 1) return print_strings(argv[1]);
  if (INF != DA_INFINITY.r || NAN_R != DA_NAN.r) {
    puts("constants out of sync with dec-alpha.h");
    return 1;
  }
  test_numerals();
  test_cases();
  test_quantize();
  test_mult_integer();
  test_ordering();
  test_nan();
  test_printing();
  test_to_string();
  test_inexact();
  printf("fixed: %ld checks, %ld failures\n", checks, failures);
  return failures != 0;
}

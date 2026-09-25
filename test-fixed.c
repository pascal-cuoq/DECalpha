/* Fixed tests of dec-alpha.c: documented behaviors and hand-checked cases,
   with expected results written down rather than computed. They need
   neither a seed nor GMP; the random tests are in test-random.c.

   Build: cc -std=c11 test-fixed.c dec-alpha.o */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
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

static const struct { const char *in; uint64_t m; int e, end; } numerals[] = {
  {"", 0, -1, 0}, {".", 0, -1, 0}, {"-", 0, -1, 0}, {"e5", 0, -1, 0},
  {"+.e5", 0, -1, 0}, {" \t\n-0", SIGN, -1, 5}, {"1e", 1, BIAS, 1},
  {"1e+", 1, BIAS, 1}, {"1.e-x", 1, BIAS, 2}, {"5.", 5, BIAS, 2},
  {".5", 5, BIAS - 1, 2}, {"inf", INF, -1, 3}, {"-INFINITY", INF | SIGN, -1, 9},
  {"infinit", INF, -1, 3}, {"nan", NAN_R, -1, 3},
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
  {"9876543219876543499999999999999", UINT64_C(9876543219876543), BIAS + 15,
   31},
  /* 16 digits followed by an exact tie, rounded to the even 9876543219876544 */
  {"98765432198765435000000000000000000", UINT64_C(9876543219876544),
   BIAS + 19, 35},
  /* between DECADE_HI and the next decade, below the midpoint 4003...746:
     down to DECADE_HI */
  {"40031996687737745999999999999", DA_DECADE_HI, BIAS + 12, 29},
  /* exactly on that midpoint: to DECADE_HI, the even one */
  {"400319966877377460000000", DA_DECADE_HI, BIAS + 7, 24},
  /* just above it: up to DECADE_LO of the next decade */
  {"4003199668773774600000000000000001", DA_DECADE_LO, BIAS + 18, 34},
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
      printf("FAIL strtoda endptr on \"%s\": consumed %d\n", numerals[i].in,
             (int)(end - numerals[i].in));
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
  {"fma", "1.0000000000000001", "1.0000000000000001", "-1", "2.0000000000000001e-16"},
  {"fma", "inf", "0", "1", "nan"},
  {"fma", "inf", "1", "-inf", "nan"},
  {"fma", "1", "1", "nan", "nan"},
  {"fma", "40031996687737742e112", "1", "4e112", "40031996687737742e112"},
  {"fma", "40031996687737742e112", "1", "5e112", "inf"},
  {"fma", "1e-142", "0.5", "0", "0"},
  {"fma", "1e-142", "0.5", "1e-142", "2e-142"},
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
};

static da apply(const char *op, da x, da y, da z) {
  switch (op[0]) {
  case '+': return da_add(x, y);
  case '*': return da_mult(x, y);
  case '/': return da_div(x, y);
  case 'f': return da_fma(x, y, z);
  case 'n': return da_neg(x);
  case 'p': return da_pred(x);
  default: return op[1] == 'q' ? da_sqrt(x) : da_succ(x);
  }
}

static void test_cases(void) {
  char what[200];
  for (unsigned i = 0; i < sizeof cases / sizeof *cases; i++) {
    const char *y = cases[i].y ? cases[i].y : "", *z = cases[i].z ? cases[i].z : "";
    snprintf(what, sizeof what, "%s %s %s %s", cases[i].op, cases[i].x, y, z);
    expect(what, apply(cases[i].op, val(cases[i].x), val(y), val(z)),
           val(cases[i].want));
  }
}

/* ---- quantize ---- */

static const struct { const char *x; int e; const char *want; } quantized[] = {
  {"2.5", 0, "2"},
  {"3.5", 0, "4"},
  {"-2.5", 0, "-2"},
  {"1.005", -2, "1"},
  {"1.015", -2, "1.02"},
  {"123.456", -2, "123.46"},
  {"123.456", 2, "100"},
  {"0.4", 0, "0"},
  {"-0.5", 0, "-0"},
  {"0.5", 0, "0"},
  {"1.5", 0, "2"},
  {"1e20", -2, "1e20"},
  {"1e20", -200, "1e20"},
  {"inf", 0, "inf"},
  {"-inf", 3, "-inf"},
  {"nan", 5, "nan"},
  {"40031996687737742e112", 130, "0"},
  {"40031996687737742e112", 120, "inf"},
  {"40031996687737742e112", 112, "40031996687737742e112"},
  {"40031996687737742e112", 113, "40031996687737740e112"},
  {"1e-142", -142, "1e-142"},
  {"1e-142", -141, "0"},
  {"5e-142", -141, "0"},
  {"15e-142", -141, "2e-141"},
  {"4003199668773775", 1, "4003199668773780"},
  {"4003199668773775", 0, "4003199668773775"},
};

static void test_quantize(void) {
  char what[100];
  for (unsigned i = 0; i < sizeof quantized / sizeof *quantized; i++) {
    snprintf(what, sizeof what, "quantize %s %d", quantized[i].x, quantized[i].e);
    expect(what, da_quantize(val(quantized[i].x), quantized[i].e),
           val(quantized[i].want));
  }
}

/* ---- comparisons: -0 equals +0 numerically and precedes it in the total
   order; NaNs are unordered numerically and at the ends of the total order
   ---- */

static const struct { const char *x, *y; int cmp, total; } ordered[] = {
  {"1", "2", -1, -1}, {"2", "1", 1, 1}, {"1", "1", 0, 0}, {"0", "-0", 0, 1},
  {"-0", "0", 0, -1}, {"-1", "-2", 1, 1}, {"-inf", "inf", -1, -1},
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
    snprintf(what, sizeof what, "compare %s %s", ordered[i].x, ordered[i].y);
    expect(what, (da){(uint64_t)da_compare(x, y)}, (da){(uint64_t)ordered[i].cmp});
    snprintf(what, sizeof what, "total_order %s %s", ordered[i].x, ordered[i].y);
    expect(what, (da){(uint64_t)da_total_order(x, y)},
           (da){(uint64_t)ordered[i].total});
  }
  /* NaNs of different payloads: the total order follows the representation,
     reversed on the negative side */
  da a = {NAN_R + 5}, b = {NAN_R + 9};
  expect("total_order nan payloads", (da){(uint64_t)da_total_order(a, b)},
         (da){(uint64_t)-1});
  expect("total_order -nan payloads",
         (da){(uint64_t)da_total_order(da_neg(a), da_neg(b))}, (da){1});
}

/* ---- NaN propagation: the first NaN operand is returned unchanged, payload
   and sign included; an invalid operation on non-NaN operands gives DA_NAN
   ---- */

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
  expect("fma inf*0 before nan z", da_fma(DA_INFINITY, DA_ZERO, b), DA_NAN);
  expect("quantize nan", da_quantize(b, 3), b);
  expect("succ nan", da_succ(b), b);
  expect("neg nan", da_neg(b), (da){b.r ^ SIGN});
}

int main(void) {
  if (INF != DA_INFINITY.r || NAN_R != DA_NAN.r) {
    puts("constants out of sync with dec-alpha.h");
    return 1;
  }
  test_numerals();
  test_cases();
  test_quantize();
  test_ordering();
  test_nan();
  printf("fixed: %ld checks, %ld failures\n", checks, failures);
  return failures != 0;
}

#include <stdio.h>
#include <stdlib.h>
#include "dec-alpha.h"

static int by_total_order(const void *a, const void *b) {
  return da_total_order(*(const da *)a, *(const da *)b);
}

int main(void)
{
  da_print((da){0});puts("");
  da_print((da){1});puts("");
  da_print((da){2});puts("");
  puts("...");
  da_print((da){DA_DECADE_LO-2});puts("");
  da_print((da){DA_DECADE_LO-1});puts("");
  da_print((da){DA_DECADE_LO});puts("");
  da_print((da){DA_DECADE_LO+1});puts("");
  da_print((da){DA_DECADE_LO+2});puts("");
  puts("...");
  da_print((da){DA_DECADE_HI-2});puts("");
  da_print((da){DA_DECADE_HI-1});puts("");
  da_print((da){DA_DECADE_HI});puts("");
  da_print((da){DA_DECADE_HI+1});puts("");
  da_print((da){DA_DECADE_HI+2});puts("");
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
  da DA_MAX=da_pred(DA_INFINITY);
  da_print(da_pred(DA_MAX));puts("");
  da_print(DA_MAX);puts(" DA_MAX");
  da_print(DA_INFINITY);puts("");
  da_print((da){DA_INFINITY.r + 1});puts("");
  puts("\nSuccessor and predecessor:");
  da_print(da_succ(DA_ZERO));puts(" (succ(0))");
  da_print(da_succ(da_neg(DA_ZERO)));puts(" (succ(-0))");
  da_print(da_pred(DA_ZERO));puts(" (pred(0))");
  da_print(da_succ(da_neg((da){1})));puts(" (succ(-1E-142))");
  da_print(da_succ(da_neg(one)));puts(" (succ(-1))");
  da_print(da_pred(da_neg(one)));puts(" (pred(-1))");
  da_print(da_succ(DA_MAX));puts(" (succ(DA_MAX))");
  da_print(da_succ(DA_INFINITY));puts(" (succ(inf))");
  da_print(da_pred(da_neg(DA_INFINITY)));puts(" (pred(-inf))");
  da_print(da_succ(da_neg(DA_INFINITY)));puts(" (succ(-inf))");
  da_print(da_pred(da_neg(DA_MAX)));puts(" (pred(-DA_MAX))");
  da_print(da_succ(DA_NAN));puts(" (succ(NaN))");
  puts("\nCountdown:");
  da x = eleven;
  for (int i = 11; i>0; i--) {
    x = da_add(x, da_neg(one));
    da_print(x);puts("");
  }
  puts("\nMultiplication:");
  x = da_mult(five, eight);
  da_print(x);puts(" (8*5)");
  x = da_mult(eight, eight);
  da_print(x);puts(" (8*8)");
  x = da_mult(five, five);
  da_print(x);puts(" (5*5)");
  da third = da_from_integer_and_biased_exp(333333333333333333,124);
  da_print(da_mult(third, three));puts(" (3*.333...)");
  da ninth = da_mult(third, third);
  da_print(ninth);puts(" (.333...*.333...)");
  da_print(da_mult(ninth, eleven));puts(" (11*.111...)");
  puts("\nMultiplication of subnormal operand:");
  da_print(da_mult((da){1}, DA_MAX));puts(" (1E-142*DA_MAX)");
  da_print(da_mult((da){9}, DA_MAX));puts(" (9E-142*DA_MAX)");
  da_print(da_mult((da){987654321}, DA_MAX));
  puts(" (987654321E-142*DA_MAX)");
  puts("\nSubnormal result of multiplication:");
  da_print(da_mult((da){1001}, da_from_integer(999)));
  puts(" (1001E-142*999)");
  da_print(da_mult(da_from_integer_and_biased_exp(99999, 72),
                   da_from_integer_and_biased_exp(10000001, 72)));
  puts(" (99999E-70*10000001E-70)");
  da_print(da_mult(da_from_integer_and_biased_exp(1234567899999, 72),
                   da_from_integer_and_biased_exp(1001, 72)));
  puts(" (1234567899999E-70*1001E-70)");
  da_print(da_mult(da_from_integer_and_biased_exp(123456, 71),
                   da_from_integer_and_biased_exp(10000001, 62)));
  puts(" (123456E-69*10000001E-60)");
  da_print(da_mult(da_from_integer_and_biased_exp(523456, 70),
                   da_from_integer_and_biased_exp(10000001, 61)));
  puts(" (523456E-68*10000001E-59)");
  da_print(da_mult(da_from_integer_and_biased_exp(423456, 70),
                   da_neg(da_from_integer_and_biased_exp(10000001, 61))));
  puts(" (423456E-68*(-10000001E-59))");
  puts("\nDivision:");
  da_print(da_div(one, three));puts(" (1/3)");
  da_print(da_div(two, three));puts(" (2/3)");
  da_print(da_div(eleven, da_neg(five)));puts(" (11/-5)");
  da_print(da_div(one, da_from_integer(7)));puts(" (1/7)");
  da_print(da_div(da_from_integer(20015998343868873), da_from_integer(5)));
  puts(" (20015998343868873/5, tie at the end of a decade)");
  puts("\nDivision with subnormals:");
  da_print(da_div(one, (da){3}));puts(" (1/3E-142)");
  da_print(da_div((da){3}, one));puts(" (3E-142/1)");
  da_print(da_div((da){1}, three));puts(" (1E-142/3)");
  da_print(da_div((da){2}, three));puts(" (2E-142/3)");
  puts("\nDivision with zero and inf:");
  da_print(da_div(one, DA_ZERO));puts(" (1/0)");
  da_print(da_div(da_neg(DA_ZERO), one));puts(" (-0/1)");
  da_print(da_div(one, da_neg(DA_INFINITY)));puts(" (1/-inf)");
  da_print(da_div(DA_INFINITY, DA_ZERO));puts(" (inf/0)");
  da_print(da_div(DA_ZERO, DA_ZERO));puts(" (0/0)");
  da_print(da_div(DA_INFINITY, DA_INFINITY));puts(" (inf/inf)");
  puts("\nSquare root:");
  da_print(da_sqrt(two));puts(" (sqrt(2))");
  da_print(da_sqrt(eight));puts(" (sqrt(8))");
  da_print(da_sqrt(da_from_integer(9)));puts(" (sqrt(9))");
  da_print(da_sqrt(ninth));puts(" (sqrt(.111...))");
  da_print(da_sqrt(da_from_integer_and_biased_exp(16025607588070461,143)));
  puts(" (sqrt(16025607588070461E1), rounds up to the next decade)");
  da_print(da_sqrt(DA_MAX));puts(" (sqrt(DA_MAX))");
  da_print(da_sqrt((da){1}));puts(" (sqrt(1E-142))");
  da_print(da_sqrt((da){2}));puts(" (sqrt(2E-142))");
  puts("\nSquare root of zero, inf and negative numbers:");
  da_print(da_sqrt(da_neg(DA_ZERO)));puts(" (sqrt(-0))");
  da_print(da_sqrt(DA_INFINITY));puts(" (sqrt(inf))");
  da_print(da_sqrt(da_neg(one)));puts(" (sqrt(-1))");
  da_print(da_sqrt(da_neg(DA_INFINITY)));puts(" (sqrt(-inf))");
  puts("\nParsing with strtoda:");
  const char *numerals[] = {
    "0.1", "123.45E67", "-1e-142", "1e400", "0.99999999999999999",
    "40031996687737746", "4003199668773774600000000000000001", "-INFINITY",
    "nan", "12.5abc", "abc"};
  for (unsigned i = 0; i < sizeof numerals / sizeof *numerals; i++) {
    char *end;
    da d = strtoda(numerals[i], &end);
    printf("%-36s -> ", numerals[i]);
    da_print(d);
    if (*end) printf(" (stopping at \"%s\")", end);
    puts("");
  }
  puts("\nQuantize, to a multiple of a power of ten:");
  da pi = strtoda("3.14159265358979323846", NULL);
  da_print(pi);puts(" (pi, rounded to DEC alpha)");
  da_print(da_quantize(pi, -2));puts(" (pi to hundredths)");
  da_print(da_quantize(pi, 0));puts(" (pi to units)");
  da_print(da_quantize(strtoda("2.5", NULL), 0));
  puts(" (2.5 to units, tie to even)");
  da_print(da_quantize(strtoda("3.5", NULL), 0));
  puts(" (3.5 to units, tie to even)");
  da_print(da_quantize(strtoda("1.005", NULL), -2));
  puts(" (1.005 to hundredths, tie to even)");
  da_print(da_quantize(strtoda("123456.789", NULL), 3));
  puts(" (123456.789 to thousands)");
  da_print(da_quantize(strtoda("-0.4", NULL), 0));puts(" (-0.4 to units)");
  da_print(da_quantize(DA_MAX, -2));
  puts(" (DA_MAX to hundredths, unchanged)");
  puts("\nFused multiply-add:");
  x = strtoda("1.0000000000000001", NULL);
  da_print(da_mult(x, x));puts(" (x*x for x = 1.0000000000000001)");
  da_print(da_add(da_mult(x, x), da_neg(one)));
  puts(" (x*x-1 in two roundings)");
  da_print(da_fma(x, x, da_neg(one)));
  puts(" (x*x-1 fused: the exact value)");
  da_print(da_fma(da_from_integer(20015998343868873), five, DA_ZERO));
  puts(" (20015998343868873*5+0, a tie, to even)");
  da_print(da_fma(da_from_integer(20015998343868873), five, (da){1}));
  puts(" (20015998343868873*5+1E-142, the tie broken upward)");
  da_print(da_fma(DA_INFINITY, DA_ZERO, one));puts(" (inf*0+1)");
  puts("\nComparison:");
  printf("%d (compare(1, 2))\n", da_compare(one, two));
  printf("%d (compare(2, 1))\n", da_compare(two, one));
  printf("%d (compare(0, -0))\n", da_compare(DA_ZERO, da_neg(DA_ZERO)));
  printf("%d (compare(1, NaN), DA_UNORDERED)\n", da_compare(one, DA_NAN));
  printf("%d (total_order(0, -0))\n",
         da_total_order(DA_ZERO, da_neg(DA_ZERO)));
  printf("%d (total_order(inf, NaN))\n",
         da_total_order(DA_INFINITY, DA_NAN));
  printf("%d (total_order(-NaN, -inf))\n",
         da_total_order(da_neg(DA_NAN), da_neg(DA_INFINITY)));
  puts("\nSorting with total_order:");
  da values[] = {three, da_neg(DA_ZERO), DA_NAN, da_neg(DA_INFINITY),
                 DA_ZERO, (da){1}, da_neg(two), DA_MAX, da_neg(DA_NAN),
                 DA_INFINITY};
  qsort(values, sizeof values / sizeof *values, sizeof *values,
        by_total_order);
  for (unsigned i = 0; i < sizeof values / sizeof *values; i++) {
    da_print(values[i]);
    printf("%s", i + 1 < sizeof values / sizeof *values ? " < " : "\n");
  }
}

#ifndef DEC_ALPHA_H
#define DEC_ALPHA_H

#include <stddef.h>
#include <stdint.h>

/* A DEC α value. The representation r is public: the next value after a
   non-negative d is (da){d.r + 1}. */
typedef struct { uint64_t r;} da;

// Decades range from DA_DECADE_LO to DA_DECADE_HI
#define DA_DECADE_LO UINT64_C(4003199668773775)
#define DA_DECADE_HI UINT64_C(40031996687737742)

#define DA_ZERO ((da){0})
#define DA_INFINITY ((da){UINT64_C(0x7f80000000000000) + DA_DECADE_LO})
#define DA_MINUS_INFINITY \
  ((da){UINT64_C(0xff80000000000000) + DA_DECADE_LO})
#define DA_NAN ((da){UINT64_C(0x7f80000000000000) + DA_DECADE_LO + 1})

/* The exact value of d as text, in the style of C's %g with 17 significant
   digits: 0.1, 1000, 1.5E+20, -0, inf, NaN. buf receives at most
   DA_STRING_SIZE - 1 characters and a terminator; the length is
   returned. */
#define DA_STRING_SIZE 25
int da_to_string(char buf[DA_STRING_SIZE], da d);

/* Formatting as printf does with its conversions f, e and g: fmt is what
   stands between the % and the conversion letter of a printf conversion
   specification, with the letter included, as in ".2f", "+12.5e" or "#G".
   The flags -, +, space, # and 0, the width and the precision have their
   usual meanings; * is not accepted. The value is exact in decimal, so the
   only rounding is to the precision, done with ties to even. da_snprintf
   writes at most size - 1 characters followed by a terminator and returns
   the length of the complete output; da_asprintf stores a malloc'd copy in
   *strp. Both return -1, with errno set to EINVAL on a fmt that is not
   such a specification, and to EOVERFLOW when the output would be longer
   than INT_MAX. */
int da_snprintf(char *buf, size_t size, const char *fmt, da d);
int da_asprintf(char **strp, const char *fmt, da d);

/* da_to_string to stdout. */
void da_print(da d);

// Returns the closest DEC alpha representation of i * 10^(exp-142)
/*@ requires 0 <= exp < 255; */
da da_from_integer_and_biased_exp(uint64_t i, int exp);
da da_from_integer(uint64_t i);

/* Converts the initial portion of nptr to the nearest DEC alpha value, as
   strtod does for doubles in the C locale, whatever the current locale:
   optional whitespace and sign, then decimal digits with an optional
   point and an optional exponent, or inf, infinity or nan, all
   case-insensitive. Unlike strtod, it accepts no hexadecimal form and
   never sets errno. If endptr is not null, it receives the address of
   the first unconsumed character, or nptr when there is nothing to
   convert, in which case the result is +0. */
da strtoda(const char *nptr, char **endptr);

da da_neg(da x);
da da_add(da dx, da dy);
da da_mult(da dx, da dy);
da da_div(da dx, da dy);
da da_sqrt(da dx);

/* x rounded to a multiple of 10^e in the rounding mode given, one of the
   constants below, or infinite when that exceeds the largest finite value.
   This is IEEE 754's quantize, without the restriction on the number of
   digits of the result, and with the rounding direction as an argument.
   NaN and infinities are unchanged, and the sign of x is kept when the
   result is zero. The modes are IEEE 754's roundTiesToEven,
   roundTiesToAway, roundTowardZero, roundTowardPositive and
   roundTowardNegative, and rounding away from zero, which IEEE 754 lacks
   and which the encoding of the others gives for free. */
#define DA_TIES_TO_EVEN 0
#define DA_TIES_TO_AWAY 1
#define DA_TOWARD_ZERO 4
#define DA_TOWARD_POSITIVE 5
#define DA_TOWARD_NEGATIVE 6
#define DA_AWAY_FROM_ZERO 7
da da_quantize(da x, int e, int mode);

/* x * y + z with a single rounding, as IEEE 754's fusedMultiplyAdd. */
da da_fma(da x, da y, da z);

/* The next value toward +inf and toward -inf, as IEEE 754's nextUp and
   nextDown. The successor of both zeros is the smallest positive
   subnormal, and that of the smallest negative subnormal is -0. NaN is
   returned unchanged, and so are +inf by da_succ and -inf by da_pred. */
da da_succ(da x);
da da_pred(da x);

/* -1, 0 or 1 as x is less than, equal to or greater than y, or
   DA_UNORDERED when either is NaN. Zeros of both signs are equal.
   Comparing the result to 0 with <, <=, == or != gives IEEE 754's quiet
   predicate of the same name; for > and >=, swap the arguments instead,
   DA_UNORDERED being positive. */
#define DA_UNORDERED 2
int da_compare(da x, da y);

/* -1, 0 or 1 following IEEE 754's totalOrder: negative NaNs, then -inf up
   to -0, then +0 up to +inf, then positive NaNs, NaNs of the same sign
   being ordered by their representation. Suitable for sorting. */
int da_total_order(da x, da y);

/* IEEE 754's inexact flag, sticky and per thread: the library raises it
   when a result differs from the exact one, the infinities of overflow
   and the zeros of underflow included, and never clears it; a program
   that cares clears it before a computation and reads it after. Raising
   it is a compile-time option of each file: dec-alpha.c compiled with
   DA_INEXACT defined raises it in the operations and the conversions,
   and da_printing.c compiled with DA_INEXACT_PRINTF defined raises it
   when the precision of da_snprintf and da_asprintf drops nonzero
   digits. Otherwise the library never touches it. */
extern _Thread_local int da_inexact;

#endif

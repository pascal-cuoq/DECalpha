DEC α is a new 64-bit decimal floating-point format, and a C11 library to
manipulate this format.

The advantage of a decimal floating-point format over the widespread
hardware implementations of binary floating-point is that decimal
floating-point allows to represent exactly values such as 123E45 or
0.1 in a compact manner. Note that in a decimal floating-point system
with at least 3 digits of precision, the value 3.14 is represented
exactly, but π isn't represented any more exactly in decimal than it
is in binary. For computations that involve physical measurements or
any constants not chosen by humans (including the irrational values π
or e, or the Avogadro constant until 2019-05-20), binary
floating-point is more efficient. Decimal is only better in specific
usecases such as monetary computations or computations involving the
Avogadro constant after 2019-05-20
(https://en.wikipedia.org/wiki/Avogadro_constant ).

DEC α represents numbers with 16 or 17 decimal digits of
precision. Unlike in many other decimal floating-point formats, each
representable value has only one representation, and each 64-bit unsigned
integer represents some DEC α value (which can be a NaN value).

The DEC α values of positive sign are represented in increasing order
from 0 (representing +0) to 0x7f8e38e38e38e38e (representing the
maximum finite value, 4.0031996687737742E128) and 0x7f8e38e38e38e38f
(representing +inf).  Within this range, the next representable value
after a DEC α number D can always be obtained by adding one to the
representation of D. This aspect is similar to binary IEEE 754
formats, although the decimal formats specified in IEEE 754-2008 do
not have these properties. These properties are also absent from
.NET's 128-bit decimal format and Douglas Crockford's DEC64 format.

## Representation

A DEC α value is a 64-bit unsigned integer `r`. Bit 63 is the sign and
the 63 remaining bits encode a magnitude, as follows.

* `r` below `DECADE_LO` = 4003199668773775 is zero or a subnormal, of
  value `r` × 10^-142.
* Otherwise, let `o` = `r` − `DECADE_LO`. The biased exponent is
  `e` = `o` >> 55, and the significand is `sd` = `DECADE_LO` + (`o` mod
  2^55). For `e` from 0 to 254, the value is `sd` × 10^(`e` − 142), with
  `sd` between `DECADE_LO` and `DECADE_HI` = 40031996687737742.
* `e` = 255 encodes infinity when `sd` is `DECADE_LO`, and NaN otherwise.

Each decade thus contains exactly 2^55 significands, so that splitting
a representation into exponent and significand is a subtraction and a
shift. The gap between two consecutive values is one unit inside a
decade, and eight units at the boundary between two decades, because
9 × `DECADE_LO` exceeds 2^55 by 7.

Values with biased exponent 0 have the same granularity as the
subnormals, which are the natural continuation below `DECADE_LO`.

## Precision

Every decimal number with at most 16 significant digits is represented
exactly when it is within range. A decimal number with 17 significant
digits is represented exactly when its 17 digits form an integer at most
40031996687737742. The README's "16 or 17 digits" should be read with
this in mind: a 17-digit number that starts with 5, 6, 7, 8 or 9 is
rounded, as are some 17-digit numbers starting with 4.

The boundary at 4.0032 × 10^k is a trade-off. The alternative could
have been decades of 9 × 10^15 significands starting at 10^15,
representing exactly the 16-digit decimals, with 1024 decades of
exponent range instead of 255, at the cost of a division by a constant
when splitting a representation. That cost was overestimated when DEC
α was designed: on modern processors such a division compiles to a
multiplication by a precomputed reciprocal, and the alternative
remains worth exploring.

The choice of 2^55 significands keeps the separation of exponent and
significand a subtraction, a shift and a mask, in software as in
hardware. IEEE 754 arguably gave this up when it defined two encodings
for its decimal formats: the binary integer encoding, meant for
software, stores the exponent at one of two positions depending on the
two leading bits of the combination field, and the densely packed
encoding, meant for hardware, stores the digits three by three in
declets that need decoding. This is a genuine simplification, but a
modest one: extracting the fields is a small part of any operation,
whose cost is dominated by the divisions by powers of ten of the
rounding, and the division by a constant that decades of 9 × 10^15
significands would need costs a few cycles on modern processors. The
properties of DEC α that stand on their own are the unique
representation and the monotone encoding, which do not depend on the
number of significands per decade.

The choice of 55 in 2^55 buys worst-case
relative precision at the cost of range. The unit roundoff, the
largest relative error of rounding to nearest, is half a unit divided
by `DECADE_LO`:

| Format                 | Unit roundoff |
|------------------------|---------------|
| DEC α                  | 1.25e-16      |
| IEEE 754 binary64      | 1.11e-16      |
| IEEE 754 decimal64     | 5e-16         |

DEC α is thus almost as precise as binary64 in the worst case, while
decimal64 is four times less precise.

The largest finite value is `DECADE_HI` × 10^112, about 4.0032e128. The
smallest normal value is `DECADE_LO` × 10^-142, about 4.0032e-127, and
the smallest subnormal is 10^-142. The range is small compared to
decimal64, which extends from 10^-398 to almost 10^385. The exponent
bias of 142 follows the IEEE 754 convention that the overflow threshold
times the smallest normal value is about the square of the radix: the
reciprocal of every normal value is finite, 1/x is subnormal when x
exceeds about 2.5e126, and 1/x overflows to infinity only when x is
itself subnormal, below about 2.5e-129.

## Rounding

All operations return the representable value nearest to the exact
result, with ties going to the even representation. Since `DECADE_LO` is
odd, the parity of a representation is that of its significand, and this
holds across decade boundaries as well: on the midpoint between
`DECADE_HI` × 10^k and `DECADE_LO` × 10^(k+1), which is
40031996687737746 × 10^k, the result is `DECADE_HI` × 10^k.

The same rule decides overflow: a result rounds to infinity when it is
strictly greater than 40031996687737746 × 10^112, and to the largest
finite value when it is at most that midpoint. A result below half the
smallest subnormal rounds to zero.

There are no other rounding modes, and no exception flags: inexact,
overflow, underflow, division by zero and invalid operation cannot be
observed other than through the result. This is a deliberate
simplification.

## Special values

Zero is signed. A product or quotient that is zero has the exclusive-or
of the signs of the operands. A sum that is exactly zero is +0, except
that (−0) + (−0) is −0. A result that underflows to zero keeps the sign
the exact result would have.

Infinities behave as in IEEE 754: x / 0 is infinite with the sign of x
for x nonzero and finite, and inf − inf, 0 × inf, 0 / 0, inf / inf and
the square root of a negative number are NaN. The square root of −0 is
−0.

Every representation above that of infinity, in either sign, is a NaN.
There are 32025597350190192 of them per sign, no distinction between
quiet and signaling, and no a priori meaning attached to the payload.
An operation with NaN operands returns its first NaN operand unchanged.
An invalid operation with non-NaN operands returns `DA_NAN`, the
representation just above +inf.

## Ordering

The representations of values of positive sign are in increasing
order, as the introduction says. Values of negative sign are in
sign-magnitude form, so their representations are in decreasing order
of value, as in the IEEE 754 binary formats. A total order in the sense
of IEEE 754's `totalOrder`, with −0 below +0, negative NaNs below −inf
and positive NaNs above +inf, is obtained by comparing as signed 64-bit
integers the representations transformed by
`r ^ (((int64_t)r >> 63) & INT64_MAX)`. `da_total_order` implements it.

## The library

The library is the files `dec-alpha.c` and `da_printing.c`, with their
interface in `dec-alpha.h`, and `demo.c` is a program that shows it off.
`dec-alpha.c` holds the arithmetic, the comparisons and the conversions
from and to strings, and depends on nothing beyond `sqrt` from
`math.h`, whose binary floating-point root seeds `da_sqrt`.[^fenv]

[^fenv]: The rounding mode does not affect the result, but `da_sqrt` can
         raise `FE_INEXACT` even when the root is exact. No other
         floating-point flag is ever raised by the library.

`da_printing.c` holds everything that writes to a stream or
allocates, so that programs that need neither can leave it out. The
locale is ignored both when printing and when parsing.

The library needs a 128-bit unsigned integer type to get at the
processor's 64×64→128 multiplication and 128/64→64 division: C23's
`unsigned _BitInt(128)` when the compiler provides it, which Clang 14
and later do on every target, and GCC 14 and later on IA-32, x86-64 and
little-endian AArch64, joined in GCC 16 by 32-bit ARM and RISC-V, in any
language mode, and otherwise the `__uint128_t` extension of older GCC
and Clang, from GCC 4.6 and Clang 3.3 on, which only 64-bit targets
provide.

The command `make` builds the demonstration with the project's warning
flags and with `-fno-math-errno`, which lets compilers inline `sqrt` as
a single instruction on common 64-bit processors, so that no math
library is needed at link time. Without this flag, GCC keeps a fallback
call for a negative argument that cannot occur and the program must be
linked with `-lm`.

The header defines the type `da`, whose representation `r` is public,
the constants `DA_DECADE_LO` and `DA_DECADE_HI`, the values `DA_ZERO`,
`DA_INFINITY`, `DA_MINUS_INFINITY` and `DA_NAN` as compound literals,
and declares the functions:

* `da_from_integer(uint64_t)` and `da_from_integer_and_biased_exp(uint64_t
  i, int exp)`, which round `i` × 10^(`exp` − 142) to nearest;
* `strtoda(const char *, char **)`, which converts the initial portion of
  a string as `strtod` does in the C locale, whatever the current one,
  correctly rounded whatever the number of digits, minus the hexadecimal
  form and the setting of `errno`;
* `da_neg`, `da_add`, `da_mult`, `da_div`, `da_sqrt` and `da_fma`,
  correctly rounded for all inputs, including special values;
* `da_quantize(da x, int e)`, the multiple of 10^e nearest to `x`, ties
  to even, which is IEEE 754's `quantize` without the restriction on the
  number of digits of the result: a value too large to have digits below
  10^e is returned unchanged;
* `da_succ` and `da_pred`, the next value toward +inf and toward −inf,
  as IEEE 754's `nextUp` and `nextDown`;
* `da_compare`, returning −1, 0, 1 or `DA_UNORDERED` (which is 2, so
  that comparing the result to 0 with `<`, `<=`, `==` or `!=` gives the
  IEEE 754 quiet predicate of that name, and `>` and `>=` are obtained by
  swapping the arguments), and `da_total_order`, the −1, 0 or 1 of the
  total order above, for sorting;
* `da_to_string(char buf[DA_STRING_SIZE], da d)`, which writes the exact
  value to `buf` in the style of C's `%g` with 17 significant digits:
  positional notation such as `0.1` or `1000` when the leading digit has
  a decimal exponent between −4 and 16, and `d.dddE+dd` otherwise. The
  output is at most 24 characters, a sign, 17 digits, a point and a
  three-digit exponent with its sign, so a buffer of `DA_STRING_SIZE`
  bytes always suffices, and the length is returned. This string is
  canonical: it is read back exactly by `strtoda`;
* `da_print`, in `da_printing.c`, which writes `da_to_string` to the
  standard output;
* `da_snprintf(char *buf, size_t size, const char *fmt, da d)` and
  `da_asprintf(char **strp, const char *fmt, da d)`, also in
  `da_printing.c`, which format `d` as `snprintf` and `asprintf` would
  with a single conversion. `fmt` is what stands between the `%` and the
  conversion letter of a `printf` conversion specification, with the
  letter included: `".2f"`, `"+12.5e"`, `"#G"`. The flags `-`, `+`,
  space, `#` and `0`, the width and the precision have their usual
  meanings, and the letter is one of `f`, `e`, `g` and their uppercase
  forms; `*` is not accepted. Because the value is an exact decimal, the
  output is what `printf` prints for a `double` of the same value when
  such a `double` exists, and the only rounding is to the requested
  precision, with ties to even: `".0f"` prints `2.5` as `2`. The return
  value is the length of the complete output, or −1 when `fmt` is not
  such a specification.

There is no conversion from or to binary floating-point.

## Testing

`make check` builds and runs two test programs. `test-fixed.c` holds
cases with expected results written by hand: the syntax and rounding of
`strtoda` on long numerals, the signs of zero, the special values, ties
inside a decade and at its ends, the overflow threshold, subnormals,
NaN propagation, the orderings, and the output of `da_snprintf` and
`da_to_string`. It needs nothing beyond the library.
`test-random.c` checks the library against an oracle built on GMP
rationals, and requires GMP; `./test-random seed count` chooses the
random seed and the number of iterations per section.

The oracle is a single function that rounds a rational to the nearest
DEC α value, or to the nearest value of its square root, using nothing
but the definition of the representation: a binary search over the
monotone encoding finds the two neighbors of the exact result, and a
comparison with their midpoint decides, ties going to the even
representation. Decoding the representation of +inf as `DECADE_LO` ×
10^113 makes the overflow rule fall out of the same comparison.

Each operation is exercised on uniformly random operands and on
constructed ones: exact midpoints for multiplication and division,
half-unit addends and exponent gaps around the cutoff for addition,
the decade boundary in all operations, arguments whose square root is
near a midpoint, subnormal operands and results, the overflow region,
and every special value. The test prints how many exact ties each
section met. `da_succ` and `da_pred` are checked for adjacency by
rounding the midpoint of the two values nudged slightly either way.

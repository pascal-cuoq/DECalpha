## Testing

The command `make check` builds and runs two test programs:

  - `test-fixed.c` checks hand-written tricky cases with expected
    results: syntax and rounding of `strtoda` on long numerals, signs
    of zero, special values, ties inside a decade and at the decade
    gap, overflow threshold, subnormals, NaN propagation, orderings,
    inexact flag on cases of every kind, and output of `da_snprintf`
    and `da_to_string`. It needs nothing beyond the library.

  - `test-random.c` checks the library against an oracle built on GMP
    rationals. It requires GMP. The command `./test-random seed count`
    chooses the random seed and the number of iterations per section.

    The oracle is a single function that rounds a rational to the
    nearest DEC α value, or to the nearest value of its square root,
    using nothing but the definition of the representation: a binary
    search over the monotone encoding finds the two neighbors of the
    exact result, and a comparison with their midpoint decides, ties
    going to the even representation. Decoding the representation of
    +inf as `DECADE_LO` × 10^113 makes the overflow rule fall out of
    the same comparison.

    The random tests exercise each operation both on uniformly random
    operands and on biased ones: exact midpoints for multiplication
    and division, half-unit addends and exponent gaps around the
    cutoff for addition, the decade boundary in all operations,
    arguments whose square root is near a midpoint, subnormal operands
    and results, the overflow region, and every special value. The
    test prints how many exact ties each section met. `da_succ` and
    `da_pred` are checked for adjacency by rounding the midpoint of
    the two values nudged slightly either way.

Each test program is linked with both builds of the library, and
checks the inexact flag against the build: in the build with the
option, raised exactly when the exact result is not representable, or
when a printed value does not read back as the value printed, and in
the other, never touched.

## Why are there four rounding functions?

The functions are `da_round`, `da_round_wide`, `da_round_narrow`,
and `da_round_any_exp`.

`da_round` is a common tail for the other three. It takes a 128-bit
numerator, a divisor, and a biased exponent. The quotient must already
sit in a decade, or below the first decade when the exponent is zero.
It does one 128/64 division[^div], decides on the remainder with ties
to even, handles the seven holes at the top of the decade by choosing
between the top value and the next decade's bottom one, and lets
`da_wrap` turn an exponent past the limit into infinity. It does no
power-of-ten scaling. The three other functions, plus
`da_from_integer_and_biased_exp`, end by calling it, except where they
settle the result on their own as exact or as zero. Square root and
quantization do not use it: their rounding has no division to share,
and each decides inline.

[^div]: I have not managed to make either GCC or Clang emit the
straight processor instruction when the target processor has it. This
and a couple of other annoyances could be fixed by making an x86-64
assembly version of the library, but to be fair, this would only save
a few cycles. One reason to write this library in C was that C seemed
a good match for it, and it has been, mostly.

Each front-end for `da_round` matches what its callers already know
about where the exact result lies, so that each operation only pays
for the scaling it needs.

  - `da_round_narrow` serves addition and subtraction. The caller knows
    the exact result is in decade j or j+1: a sum of two aligned
    significands can overflow its decade by at most one, and a
    difference without cancellation can drop by at most one. One
    comparison settles which, the divisor is a table entry, and the
    exponent is the smaller operand's, which is never negative, so no
    subnormal or underflow logic is needed. This is the cheapest path.

  - `da_round_any_exp` serves multiplication and division. There the
    quotient (of the arguments of `da_round`) is known to be below the
    top of a decade but may be one or two decades too small for normal
    operands (and further below for subnormal ones). A short
    multiply-by-ten loop fixes that, running zero to two times in the
    normal case. The exponent it receives may already be negative, the
    operands being small, and the loop lowers it further, so this is
    also the entry that must handle a negative exponent: it folds the
    missing power of ten into the divisor so the tail still sees
    exponent zero, and returns zero below -16. It is the only front-end
    whose divisor is not a power of ten, since division passes the
    divisor's significand.

  - `da_round_wide` serves `strtoda` and `da_fma`, whose exact results
    can land anywhere over dozens of decades: a parsed 19-digit mantissa
    with an arbitrary exponent, or a 128-bit product plus addend that may
    have cancelled massively. A loop would be too long here, so it
    uses the decade lookup. It also owns cases the others never meet:
    a result already exact, finished with a single 64-bit multiply and
    no division, which matters for fma, and a subnormal result whose
    divisor exceeds 64 bits and is built from two table entries. Its
    exponent floor of -34 comes from the fma alignment: an addend
    scaled up by 10^33 to meet the product of two subnormals, then by
    10 more to make room for the sticky digit. `strtoda`, which clamps
    its decimal exponent to ±300, passes exponents down to -159, but
    the underflow test turns everything below -35 into zero before the
    exponent is used.

  - `da_from_integer_and_biased_exp` is effectively a fourth front-end
    for `da_round`. It allows the user of the library to create values,
    so it has to accept arbitrary `uint64_t` integers and a wide gamut
    of exponents. It is also used as the last step of subtractions
    with cancellation, a situation where no rounding is necessary but
    the integer can be arbitrarily small and has to be lifted by many
    powers of ten in order to create a normalized representation. The
    power of ten needed is approximated from the bit width of the
    integer, using 1233/4096 as an approximation of log10(2), followed
    by an optional last multiplication by 10 if the result is still too
    low, written so that the compiler translates it branchlessly, which
    GCC does at `-O2`. Both steps stop at biased exponent 0, where the
    result is subnormal. In the other direction, an integer of up to
    20 digits can exceed the decade by up to three; three comparisons
    count by how many, and `da_round` divides by that power of ten.

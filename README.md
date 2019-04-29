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
Avogadro constant after 2019-05-20 (https://en.wikipedia.org/wiki/Avogadro_constant ).

DEC α represents numbers with 16 or 17 decimal digits of
precision. Unlike in many other decimal floating-point formats, each
representable value has only one representation, and each 64-bit unsigned
integer represents some DEC α value (which can be a NaN value).

The positive DEC α values are represented in increasing order
from 0 (representing 0) to 0x7f8e38e38e38e38e (representing the
maximum finite value, 4.0031996687737742E130) and 0x7f8e38e38e38e38f
(representing +inf).  Within this range, the next representable value
after a DEC α number D can always be obtained by adding one to the
representation of D. This aspect is similar to binary IEEE 754
formats, although the decimal formats specified in IEEE 754-2008 do
not have these properties. These properties are also absent from
.NET's 128-bit decimal format and Douglas Crockford' DEC64 format.




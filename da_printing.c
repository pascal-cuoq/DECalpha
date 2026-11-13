/* Printing of DEC α values: da_to_string to stdout, and the conversions f,
   e and g of printf, in their lowercase and uppercase forms. A DEC α value
   is an exact decimal, so the only rounding is the one asked for by the
   precision, done in decimal with ties to even, as glibc does for a double
   whose binary expansion is exactly a tie. This file is the only part of
   the library that depends on stdio and malloc. */

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "da_internal.h"

/* The inexact flag, raised by the rounding to the precision when this
   file is compiled with DA_INEXACT_PRINTF defined, untouched otherwise: */
#ifdef DA_INEXACT_PRINTF
#define INEXACT_PRINTF(cond) (da_inexact |= (cond))
#else
#define INEXACT_PRINTF(cond) ((void)0)
#endif

int da_print(da d) {
  char buf[DA_STRING_SIZE];
  da_to_string(buf, d);
  return fputs(buf, stdout);
}

/* Output that counts every character and stores those that fit, leaving
   room for the terminator, as snprintf does. */
typedef struct { char *buf; size_t size, n; } sink;

static void put(sink *s, char c) {
  size_t n = s->n;
  if (n + 1 < s->size) s->buf[n] = c;
  s->n = n + 1;
}

static void fill(sink *s, char c, int count) {
  while (count-- > 0) put(s, c);
}

static void text(sink *s, const char *str) {
  char c;
  while (c = *str) { put(s, c); str++; }
}

/* The digit at index i of the string made of lead zeros, the nd digits of
   nb, and zeros forever after. */
static void digits(sink *s, const char *nb, int nd, int lead, int lo,
                   int hi) {
  for (int i = lo; i < hi; i++) {
    int j = i - lead;
    put(s, 0 <= j && j < nd ? nb[j] : '0');
  }
}

/* sd / 10^drop rounded to nearest, ties to even. sd is nonzero and below
   10^17. */
static uint64_t round_drop(uint64_t sd, int drop) {
  if (drop > 17) {
    INEXACT_PRINTF(1);
    return 0;
  }
  uint64_t p = da_powers[drop], n = sd / p, rem = sd - n * p;
  INEXACT_PRINTF(rem != 0);
  return n + (2 * rem > p || 2 * rem == p && (n & 1));
}

/* The decimal digits of n, as a string, and their number. */
static int utoa(char nb[static 21], uint64_t n) {
  return sprintf(nb, "%" PRIu64, n);
}

int da_snprintf(char *buf, size_t size, const char *fmt, da d) {
  _Bool left = 0, plus = 0, space = 0, alt = 0, zero = 0;
  char c;
  for (;; fmt++) {
    switch (c = *fmt) {
    case '-': left = 1; continue;
    case '+': plus = 1; continue;
    case ' ': space = 1; continue;
    case '#': alt = 1; continue;
    case '0': zero = 1; continue;
    }
    break;
  }
  /* A width beyond INT_MAX becomes -1, and makes the output too long
     for the int return type. A precision beyond it becomes INT_MAX,
     which makes the output too long too unless it is clamped below. */
  int width = 0, prec = -1;
  for (; c >= '0' && c <= '9'; fmt++, c = *fmt) {
    int d = c - '0';
    width = width < 0 || width > (INT_MAX - d) / 10 ? -1 : 10 * width + d;
  }
  if (c == '.') {
    prec = 0;
    for (fmt++, c = *fmt; c >= '0' && c <= '9'; fmt++, c = *fmt) {
      int d = c - '0';
      prec = prec > (INT_MAX - d) / 10 ? INT_MAX : 10 * prec + d;
    }
  }
  if (!c || fmt[1] || !strchr("fFeEgG", c)) {
    errno = EINVAL;
    return -1;
  }
  _Bool upper = c < 'a';
  char conv = c | 0x20;
  if (prec < 0) prec = 6;
  /* No value has more than 17 significant digits nor its leading digit
     beyond 10^128, so g without # prints the same for any precision from
     129 on. */
  if (conv == 'g' && !alt && prec > 129) prec = 129;

  uint64_t a = d.r & ~SIGN_MASK;
  char sign = d.r != a ? '-' : plus ? '+' : space ? ' ' : 0;
  const char *special = NULL;
  /* Finite values are n * 10^(z-P) as a string: the nd digits of nb, then
     z zeros, with the point P places from the end and frac of the P
     fractional digits actually printed, then extra zeros. eb is the
     exponent suffix. */
  char nb[21], eb[8] = "";
  int nd = 0, z = 0, P = 0, frac = 0, lead = 0, extra = 0;
  if (a >= DA_INFINITY.r) {
    special = a == DA_INFINITY.r ? (upper ? "INF" : "inf")
                                 : (upper ? "NAN" : "nan");
    zero = 0;
  }
  else {
    uint64_t sd = a;
    int k = EXP_MIN; // the value is sd * 10^k
    if (a >= DA_DECADE_LO) {
      uint64_t o = a - DA_DECADE_LO;
      sd = DA_DECADE_LO + (o & SD_MASK);
      k += (int)(o >> EXP_SHIFT);
    }
    if (sd == 0) k = 0;
    /* No value has a digit below 10^-142 nor more than 17 digits, so
       from 142 on, more precision only appends zeros. */
    if (prec > 142) {
      extra = prec - 142;
      prec = 142;
    }
    uint64_t n = sd;
    if (conv == 'f') {
      P = prec;
      int drop = -P - k;
      if (drop > 0) n = round_drop(sd, drop);
      else z = -drop;
      frac = P;
    }
    else { // e, or g which starts as e
      int sig = conv == 'e' ? prec + 1 : prec ? prec : 1;
      int len = utoa(nb, sd);
      int x = len - 1 + k; // the decimal exponent of the leading digit
      int drop = len - sig;
      if (drop > 0) {
        n = round_drop(sd, drop);
        if (n == da_powers[sig]) { // 99..9 rounded up
          n /= 10;
          x++;
        }
      }
      else
        z = -drop;
      if (conv == 'g' && x >= -4 && x < sig)
        P = sig - 1 - x;
      else {
        P = sig - 1;
        sprintf(eb, "%c%+03d", upper ? 'E' : 'e', x);
      }
      frac = P;
      if (conv == 'g' && !alt) { // drop the trailing zeros of the fraction
        int tz = z;
        for (uint64_t m = n; m && m % 10 == 0; m /= 10) tz++;
        frac = tz < P ? P - tz : 0;
      }
    }
    nd = utoa(nb, n);
    if (nd + z < P + 1) lead = P + 1 - nd - z;
  }
  _Bool point = frac > 0 || alt;
  int body = special ? 3
    : lead + nd + z - P + point + frac + (int)strlen(eb);
  if (width < 0 || extra > INT_MAX - (sign != 0) - body) {
    errno = EOVERFLOW;
    return -1;
  }
  body += extra;
  int pad = width - body - (sign != 0);

  sink s = {buf, size, 0};
  if (!left && !zero) fill(&s, ' ', pad);
  if (sign) put(&s, sign);
  if (!left && zero) fill(&s, '0', pad);
  if (special)
    text(&s, special);
  else {
    int T = lead + nd + z;
    digits(&s, nb, nd, lead, 0, T - P);
    if (point) put(&s, '.');
    digits(&s, nb, nd, lead, T - P, T - P + frac);
    fill(&s, '0', extra);
    text(&s, eb);
  }
  if (left) fill(&s, ' ', pad);
  if (size) buf[s.n < size ? s.n : size - 1] = 0;
  return (int)s.n;
}

int da_asprintf(char **strp, const char *fmt, da d) {
  int len = da_snprintf(NULL, 0, fmt, d);
  if (len < 0 || !(*strp = malloc((size_t)len + 1))) return -1;
  return da_snprintf(*strp, (size_t)len + 1, fmt, d);
}

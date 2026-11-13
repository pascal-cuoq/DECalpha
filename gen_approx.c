/* What the generators share: see gen_approx.h. */
#include <assert.h>
#include <math.h>
#include "gen_approx.h"

#define STEPS 2000
#define PI 3.141592653589793 // the double nearest pi

static mpq_t M[DEGREE_MAX + 2][DEGREE_MAX + 3]; // the system of solve
static mpfr_t S[DEGREE_MAX + 2];                // its solution
static mpfr_t grid[STEPS], fs[STEPS], ws[STEPS], errs[STEPS];

void approx_init(void)
{
  mpfr_set_default_prec(PRECISION);
  for (int r = 0; r < DEGREE_MAX + 2; r++) {
    mpfr_init(S[r]);
    for (int j = 0; j < DEGREE_MAX + 3; j++)
      mpq_init(M[r][j]);
  }
  for (int k = 0; k < STEPS; k++)
    mpfr_inits(grid[k], fs[k], ws[k], errs[k], (mpfr_ptr)0);
}

double q(mpz_t i, mpfr_srcptr v, int n)
{
  mpfr_t s;
  mpfr_init(s);
  mpfr_mul_2si(s, v, n, MPFR_RNDN);
  mpfr_get_z(i, s, MPFR_RNDN);
  assert(mpz_sgn(i) < 0 ? mpz_fits_slong_p(i)
         : mpz_sizeinbase(i, 2) <= 64);
  mpfr_sub_z(s, s, i, MPFR_RNDN);
  double err = fabs(mpfr_get_d(s, MPFR_RNDN));
  mpfr_clear(s);
  return err;
}

void bias(mpfr_ptr v, double units, int n)
{
  mpfr_t s;
  mpfr_init(s);
  mpfr_set_d(s, units, MPFR_RNDN);
  mpfr_mul_2si(s, s, -n, MPFR_RNDN);
  mpfr_add(v, v, s, MPFR_RNDN);
  mpfr_clear(s);
}

/* The solution of the linear system of the first n rows of M, each
   the coefficients and the right-hand side, in S: Gauss-Jordan on
   exact rationals. */
static void solve(int n)
{
  mpq_t t, u;
  mpq_inits(t, u, (mpq_ptr)0);
  for (int c = 0; c < n; c++) {
    int p = c;
    while (!mpq_sgn(M[p][c]))
      p++;
    for (int j = 0; j <= n; j++)
      mpq_swap(M[c][j], M[p][j]);
    mpq_set(t, M[c][c]);
    for (int j = 0; j <= n; j++)
      mpq_div(M[c][j], M[c][j], t);
    for (int r = 0; r < n; r++) {
      if (r == c)
        continue;
      mpq_set(t, M[r][c]);
      for (int j = 0; j <= n; j++) {
        mpq_mul(u, t, M[c][j]);
        mpq_sub(M[r][j], M[r][j], u);
      }
    }
  }
  for (int r = 0; r < n; r++)
    mpfr_set_q(S[r], M[r][n], MPFR_RNDN);
  mpq_clears(t, u, (mpq_ptr)0);
}

/* The polynomial of the n coefficients c, highest degree first, at
   x, in p, which is not x. */
static void horner(mpfr_ptr p, mpfr_t *c, int n, mpfr_srcptr x)
{
  mpfr_set_zero(p, 1);
  for (int k = 0; k < n; k++) {
    mpfr_mul(p, p, x, MPFR_RNDN);
    mpfr_add(p, p, c[k], MPFR_RNDN);
  }
}

/* Remez's exchange: p has errors of the same magnitude and
   alternating signs at n + 1 points, which are then moved to the
   extrema of its error, on a grid. */
double remez(mpfr_t *c, fn *f, fn *weight, mpfr_srcptr top, int n)
{
  int ks[DEGREE_MAX + 2];
  assert(n <= DEGREE_MAX + 1);
  mpq_t g;
  mpq_init(g);
  for (int k = 0; k < STEPS; k++) {
    mpfr_mul_ui(grid[k], top, k + 1, MPFR_RNDN);
    mpfr_div_ui(grid[k], grid[k], STEPS, MPFR_RNDN);
    f(fs[k], grid[k]);
    weight(ws[k], grid[k]);
  }
  for (int k = 0; k <= n; k++)
    ks[k] = nearbyint(STEPS * (1 - cos((k + 1) * PI / (n + 1))) / 2)
      - 1;
  for (int it = 0; it < 12; it++) {
    for (int i = 0; i <= n; i++) {
      mpfr_get_q(g, grid[ks[i]]);
      mpq_set_ui(M[i][0], 1, 1);
      for (int j = 1; j < n; j++)
        mpq_mul(M[i][j], M[i][j - 1], g);
      mpfr_get_q(M[i][n], ws[ks[i]]);
      mpq_inv(M[i][n], M[i][n]);
      if (i & 1)
        mpq_neg(M[i][n], M[i][n]);
      mpfr_get_q(M[i][n + 1], fs[ks[i]]);
    }
    solve(n + 1);
    for (int j = 0; j < n; j++) // highest degree first
      mpfr_set(c[j], S[n - 1 - j], MPFR_RNDN);
    // the grid by runs of the sign of the error, and the largest
    // error of each run
    int r = 0;
    ks[0] = 0;
    for (int k = 0; k < STEPS; k++) {
      horner(errs[k], c, n, grid[k]);
      mpfr_sub(errs[k], errs[k], fs[k], MPFR_RNDN);
      mpfr_mul(errs[k], errs[k], ws[k], MPFR_RNDN);
      if (k == 0)
        continue;
      if ((mpfr_sgn(errs[k]) > 0) != (mpfr_sgn(errs[k - 1]) > 0)) {
        r++;
        assert(r <= n);
        ks[r] = k;
      } else if (mpfr_cmpabs(errs[k], errs[ks[r]]) > 0)
        ks[r] = k;
    }
    assert(r == n);
  }
  mpq_clear(g);
  int m = 0;
  for (int k = 1; k < STEPS; k++)
    if (mpfr_cmpabs(errs[k], errs[m]) > 0)
      m = k;
  return fabs(mpfr_get_d(errs[m], MPFR_RNDN));
}

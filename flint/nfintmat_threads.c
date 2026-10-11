/* 
 * (C) 2026 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
 *
 * This file implements a translation of the GAP library function DoNFIM
 * to a standalone C program.
 *
 * It uses FLINT (https://flintlib.org/) for the arithmetic and a thread
 * farm. The main loops are parallelized.
 *
 *
 *      nfintmat nrthreads options  < inputflintmat > outputgaprec
 *
 * options as for DoNFIM: 1 Smith, 2 reduce off diagonal entries,
 * 4 row transforms, 8 col transforms. Option 16 is handled by the 
 * GAP wrapper, which is DoNFIMthreads.
 *
 *
 * compile with
 *     gcc -O3 -march=native -mavx2 -o nfintmat nfintmat.c do_parallel_dyn.c -lflint -lgmp
 *
 * For easier comparison with the GAP code, rows and columns are counted from 1
 * (row and col 0 are unused).
*/

#include <stdlib.h>
#include <stdio.h>
#include <gmp.h>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>
#include <flint/thread_pool.h>
#include <flint/thread_support.h>
#include "do_parallel_dyn.h"

/* compile with -DNFIM_PROFILE to get timings of the phases on stderr */
#ifdef NFIM_PROFILE
#include <time.h>
static double prof_t[16], prof_last;
static const char *prof_name[16] = { "read input", "pivot search",
  "smith column ops", "mgcdex + add to row r+1", "fix row, bezout, 2x2",
  "eliminate rows r+2..n", "SNFofREF", "hermite reduce",
  "smith final", "output", "setup, bookkeeping", "hermite: smith col ops",
  "smith: mgcdex columns", "", "", "" };
static double prof_now(void)
{
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + 1e-9*ts.tv_nsec;
}
#define PROF(k) do { double _t = prof_now(); prof_t[k] += _t - prof_last; \
                     prof_last = _t; } while (0)
#define PROFSTART() (prof_last = prof_now())
static slong maxbits(fmpz **X, slong lo, slong hi, slong len)
{
  slong i, b = 0;
  for (i = lo; i <= hi; i++)
    b = FLINT_MAX(b, FLINT_ABS(_fmpz_vec_max_bits(X[i]+1, len)));
  return b;
}
#else
#define PROF(k)
#define PROFSTART()
#endif

typedef fmpz ** imat;   /* array of rows, 1-based */

static imat imat_init(slong n, slong m)
{
  slong i;
  imat A = flint_malloc((n+1)*sizeof(fmpz *));
  A[0] = NULL;
  for (i = 1; i <= n; i++)
    A[i] = _fmpz_vec_init(m+1);
  return A;
}

static imat imat_identity(slong n)
{
  slong i;
  imat A = imat_init(n, n);
  for (i = 1; i <= n; i++)
    fmpz_one(A[i]+i);
  return A;
}

static void imat_clear(imat A, slong n, slong m)
{
  slong i;
  for (i = 1; i <= n; i++)
    if (A[i] != NULL)
      _fmpz_vec_clear(A[i], m+1);
  flint_free(A);
}

/* a*b == c*d */
static int cross_eq(const fmpz_t a, const fmpz_t b,
                    const fmpz_t c, const fmpz_t d)
{
  int res;
  fmpz_t s, t;
  fmpz_init(s);
  fmpz_init(t);
  fmpz_mul(s, a, b);
  fmpz_mul(t, c, d);
  res = fmpz_equal(s, t);
  fmpz_clear(s);
  fmpz_clear(t);
  return res;
}

/* AddRowVector(v, w, c) on entries lo..hi */
static void addrow(fmpz *v, const fmpz *w, const fmpz_t c, slong lo, slong hi)
{
  if (!fmpz_is_zero(c) && hi >= lo)
    _fmpz_vec_scalar_addmul_fmpz(v+lo, w+lo, hi-lo+1, c);
}

static void subrow(fmpz *v, const fmpz *w, const fmpz_t c, slong lo, slong hi)
{
  if (!fmpz_is_zero(c) && hi >= lo)
    _fmpz_vec_scalar_submul_fmpz(v+lo, w+lo, hi-lo+1, c);
}

/* Apply(v, x -> x mod d) on entries 1..len */
static void modrow(fmpz *v, const fmpz_t d, slong len)
{
  _fmpz_vec_scalar_mod_fmpz(v+1, v+1, len, d);
}

/* GAP's Gcdex(m, n) */
typedef struct {
  fmpz_t gcd, coeff1, coeff2, coeff3, coeff4;
} gcdex_struct;

static void gcdex_init(gcdex_struct *e)
{
  fmpz_init(e->gcd);
  fmpz_init(e->coeff1);
  fmpz_init(e->coeff2);
  fmpz_init(e->coeff3);
  fmpz_init(e->coeff4);
}

static void gcdex_clear(gcdex_struct *e)
{
  fmpz_clear(e->gcd);
  fmpz_clear(e->coeff1);
  fmpz_clear(e->coeff2);
  fmpz_clear(e->coeff3);
  fmpz_clear(e->coeff4);
}

static void Gcdex(gcdex_struct *e, const fmpz_t m, const fmpz_t n)
{
  fmpz_t f, g, h, fm, gm, q;
  fmpz_init(f); fmpz_init(g); fmpz_init(h);
  fmpz_init(fm); fmpz_init(gm); fmpz_init(q);

  if (fmpz_sgn(m) >= 0) { fmpz_set(f, m); fmpz_one(fm); }
  else { fmpz_neg(f, m); fmpz_set_si(fm, -1); }
  fmpz_abs(g, n);
  fmpz_zero(gm);
  while (!fmpz_is_zero(g)) {
    fmpz_tdiv_q(q, f, g);
    fmpz_submul(f, q, g);  fmpz_swap(f, g);
    fmpz_submul(fm, q, gm);  fmpz_swap(fm, gm);
  }
  fmpz_set(e->gcd, f);
  fmpz_set(e->coeff1, fm);
  fmpz_set(e->coeff3, gm);
  if (fmpz_is_zero(n)) {
    fmpz_zero(e->coeff2);
    fmpz_one(e->coeff4);
  } else {
    /* coeff2 := (f - fm*m)/n,  coeff4 := (0 - gm*m)/n */
    fmpz_set(h, f);
    fmpz_submul(h, fm, m);
    fmpz_divexact(e->coeff2, h, n);
    fmpz_mul(h, gm, m);
    fmpz_neg(h, h);
    fmpz_divexact(e->coeff4, h, n);
  }
  fmpz_clear(f); fmpz_clear(g); fmpz_clear(h);
  fmpz_clear(fm); fmpz_clear(gm); fmpz_clear(q);
}

/* MATINTsplit(N, a): product of prime factors of N which are not
   factors of a */
static void MATINTsplit(fmpz_t res, const fmpz_t N, const fmpz_t a)
{
  fmpz_t x, t;
  fmpz_init_set(x, a);
  fmpz_init_set(t, N);
  while (!fmpz_is_one(x)) {
    fmpz_gcd(x, x, t);
    fmpz_tdiv_q(t, t, x);
  }
  fmpz_swap(res, t);
  fmpz_clear(x);
  fmpz_clear(t);
}

/* MATINTrgcd(N, a): smallest nonnegative c such that gcd(N, a+c) = 1 */
static void MATINTrgcd(fmpz_t res, const fmpz_t N, const fmpz_t a)
{
  slong k, i, alloc, c;
  fmpz *r, *d;
  fmpz_t g, q, tmp;

  if (fmpz_is_one(N)) {
    fmpz_zero(res);
    return;
  }
  fmpz_init(g); fmpz_init(q); fmpz_init(tmp);
  alloc = 8;
  r = _fmpz_vec_init(alloc+1);
  d = _fmpz_vec_init(alloc+1);
  k = 1;
  fmpz_sub_ui(r+1, a, 1);
  fmpz_mod(r+1, r+1, N);
  fmpz_set(d+1, N);
  c = 0;
  while (1) {
    for (i = 1; i <= k; i++) {
      fmpz_add_ui(r+i, r+i, 1);
      fmpz_mod(r+i, r+i, d+i);
    }
    for (i = 1; i <= k && fmpz_sgn(r+i) > 0; i++) ;
    if (i > k) {
      fmpz_one(g);
      i = 0;
      while (fmpz_is_one(g) && i < k) {
        i++;
        fmpz_gcd(g, r+i, d+i);
      }
      if (fmpz_is_one(g))
        break;
      fmpz_tdiv_q(tmp, d+i, g);
      MATINTsplit(q, tmp, g);
      if (fmpz_cmp_ui(q, 1) > 0) {
        k++;
        if (k > alloc) {
          fmpz *r2 = _fmpz_vec_init(2*alloc+1);
          fmpz *d2 = _fmpz_vec_init(2*alloc+1);
          _fmpz_vec_swap(r2, r, alloc+1);
          _fmpz_vec_swap(d2, d, alloc+1);
          _fmpz_vec_clear(r, alloc+1);
          _fmpz_vec_clear(d, alloc+1);
          r = r2; d = d2;
          alloc *= 2;
        }
        fmpz_mod(r+k, r+i, q);
        fmpz_set(d+k, q);
      }
      fmpz_zero(r+i);
      fmpz_set(d+i, g);
    }
    c++;
  }
  fmpz_set_si(res, c);
  _fmpz_vec_clear(r, alloc+1);
  _fmpz_vec_clear(d, alloc+1);
  fmpz_clear(g); fmpz_clear(q); fmpz_clear(tmp);
}

/* MATINTmgcdex(N, a, v): returns c[1..l] in c (c[0] unused) such that
   gcd(N, a+c[1]*v[1]+...+c[l]*v[l]) = gcd(N, a, v[1], ..., v[l]).
   v is given as array of pointers v[1..l]. */
static void MATINTmgcdex(fmpz *c, const fmpz_t N, const fmpz_t a,
                         fmpz * const *v, slong l)
{
  slong i;
  fmpz *M;
  fmpz_t h, g, b, d, x;

  fmpz_init(h); fmpz_init(g); fmpz_init(b); fmpz_init(d); fmpz_init(x);
  M = _fmpz_vec_init(l+1);
  fmpz_set(h, N);
  for (i = 1; i <= l; i++) {
    fmpz_set(g, h);
    fmpz_gcd(h, g, v[i]);
    fmpz_tdiv_q(M+i, g, h);
  }
  fmpz_gcd(h, a, h);
  fmpz_tdiv_q(g, a, h);

  for (i = l; i >= 1; i--) {
    fmpz_tdiv_q(b, v[i], h);
    MATINTsplit(d, M+i, b);
    if (fmpz_is_one(d)) {
      fmpz_zero(c+i);
    } else {
      /* g/b mod d, b is invertible mod d */
      fmpz_mod(x, b, d);
      fmpz_invmod(x, x, d);
      fmpz_mul(x, x, g);
      fmpz_mod(x, x, d);
      MATINTrgcd(c+i, d, x);
      fmpz_addmul(g, c+i, b);
    }
  }
  _fmpz_vec_clear(M, l+1);
  fmpz_clear(h); fmpz_clear(g); fmpz_clear(b); fmpz_clear(d); fmpz_clear(x);
}

/* MATINTmgcdex(N, a, [b])[1] */
static void MATINTmgcdex1(fmpz_t res, const fmpz_t N, const fmpz_t a,
                          const fmpz_t b)
{
  fmpz *v[2];
  fmpz c[2];
  v[1] = (fmpz *) b;
  fmpz_init(c+1);
  MATINTmgcdex(c, N, a, v, 1);
  fmpz_swap(res, c+1);
  fmpz_clear(c+1);
}

/* MATINTbezout(a, b, c, d): result in e->coeff1..coeff4 */
static void MATINTbezout(gcdex_struct *e, const fmpz_t a, const fmpz_t b,
                         const fmpz_t c, const fmpz_t d)
{
  fmpz_t f, g, q;
  fmpz_init(f); fmpz_init(g); fmpz_init(q);

  Gcdex(e, a, c);
  fmpz_mul(f, e->coeff1, b);
  fmpz_addmul(f, e->coeff2, d);
  fmpz_mul(g, e->coeff3, b);
  fmpz_addmul(g, e->coeff4, d);
  if (fmpz_sgn(g) < 0) {
    fmpz_neg(e->coeff3, e->coeff3);
    fmpz_neg(e->coeff4, e->coeff4);
    fmpz_neg(g, g);
  }
  if (fmpz_sgn(g) > 0) {
    /* q := QuoInt(f - (f mod g), g) */
    fmpz_fdiv_q(q, f, g);
    fmpz_submul(e->coeff1, q, e->coeff3);
    fmpz_submul(e->coeff2, q, e->coeff4);
  }
  fmpz_clear(f); fmpz_clear(g); fmpz_clear(q);
}

/* SNFofREF(T): fast SNF of a matrix T (n x m) in row echelon form,
   works in place */
static void SNFofREF(imat T, slong n, slong m)
{
  slong k, ii, si, i, j, r, t, *piv, *isp;
  fmpz *A, *row;
  fmpz_t d, d2, tt, b, q;
  gcdex_struct g;
  fmpz *v[2];

  fmpz_init(d); fmpz_init(d2); fmpz_init(tt); fmpz_init(b); fmpz_init(q);
  gcdex_init(&g);

  piv = flint_malloc((m+1)*sizeof(slong));
  isp = flint_calloc(m+1, sizeof(slong));
  for (r = 0; r < n; r++) {
    for (j = 1; j <= m && fmpz_is_zero(T[r+1]+j); j++) ;
    if (j > m)
      break;
    piv[r+1] = j;
    isp[j] = 1;
  }
  /* now r is the number of nonzero rows */
  for (i = r+1, j = 1; j <= m; j++)
    if (!isp[j])
      piv[i++] = j;

  /* permute columns of first r rows */
  row = _fmpz_vec_init(m+1);
  for (i = 1; i <= r; i++) {
    for (j = 1; j <= m; j++)
      fmpz_swap(row+j, T[i]+piv[j]);
    _fmpz_vec_swap(row, T[i], m+1);
  }
  _fmpz_vec_clear(row, m+1);

  si = 1;
  A = _fmpz_vec_init(r+1);
  fmpz_set_ui(d, 2);
  for (k = 1; k <= m; k++) {
    if (k <= r) {
      fmpz_abs(tt, T[k]+k);
      fmpz_mul(d, d, tt);
      fmpz_mul_ui(d2, d, 2);
      modrow(T[k], d2, m);
    }

    t = FLINT_MIN(k, r);
    for (i = t-1; i >= si; i--) {
      v[1] = T[i+1]+k;
      MATINTmgcdex1(tt, A+i, T[i]+k, v[1]);
      if (!fmpz_is_zero(tt)) {
        addrow(T[i], T[i+1], tt, 1, m);
        modrow(T[i], A+i, m);
      }
    }

    for (i = si; i <= FLINT_MIN(k-1, r); i++) {
      Gcdex(&g, A+i, T[i]+k);
      fmpz_zero(T[i]+k);
      if (!fmpz_equal(g.gcd, A+i)) {
        fmpz_tdiv_q(b, A+i, g.gcd);
        fmpz_set(A+i, g.gcd);
        for (ii = i+1; ii <= FLINT_MIN(k-1, r); ii++) {
          /* -g.coeff2*QuoInt(T[ii,k],A[i]) mod A[ii] */
          fmpz_tdiv_q(q, T[ii]+k, A+i);
          fmpz_mul(q, q, g.coeff2);
          fmpz_neg(q, q);
          fmpz_mod(q, q, A+ii);
          addrow(T[ii], T[i], q, 1, m);
          fmpz_mul(T[ii]+k, T[ii]+k, b);
          modrow(T[ii], A+ii, m);
        }
        if (k <= r) {
          fmpz_tdiv_q(q, T[k]+k, g.gcd);
          fmpz_mul(q, q, g.coeff2);
          subrow(T[k], T[i], q, 1, m);
          fmpz_mul(T[k]+k, T[k]+k, b);
        }
        modrow(T[i], A+i, m);
        if (fmpz_is_one(A+i))
          si = i+1;
      }
    }

    if (k <= r) {
      fmpz_abs(A+k, T[k]+k);
      modrow(T[k], A+k, m);
    }
  }

  for (i = 1; i <= r; i++)
    fmpz_set(T[i]+i, A+i);

  _fmpz_vec_clear(A, r+1);
  flint_free(piv);
  flint_free(isp);
  fmpz_clear(d); fmpz_clear(d2); fmpz_clear(tt); fmpz_clear(b); fmpz_clear(q);
  gcdex_clear(&g);
}

static slong nthr;

/* Worker: eliminate entries in columns c1 and c2 of row r+2+k using the
   pivot rows r and r+1 */
typedef struct {
  imat A, Q;
  slong r, c1, c2, n, m;
  int opt3;
} elim_args_t;

static void elim_worker(slong k, void *args)
{
  elim_args_t *e = args;
  slong i = e->r+2+k;
  fmpz_t q;
  fmpz_init(q);
  fmpz_tdiv_q(q, e->A[i]+e->c1, e->A[e->r]+e->c1);
  subrow(e->A[i], e->A[e->r], q, 1, e->m);
  if (e->opt3) subrow(e->Q[i], e->Q[e->r], q, 1, e->n);
  fmpz_tdiv_q(q, e->A[i]+e->c2, e->A[e->r+1]+e->c2);
  subrow(e->A[i], e->A[e->r+1], q, 1, e->m);
  if (e->opt3) subrow(e->Q[i], e->Q[e->r+1], q, 1, e->n);
  fmpz_clear(q);
}

/* Worker: Q[i] -= Sum_{j=i+1..jmax} qv[j]*Q[j] on k-th chunk of columns */
typedef struct {
  imat Q;
  fmpz *qv;
  slong i, jmax, n, chunk;
} qupd_args_t;

static void qupd_worker(slong k, void *args)
{
  qupd_args_t *e = args;
  slong j, lo, hi;
  lo = 1 + k*e->chunk;
  hi = FLINT_MIN(lo + e->chunk - 1, e->n);
  for (j = e->i+1; j <= e->jmax; j++)
    subrow(e->Q[e->i], e->Q[j], e->qv+j, lo, hi);
}

/* Worker: for column j = L[k] compute
   cb[j] := MATINTmgcdex(N, A[r,j], A{[r+1..n]}[j]) and
   bv[j] := A[r,j] + cb[j]*A{[r+1..n]}[j] */
typedef struct {
  imat A;
  fmpz **cb, *bv, *N;
  slong *L, r, n;
} smgc_args_t;

static void smgc_worker(slong k, void *args)
{
  smgc_args_t *e = args;
  slong i, j = e->L[k], r = e->r, n = e->n;
  fmpz **v = flint_malloc((n-r+1)*sizeof(fmpz *));
  for (i = r+1; i <= n; i++)
    v[i-r] = e->A[i]+j;
  MATINTmgcdex(e->cb[j], e->N, e->A[r]+j, v, n-r);
  fmpz_set(e->bv+j, e->A[r]+j);
  for (i = r+1; i <= n; i++)
    fmpz_addmul(e->bv+j, e->cb[j]+i-r, e->A[i]+j);
  flint_free(v);
}

/* rows r and r+1 of X (entries 1..len) := [[c1,c2],[c3,c4]] * rows */
static void rows2x2(imat X, slong r, slong len, gcdex_struct *g)
{
  slong j;
  fmpz_t x, y;
  fmpz_init(x); fmpz_init(y);
  for (j = 1; j <= len; j++) {
    fmpz_mul(x, g->coeff1, X[r]+j);
    fmpz_addmul(x, g->coeff2, X[r+1]+j);
    fmpz_mul(y, g->coeff3, X[r]+j);
    fmpz_addmul(y, g->coeff4, X[r+1]+j);
    fmpz_swap(X[r]+j, x);
    fmpz_swap(X[r+1]+j, y);
  }
  fmpz_clear(x); fmpz_clear(y);
}

/* print rows lo..hi, columns lo2..hi2 of X as GAP matrix */
static void printgapmat(FILE *f, imat X, slong lo, slong hi,
                        slong lo2, slong hi2)
{
  slong i, j;
  fprintf(f, "[");
  for (i = lo; i <= hi; i++) {
    fprintf(f, "[");
    for (j = lo2; j <= hi2; j++) {
      fmpz_fprint(f, X[i]+j);
      if (j < hi2)
        fprintf(f, ",");
    }
    fprintf(f, "]");
    if (i < hi)
      fprintf(f, ",\n");
  }
  fprintf(f, "]");
}

/* The main function, mat is nr x nc with nr, nc > 0, rows 1-based.
   Result is printed as GAP record to stdout. mat is destroyed. */
static void DoNFIM(imat mat, slong nr, slong nc, int options)
{
  int opt1, opt2, opt3, opt4, sig, sg;
  slong n, m, r, c1, c2, j, k, i, ll, nL, *rp, *L;
  imat A, C = NULL, Q = NULL, B = NULL, P = NULL;
  fmpz *c, **v, **cb = NULL, *bv = NULL, *qv;
  elim_args_t ea;
  qupd_args_t qa;
  smgc_args_t sa;
  fmpz_t N, a, b, t, tmp, q, x, y;
  gcdex_struct g;

  opt1 = (options & 1) != 0;
  opt2 = (options & 2) != 0;
  opt3 = (options & 4) != 0;
  opt4 = (options & 8) != 0;

  fmpz_init(N); fmpz_init(a); fmpz_init(b); fmpz_init(t);
  fmpz_init(tmp); fmpz_init(q); fmpz_init(x); fmpz_init(y);
  gcdex_init(&g);

  sig = 1;

  /* embed matrix in 2 larger "id" matrix */
  n = nr+2;
  m = nc+2;
  A = flint_malloc((n+1)*sizeof(fmpz *));
  A[0] = NULL;
  for (i = 2; i <= n-1; i++) {
    A[i] = _fmpz_vec_init(m+1);
    _fmpz_vec_swap(A[i]+2, mat[i-1]+1, nc);
  }
  imat_clear(mat, nr, nc);
  A[1] = _fmpz_vec_init(m+1);
  A[n] = _fmpz_vec_init(m+1);
  fmpz_one(A[1]+1);
  fmpz_one(A[n]+m);

  if (opt3) {
    C = imat_identity(n);
    Q = imat_init(n, n);
    fmpz_one(Q[1]+1);
  }
  if (opt1 && opt4) {
    B = imat_identity(m);
    P = imat_identity(m);
  }

  c = _fmpz_vec_init(FLINT_MAX(n, m)+1);
  v = flint_malloc((FLINT_MAX(n, m)+1)*sizeof(fmpz *));
  rp = flint_malloc((m+2)*sizeof(slong));
  L = flint_malloc((m+1)*sizeof(slong));
  qv = _fmpz_vec_init(m+2);
  if (opt1 && (opt4 || opt3)) {
    /* multipliers and values for the columns in Smith with transforms */
    cb = flint_malloc((m+1)*sizeof(fmpz *));
    for (j = 0; j <= m; j++)
      cb[j] = _fmpz_vec_init(n+1);
    bv = _fmpz_vec_init(m+1);
  }

  r = 0;
  c2 = 1;
  k = 0;
  while (m > c2) {
    r++;
    c1 = c2;
    rp[r] = c1;
    if (opt3)
      fmpz_one(Q[r+1]+r+1);

    PROF(10);
    j = c1+1;
    while (j <= m) {
      k = r+1;
      while (k <= n && cross_eq(A[r]+c1, A[k]+j, A[k]+c1, A[r]+j))
        k++;
      if (k <= n) {
        c2 = j;
        j = m;
      }
      j++;
    }

    PROF(1);
    /* Smith with some transforms.. */
    if (opt1 && (opt4 || opt3) && c2 < m) {
      fmpz_zero(N);
      for (i = r; i <= n; i++)
        fmpz_gcd(N, N, A[i]+c2);
      nL = 0;
      for (j = c1+1; j <= c2-1; j++) L[nL++] = j;
      for (j = c2+1; j <= m-1; j++) L[nL++] = j;
      L[nL++] = c2;
      /* the columns L[0..nL-2] do not change in the loop below, so
         compute their multipliers first in parallel */
      PROF(2);
      sa.A = A; sa.cb = cb; sa.bv = bv; sa.N = N;
      sa.L = L; sa.r = r; sa.n = n;
      parallel_do_dyn((do_func_t)smgc_worker, &sa, nL-1, nthr-1,
                      FLINT_PARALLEL_DYNAMIC);
      PROF(12);
      for (ll = 0; ll < nL; ll++) {
        j = L[ll];
        if (j == c2) {
          fmpz_set(b, A[r]+c2);
          fmpz_set(a, A[r]+c1);
          for (i = r+1; i <= n; i++) {
            if (!fmpz_is_one(b)) {
              Gcdex(&g, b, A[i]+c2);
              fmpz_set(b, g.gcd);
              fmpz_mul(a, g.coeff1, a);
              fmpz_addmul(a, g.coeff2, A[i]+c1);
            }
          }
          fmpz_zero(N);
          for (i = r; i <= n; i++) {
            if (!fmpz_is_one(N)) {
              fmpz_tdiv_q(x, A[i]+c2, b);
              fmpz_set(y, A[i]+c1);
              fmpz_submul(y, x, a);
              fmpz_gcd(N, N, y);
            }
          }
        } else {
          fmpz_set(b, bv+j);
          fmpz_set(a, A[r]+c1);
          for (i = r+1; i <= n; i++)
            fmpz_addmul(a, cb[j]+i-r, A[i]+c1);
        }
        MATINTmgcdex1(t, N, a, b);
        fmpz_set(tmp, A[r]+c1);
        fmpz_addmul(tmp, t, A[r]+j);
        while (1) {
          if (!fmpz_is_zero(tmp)) {
            fmpz_mul(x, tmp, A[k]+c2);
            fmpz_set(y, A[k]+c1);
            fmpz_addmul(y, t, A[k]+j);
            fmpz_mul(y, y, A[r]+c2);
            if (!fmpz_equal(x, y))
              break;
          }
          /* t := t+1+MATINTmgcdex(N,a+t*b+b,[b])[1] */
          fmpz_add_ui(x, t, 1);
          fmpz_set(y, a);
          fmpz_addmul(y, x, b);
          MATINTmgcdex1(y, N, y, b);
          fmpz_add(t, x, y);
          fmpz_set(tmp, A[r]+c1);
          fmpz_addmul(tmp, t, A[r]+j);
        }
        if (fmpz_sgn(t) > 0) {
          for (i = 1; i <= n; i++)
            fmpz_addmul(A[i]+c1, t, A[i]+j);
          if (opt4)
            fmpz_add(B[j]+c1, B[j]+c1, t);
        }
      }
      if (cross_eq(A[r]+c1, A[k]+c1+1, A[k]+c1, A[r]+c1+1)) {
        for (i = 1; i <= n; i++)
          fmpz_add(A[i]+c1+1, A[i]+c1+1, A[i]+c2);
        if (opt4)
          fmpz_one(B[c2]+c1+1);
      }
      c2 = c1+1;
    }

    PROF(2);
    fmpz_abs(x, A[r]+c1);
    for (i = r+2; i <= n; i++)
      v[i-r-1] = A[i]+c1;
    MATINTmgcdex(c, x, A[r+1]+c1, v, n-r-1);
    for (i = r+2; i <= n; i++) {
      if (!fmpz_is_zero(c+i-r-1)) {
        addrow(A[r+1], A[i], c+i-r-1, 1, m);
        if (opt3) {
          fmpz_set(C[r+1]+i, c+i-r-1);
          addrow(Q[r+1], Q[i], c+i-r-1, 1, n);
        }
      }
    }

    PROF(3);
    i = r+1;
    while (cross_eq(A[r]+c1, A[i]+c2, A[i]+c1, A[r]+c2))
      i++;
    if (i > r+1) {
      fmpz_abs(x, A[r]+c1);
      fmpz_add(y, A[r+1]+c1, A[i]+c1);
      MATINTmgcdex1(t, x, y, A[i]+c1);
      fmpz_add_ui(t, t, 1);
      addrow(A[r+1], A[i], t, 1, m);
      if (opt3) {
        fmpz_add(C[r+1]+i, C[r+1]+i, t);
        addrow(Q[r+1], Q[i], t, 1, n);
      }
    }

    MATINTbezout(&g, A[r]+c1, A[r]+c2, A[r+1]+c1, A[r+1]+c2);
    fmpz_mul(x, A[r]+c1, A[r+1]+c2);
    fmpz_submul(x, A[r]+c2, A[r+1]+c1);
    sg = fmpz_sgn(x);
    sig = sig*sg;
    rows2x2(A, r, m, &g);
    if (opt3)
      rows2x2(Q, r, n, &g);

    PROF(4);
    ea.A = A; ea.Q = Q; ea.r = r; ea.c1 = c1; ea.c2 = c2;
    ea.n = n; ea.m = m; ea.opt3 = opt3;
    parallel_do_dyn((do_func_t)elim_worker, &ea, n-r-1, nthr-1,
                    FLINT_PARALLEL_DYNAMIC);
    PROF(5);
#ifdef NFIM_PROFILE
    if (r % 100 == 0)
      fprintf(stderr, "r=%ld  maxbits A: %ld%s%ld\n", (long)r,
              (long)maxbits(A, 1, n, m), opt3 ? "  Q: " : "",
              opt3 ? (long)maxbits(Q, 1, n, n) : 0L);
    PROF(10);
#endif
  }
  rp[r+1] = m;
  if (n == m && r+1 < n)
    sig = 0;

  /* smith w/ NO transforms - farm the work out... */
  if (opt1 && !(opt3 || opt4)) {
    for (i = 2; i <= n-1; i++) {
      _fmpz_vec_swap(A[i-1]+1, A[i]+2, m-2);
    }
    SNFofREF(A, n-2, m-2);
    PROF(6);
    printf("TMPRES_NFIM_5830197461 := rec(\nnormal := ");
    printgapmat(stdout, A, 1, n-2, 1, m-2);
    printf(",\nrank := %ld", (long)(r-1));
    if (n == m)
      printf(",\nsigndet := %d", sig);
    printf(");\n");
    PROF(9);
    imat_clear(A, n, m);
    goto cleanup;
  }

  PROF(10);
  /* hermite or (smith w/ column transforms) */
  if ((!opt1 && opt2) || (opt1 && opt4)) {
    qa.Q = Q; qa.qv = qv; qa.n = n; qa.jmax = r+1;
    /* chunks of columns of Q */
    nL = (nthr > 2) ? FLINT_MIN(n, 8*(nthr-1)) : 1;
    qa.chunk = (n + nL - 1)/nL;
    nL = (n + qa.chunk - 1)/qa.chunk;
    for (i = r; i >= 1; i--) {
      for (j = i+1; j <= r+1; j++) {
        /* q := QuoInt(A[i,rp[j]]-(A[i,rp[j]] mod A[j,rp[j]]),A[j,rp[j]]) */
        fmpz_mod(x, A[i]+rp[j], A[j]+rp[j]);
        fmpz_sub(x, A[i]+rp[j], x);
        fmpz_divexact(qv+j, x, A[j]+rp[j]);
        subrow(A[i], A[j], qv+j, 1, m);
      }
      /* the multipliers only depend on A, now apply them to Q */
      if (opt3) {
        qa.i = i;
        parallel_do_dyn((do_func_t)qupd_worker, &qa, nL, nthr-1,
                        FLINT_PARALLEL_DYNAMIC);
      }
      PROF(7);
      if (opt1 && i < r) {
        for (j = i+1; j <= m; j++) {
          fmpz_tdiv_q(q, A[i]+j, A[i]+i);
          if (!fmpz_is_zero(q))
            for (k = 1; k <= i; k++)
              fmpz_submul(A[k]+j, q, A[k]+i);
          if (opt4)
            fmpz_neg(P[i]+j, q);
        }
      }
      PROF(11);
    }
  }

  PROF(7);
  /* Smith w/ row but not col transforms */
  if (opt1 && opt3 && !opt4) {
    for (i = 1; i <= r-1; i++) {
      fmpz_set(x, A[i]+i);
      _fmpz_vec_zero(A[i]+1, m);
      fmpz_set(A[i]+i, x);
    }
    for (j = r+1; j <= m-1; j++) {
      fmpz_gcd(A[r]+r, A[r]+r, A[r]+j);
      fmpz_zero(A[r]+j);
    }
  }

  /* smith w/ col transforms */
  if (opt1 && opt4 && r < m-1) {
    for (j = r+2; j <= m-1; j++)
      v[j-r-1] = A[r]+j;
    MATINTmgcdex(c, A[r]+r, A[r]+r+1, v, m-r-2);
    for (j = r+2; j <= m-1; j++) {
      fmpz_addmul(A[r]+r+1, c+j-r-1, A[r]+j);
      fmpz_set(B[j]+r+1, c+j-r-1);
      for (i = 1; i <= r; i++)
        fmpz_addmul(P[i]+r+1, c+j-r-1, P[i]+j);
    }
    _fmpz_vec_zero(P[r+1]+1, m);
    fmpz_one(P[r+1]+r+1);
    Gcdex(&g, A[r]+r, A[r]+r+1);
    fmpz_set(A[r]+r, g.gcd);
    fmpz_zero(A[r]+r+1);
    for (i = 1; i <= r+1; i++) {
      fmpz_set(t, P[i]+r);
      fmpz_mul(x, P[i]+r, g.coeff1);
      fmpz_addmul(x, P[i]+r+1, g.coeff2);
      fmpz_set(P[i]+r, x);
      fmpz_mul(x, t, g.coeff3);
      fmpz_addmul(x, P[i]+r+1, g.coeff4);
      fmpz_set(P[i]+r+1, x);
    }
    for (j = r+2; j <= m-1; j++) {
      fmpz_tdiv_q(q, A[r]+j, A[r]+r);
      for (i = 1; i <= r+1; i++)
        fmpz_submul(P[i]+j, q, P[i]+r);
      fmpz_zero(A[r]+j);
    }
    for (i = r+2; i <= m-1; i++) {
      _fmpz_vec_zero(P[i]+1, m);
      fmpz_one(P[i]+i);
    }
  }

  /* row transforms finisher */
  if (opt3)
    for (i = r+2; i <= n; i++)
      fmpz_one(Q[i]+i);

  PROF(8);
  printf("TMPRES_NFIM_5830197461 := rec(\nnormal := ");
  printgapmat(stdout, A, 2, n-1, 2, m-1);
  if (opt3) {
    printf(",\nrowC := ");
    printgapmat(stdout, C, 2, n-1, 2, n-1);
    printf(",\nrowQ := ");
    printgapmat(stdout, Q, 2, n-1, 2, n-1);
  }
  if (opt1 && opt4) {
    printf(",\ncolC := ");
    printgapmat(stdout, B, 2, m-1, 2, m-1);
    printf(",\ncolQ := ");
    printgapmat(stdout, P, 2, m-1, 2, m-1);
  }
  printf(",\nrank := %ld", (long)(r-1));
  if (n == m)
    printf(",\nsigndet := %d", sig);
  printf(");\n");

  PROF(9);
  imat_clear(A, n, m);
  if (opt3) {
    imat_clear(C, n, n);
    imat_clear(Q, n, n);
  }
  if (opt1 && opt4) {
    imat_clear(B, m, m);
    imat_clear(P, m, m);
  }

cleanup:
  if (cb != NULL) {
    for (j = 0; j <= m; j++)
      _fmpz_vec_clear(cb[j], n+1);
    flint_free(cb);
    _fmpz_vec_clear(bv, m+1);
  }
  _fmpz_vec_clear(qv, m+2);
  _fmpz_vec_clear(c, FLINT_MAX(n, m)+1);
  flint_free(v);
  flint_free(rp);
  flint_free(L);
  fmpz_clear(N); fmpz_clear(a); fmpz_clear(b); fmpz_clear(t);
  fmpz_clear(tmp); fmpz_clear(q); fmpz_clear(x); fmpz_clear(y);
  gcdex_clear(&g);
}

int main(int argc, char *argv[])
{
  slong nr, nc, i, j;
  int options;
  imat mat;
  mpz_t t;

  if (argc < 3) {
    fprintf(stderr, "usage: nfintmat_threads nrthreads options < inputflintmat\n");
    return 1;
  }
  nthr = FLINT_MAX(1, atol(argv[1]));
  flint_set_num_threads(nthr);
  options = atoi(argv[2]);

  mpz_init(t);
  if (mpz_inp_str(t, stdin, 10) == 0) return 2;
  nr = mpz_get_si(t);
  if (mpz_inp_str(t, stdin, 10) == 0) return 2;
  nc = mpz_get_si(t);
  mpz_clear(t);
  if (nr <= 0 || nc <= 0) {
    fprintf(stderr, "nfintmat: matrix must have positive dimensions\n");
    return 2;
  }
  PROFSTART();
  mat = imat_init(nr, nc);
  for (i = 1; i <= nr; i++)
    for (j = 1; j <= nc; j++)
      if (fmpz_fread(stdin, mat[i]+j) <= 0) {
        fprintf(stderr, "nfintmat: error reading matrix entry\n");
        return 2;
      }

  PROF(0);
  DoNFIM(mat, nr, nc, options);
#ifdef NFIM_PROFILE
  for (i = 0; i < 13; i++)
    if (prof_t[i] > 0)
      fprintf(stderr, "%-26s %10.3f s\n", prof_name[i], prof_t[i]);
#endif
  flint_cleanup();
  return 0;
}

/* 
 * (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
 *
 * This file implements a modular LLL algorithm for unimodular lattices,
 * similar to the GAP function LLLTransformUnimodularGram.
 *
 * It uses FLINT (https://flintlib.org/) for the arithmetic and a thread
 * farm. The main loops are parallelized.
 */
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>
#include <flint/fmpz_mat.h>
#include <flint/nmod_mat.h>
#include <flint/arith.h>
#include <flint/thread_pool.h>
#include <flint/thread_support.h>
#include "do_parallel_dyn.h"

static fmpz_mat_t A, HH, HHi;
static fmpz_t d, M;
static fmpz_t *qlist, *dd, *ddM, *lovasz;
static long *klist;
static long n, nthr;
static uint p;
static fmpz_t pf;

// the content of the inner loop for fraction free Gauss
static void pffworker(long r, void *kp) 
{
  long k = *((long*)kp);
  long i = k+1+r;
  long m;

  for(m=k+1; m<n; m++) {
    fmpz_mul(fmpz_mat_entry(A, i, m), fmpz_mat_entry(A, i, m), fmpz_mat_entry(A, k, k));
    fmpz_submul(fmpz_mat_entry(A, i, m), fmpz_mat_entry(A, k, m), fmpz_mat_entry(A, i, k));
    fmpz_divexact(fmpz_mat_entry(A, i, m), fmpz_mat_entry(A, i, m), d);
  }
  fmpz_zero(fmpz_mat_entry(A, i, k));
}


void printtogaptransposefmpzmat(fmpz_mat_t A, long n, long m)
{
  long i, j;
  flint_printf("[");
  for (i=0; i<m; i++) {
    flint_printf("[");
    for (j=0; j<n; j++) {
      fmpz_print(fmpz_mat_entry(A, j, i));
      if (j < n-1)
        flint_printf(",");
    }
    flint_printf("]");
    if (i < m-1)
      flint_printf(",\n");
  };
  flint_printf("];;\n");
}

// function for fraction free Gauss on A with pivot search of smallest entry
// on diagonal, returns permutation as image list of length n

long * fractionfreegausswithpermutation()
{
  long *perm;
  long k, kk, i;
  fmpz_t min;

  fmpz_init(min);

  perm = (long*) malloc(n*sizeof(long));
  for (k=0; k<n; k++) perm[k] = k;

  // zero-th determinnat is 1
  fmpz_init_set_si(d, 1);
  
  for(k=0; k<n; k++) {
    // find minimal diagonal entry
    for (i = k, kk = i, fmpz_set(min, fmpz_mat_entry(A, i, i)); i < n; i++) {
      if (fmpz_cmp(fmpz_mat_entry(A, i, i), min) < 0) {
        kk = i;
        fmpz_set(min, fmpz_mat_entry(A, i, i));
      }
    }
    if (k != kk) {
      // swap rows and colums k and kk
      fmpz_mat_swap_rows(A, NULL, k, kk);
      fmpz_mat_swap_cols(A, perm, k, kk);
    }
    //  we parallelize the folling loop
    //   for(r=0; r<n-1-k; r++) {
    //     pffworker(r, (void*)(&k));
    //   }
    // options: FLINT_PARALLEL_STRIDED (threads do larger steps instead of
    // intervals, FLINT_PARALLEL_VERBOSE (some infos to see what happens)
//    flint_parallel_do((do_func_t)pffworker, (void*)(&k), n-1-k, 
    parallel_do_dyn((do_func_t)pffworker, (void*)(&k), n-1-k, 
                       //nthr-1, FLINT_PARALLEL_UNIFORM);
                       nthr-1, FLINT_PARALLEL_DYNAMIC);
    fmpz_set(d, fmpz_mat_entry(A, k, k));
  }
  return perm; 
}

// helper for LLL, elementary row operation
// subtract q times row r from row k
static void modsubstractrow(long k, long r, fmpz_t q)
{
   long i, j;

   if (fmpz_is_zero(q)) return;
   // recall that HH is inverse transpose of transform H
   for (j=0; j<n; j++) {
     fmpz_addmul(fmpz_mat_entry(HH, r, j), q, fmpz_mat_entry(HH, k, j));
     fmpz_smod(fmpz_mat_entry(HH, r, j), fmpz_mat_entry(HH, r, j), M);
   }
   for (i=0; i<=r; i++) {
     fmpz_submul(fmpz_mat_entry(A, i, k), q, fmpz_mat_entry(A, i, r));
     fmpz_smod(fmpz_mat_entry(A, i, k), fmpz_mat_entry(A, i, k), ddM[i]);
   }
}

// helper for LLL, swap vectors number k and k-1
static void modswitchrow(long k)
{
  long j;
  fmpz_t x, y, z, d, s, t;

  // just swap rows in HH
  fmpz_mat_swap_rows(HH, NULL, k, k-1);

  // in A we need linear combinations of rows k and k-1
  fmpz_init_set(y, fmpz_mat_entry(A, k, k-1));
  fmpz_init_set(z, fmpz_mat_entry(A, k-1, k-1));
  fmpz_init_set(d, fmpz_mat_entry(A, k-1, k));
  fmpz_init(s);
  fmpz_init(t);
  for (j=k-1; j<n; j++) {
    fmpz_mul(s, dd[k-1], fmpz_mat_entry(A, k, j));
    fmpz_addmul(s, z, fmpz_mat_entry(A, k-1, j));
    fmpz_divexact(s, s, d);
    fmpz_smod(s, s, ddM[k-1]);
    fmpz_mul(t, y, fmpz_mat_entry(A, k-1, j));
    fmpz_submul(t, z, fmpz_mat_entry(A, k, j));
    fmpz_divexact(t, t, d);
    fmpz_smod(t, t, ddM[k]);
    fmpz_set(fmpz_mat_entry(A, k-1, j), s);
    fmpz_set(fmpz_mat_entry(A, k, j), t);
    if (j == k-1) {
      // adjust dd and ddM
      fmpz_set(dd[k], s);
      fmpz_mul(ddM[k-1], dd[k-1], dd[k]);
      fmpz_mul(ddM[k-1], ddM[k-1], M);
      fmpz_mul(ddM[k], dd[k], dd[k+1]);
      fmpz_mul(ddM[k], ddM[k], M);
    }
  }
  // adjust lovasz
  for (j=k-1; j<=k+1; j++) {
    if (j>0 && j<n) {
      fmpz_mul(lovasz[2*j], dd[j-1], dd[j+1]);
      fmpz_smod(lovasz[2*j+1], fmpz_mat_entry(A, j-1, j), dd[j]);
      fmpz_addmul(lovasz[2*j], lovasz[2*j+1], lovasz[2*j+1]);
      fmpz_mul(lovasz[2*j+1], dd[j], dd[j]);
    }
  }
  fmpz_clear(y);
  fmpz_clear(z);
  fmpz_clear(d);
  fmpz_clear(s);
  fmpz_clear(t);
}

// the content of the inner loop for LLL as worker function
static void lllworker1(long i, void *kp)
{
  long k, j;
  fmpz_t x;
  fmpz_init(x);

  k = klist[i];
  modsubstractrow(k, k-1, qlist[i]);
  // now swap columns k and k-1
  for (i=0; i<=k; i++) {
    fmpz_set(x, fmpz_mat_entry(A, i, k));
    fmpz_set(fmpz_mat_entry(A, i, k), fmpz_mat_entry(A, i, k-1));
    fmpz_set(fmpz_mat_entry(A, i, k-1), x);
  }
  fmpz_clear(x);
}
static void lllworker2(long i, void *kp)
{
  long k, j;

  k = klist[i];
  modswitchrow(k);
}

void llltransformunimodulargram( )
{
  fmpz_t max, x, y;
  long e, i, j, k, c;
  long *perm;

  fmpz_init(M);
  fmpz_init(max);
  fmpz_init(x);
  fmpz_init(y);

  // largest diagonal entry of Gram matrix
  // and modulus M for result matrix HH
  for (i = 0, fmpz_set(max, fmpz_mat_entry(A, i, i)); i < n; i++) {
    if (fmpz_cmp(fmpz_mat_entry(A, i, i), max) > 0) {
      fmpz_set(max, fmpz_mat_entry(A, i, i));
    }
  }
  e = fmpz_flog_ui(max, 2)/2 + 2;
  fmpz_set_ui(M, 2);
  fmpz_pow_ui(M, M, e);

  // fraction free Gauss
  // (we change the input matrix in place)
  perm = fractionfreegausswithpermutation();

  // initialize result matrix
  fmpz_mat_init(HH, n, n);
  for (i=0; i<n; i++)
     fmpz_set_si(fmpz_mat_entry(HH, i, perm[i]), 1);

  // initialize list of determinants of minors, moduli for rows of T,
  // numerators and denominators for Lovasz condition
  dd = (fmpz_t*)malloc((n+1)*sizeof(fmpz_t));
  for (i=0; i<=n; i++) fmpz_init(dd[i]);
  ddM = (fmpz_t*)malloc((n)*sizeof(fmpz_t));
  for (i=0; i<n; i++) fmpz_init(ddM[i]);
  lovasz = (fmpz_t*)malloc(2*n*sizeof(fmpz_t));
  for (i=0; i<2*n; i++) fmpz_init(lovasz[i]);
  fmpz_set_ui(dd[0], 1);
  fmpz_set(dd[1], fmpz_mat_entry(A, 0, 0));
  fmpz_mul(ddM[0], dd[1], M);
  for (i=1; i<n; i++) {
    fmpz_set(dd[i+1], fmpz_mat_entry(A,i,i));
    fmpz_mul(x, dd[i], dd[i+1]);
    fmpz_mul(ddM[i], x, M);
    fmpz_mul(lovasz[2*i], dd[i-1], dd[i+1]);
    fmpz_smod(x, fmpz_mat_entry(A, i-1, i), dd[i]);
    fmpz_addmul(lovasz[2*i], x, x);
    fmpz_mul(lovasz[2*i+1], dd[i], dd[i]);
  }

  // initialize klist and qlist
  klist = (long*)malloc((n)*sizeof(long));
  qlist = (fmpz_t*)malloc((n)*sizeof(fmpz_t));
  for (i=0; i<n; i++) fmpz_init(qlist[i]);
  
  // the main loop
  while (1) {
    // determine list of positions k that can be swapped independently
    for (k=n-1, c=0; k > 0; ){
      if (fmpz_cmp(lovasz[2*k+1], lovasz[2*k]) > 0) {
        klist[c] = k;
        c++;
        k -= 3;
      } else {
        k--;
      }
    }
    // done when klist is empty (no further LLL improvement possible)
    if (c == 0) break;
    
    // find the multipliers for row reductions
    for (i=0; i<c; i++) {
      k = klist[i];
      fmpz_ndiv_qr(qlist[i], x, fmpz_mat_entry(A, k-1, k), dd[k]);
    }
    
    // the main inner loop (can be done in parallel)
    /*
    for (i=0; i<c; i++) {
      k = klist[i];
      modsubstractrow(k, k-1, qlist[i], 1);
      modswitchrow(k);
      // adjust lovasz
      for (j=k-1; j<=k+1; j++) {
        if (j>0 && j<n) {
          fmpz_mul(lovasz[2*j], dd[j-1], dd[j+1]);
          fmpz_smod(x, fmpz_mat_entry(A, j-1, j), dd[j]);
          fmpz_addmul(lovasz[2*j], x, x);
          fmpz_mul(lovasz[2*j+1], dd[j], dd[j]);
        }
      }
    }
    */
    // more infos about threads with | FLINT_PARALLEL_VERBOSE
    // here FLINT_PARALLEL_STRIDED is better than FLINT_PARALLEL_UNIFORM
/*    flint_parallel_do((do_func_t)lllworker1, NULL, c, 
                       nthr-1, FLINT_PARALLEL_STRIDED);
    flint_parallel_do((do_func_t)lllworker2, NULL, c, 
                       nthr-1, FLINT_PARALLEL_STRIDED); */
    parallel_do_dyn((do_func_t)lllworker1, NULL, c, 
                       nthr-1, FLINT_PARALLEL_DYNAMIC);
    parallel_do_dyn((do_func_t)lllworker2, NULL, c, 
                       nthr-1, FLINT_PARALLEL_DYNAMIC);
  }

  // the final size reductions
  for (k=1; k<n; k++) {
    for (j=k-1; j>=0; j--) {
      fmpz_ndiv_qr(x, y, fmpz_mat_entry(A, j, k), fmpz_mat_entry(A, j, j));
      modsubstractrow(k, j, x);
    }
  }
  fmpz_clear(M);
  fmpz_clear(max);
  fmpz_clear(x);
  fmpz_clear(y);
  free(perm);
}

// main loop to invert unimodular matrix HH as worker function
// (computes i-th row of result and stores it in A)
static void invworker(long i, void *kp) 
{
  fmpz *v, *r, *x, *y;
  fmpz_t pi;
  int j, notdone;

  fmpz_init_set_si(pi, 1);
  v = _fmpz_vec_init(n);
  _fmpz_vec_zero(v, n);
  fmpz_set_si(v+i, 1);
  r = _fmpz_vec_init(n);
  _fmpz_vec_zero(r, n);
  x = _fmpz_vec_init(n);
  y = _fmpz_vec_init(n);
  
  for (notdone=1; notdone; notdone = !_fmpz_vec_is_zero(v, n)){
    fmpz_mat_fmpz_vec_mul(y, v, n, HHi);
    _fmpz_vec_scalar_smod_fmpz(x, y, n, pf);
    _fmpz_vec_scalar_addmul_fmpz(r, x, n, pi);
    fmpz_mul(pi, pf, pi);
    fmpz_mat_fmpz_vec_mul(y, x, n, HH);
    _fmpz_vec_sub(v, v, y, n);
    _fmpz_vec_scalar_divexact_ui(v, v, n, p);
  }
  for (j=0; j < n; j++)
    fmpz_set(fmpz_mat_entry(A, i, j), r+j);
}
// and here is the main inversion function of unimodular matrix HH
// result is written into A
void invertunimodular( )
{
  long i;
  nmod_mat_t Ap, Aip;

  // first invert HH modulo largest prime < 2^32
  p = 4294967291;
  // entries of HH mod p
  nmod_mat_init(Ap, n, n, p);
  fmpz_mat_get_nmod_mat(Ap, HH);
  fmpz_init_set_ui(pf, p);

  // invert mod p matrix
  nmod_mat_init(Aip, n, n, p);
  nmod_mat_inv(Aip, Ap);
  nmod_mat_clear(Ap);

  // write entries of inverse as integers
  fmpz_mat_init(HHi, n, n);
  fmpz_mat_set_nmod_mat(HHi, Aip);
  nmod_mat_clear(Aip);

  fmpz_mat_zero(A);
  // compute result row-wise with p-adic expansion
  parallel_do_dyn((do_func_t)invworker, NULL, n, 
                       nthr-1, FLINT_PARALLEL_DYNAMIC);
}

int main(int argc, char* argv[])
{
  long  m, i, k, r;
  long *perm;


  n = atol(argv[1]);

  // read and set number of threads
  nthr = atol(argv[2]);
  flint_set_num_threads(nthr);

  // initialize and read main matrix A
  fmpz_mat_init(A, n, n);
  fmpz_mat_read(A);
  
  // compute inverse transpose of result into matrix HH
  llltransformunimodulargram();

  // invert unimodular matrix HH into A
  invertunimodular();
  fmpz_mat_clear(HH);

  // GAP readable print of result
  printf("TMPRES03695464:=rec();\nTMPRES03695464.H:= \n");
  printtogaptransposefmpzmat(A, n, n);

  fmpz_clear(d);
  fmpz_mat_clear(A);

  return 0;
}

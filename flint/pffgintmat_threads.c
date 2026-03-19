/* 
 * (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
 *
 * This file implements a parallelized version of fraction free Gauss
 * algorithm for integer matrices (with permutations to minimize the
 * minors).  This is similar to the GAP function 
 * PermutedFractionFreeIntegerGaussPositiveDefinite
 *
 * It uses FLINT (https://flintlib.org/) for the arithmetic and a thread
 * farm. 
 */

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mat.h>
#include <flint/arith.h>
#include <flint/thread_support.h>
#include "do_parallel_dyn.h"

static fmpz_mat_t A;
static fmpz_t d;
static long n, nthr;

static void worker(long r, void *kp) 
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

void printtogapfmpzmat(fmpz_mat_t A, long n, long m)
{
  long i, j;
  flint_printf("[");
  for (i=0; i<n; i++) {
    flint_printf("[");
    for (j=0; j<m; j++) {
      fmpz_print(fmpz_mat_entry(A, i, j));
      if (j < m-1)
        flint_printf(",");
    }
    flint_printf("]");
    if (i < n-1)
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
    //     worker(r, (void*)(&k));
    //   }
    // options: FLINT_PARALLEL_STRIDED (threads do larger steps instead of
    // intervals, FLINT_PARALLEL_VERBOSE (some infos to see what happens)
    //flint_parallel_do((do_func_t)worker, (void*)(&k), n-1-k, nthr-1, FLINT_PARALLEL_UNIFORM);
    parallel_do_dyn((do_func_t)worker, (void*)(&k), n-1-k, nthr-1, FLINT_PARALLEL_DYNAMIC);
    fmpz_set(d, fmpz_mat_entry(A, k, k));
  }
  return perm; 
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
  
  // start with fraction free Gauss
  perm = fractionfreegausswithpermutation();

  // GAP readable print of result
  printf("TMPRES774684629486 := rec();;\nTMPRES774684629486.perm:= [");
  for (i=0; i<n; i++)
    printf("%ld, ", perm[i]+1);
  printf("];;\nTMPRES774684629486.A:= \n");
  printtogapfmpzmat(A, n, n);

  fmpz_clear(d);
  fmpz_mat_clear(A);
  free(perm);

  return 0;
}

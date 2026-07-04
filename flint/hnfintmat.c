

/* compute Hermite normal form  of an integer matrix 
       hnfintmat nrthreads nrows ncols  < inputflintmat > outputgapmat 

   compile with
       gcc -O3 -march=native -mavx2 -o hnfintmat hnfintmat.c do_parallel_dyn.c -lflint -lgmp
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


static long nrow, ncol, nthr;
static fmpz_mat_t A;


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

int main(int argc, char* argv[])
{

  nthr = atol(argv[1]);
  flint_set_num_threads(nthr);

  nrow = atol(argv[2]);
  ncol = atol(argv[3]);
  fmpz_mat_init(A, nrow, ncol);
  fmpz_mat_read(A);

  /* do the work */
  fmpz_mat_hnf(A, A);

  printf("TMPRES9676895304721:=rec();\nTMPRES9676895304721.hnf := \n");
  printtogapfmpzmat(A, nrow, ncol);
  printf(";\n\n");

  return 0;
}




/* compute inverse of a unimodular matrix 
       invuni nrthreads len p < inputflintmat > outputgapmat 
   maximal p is 4294967291    

   compile with
       gcc -O3 -march=native -mavx2 -o invuni_threads invuni_threads.c do_parallel_dyn.c -lflint -lgmp
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


static long n, nthr;
static uint p;
static fmpz_t pf;
static fmpz_mat_t A, Ai, res;

// compute i-th row of inverse of A
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
    fmpz_mat_fmpz_vec_mul(y, v, n, Ai);
    _fmpz_vec_scalar_smod_fmpz(x, y, n, pf);
    _fmpz_vec_scalar_addmul_fmpz(r, x, n, pi);
    fmpz_mul(pi, pf, pi);
    fmpz_mat_fmpz_vec_mul(y, x, n, A);
    _fmpz_vec_sub(v, v, y, n);
    _fmpz_vec_scalar_divexact_ui(v, v, n, p);
  }
  for (j=0; j < n; j++)
    fmpz_set(fmpz_mat_entry(res, i, j), r+j);
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

int main(int argc, char* argv[])
{
  long i;
  nmod_mat_t Ap, Aip;

  nthr = atol(argv[1]);
  flint_set_num_threads(nthr);

  n = atol(argv[2]);
  fmpz_mat_init(A, n, n);
  fmpz_mat_read(A);

  p = atol(argv[3]);
  nmod_mat_init(Ap, n, n, p);
  fmpz_mat_get_nmod_mat(Ap, A);
  fmpz_init_set_ui(pf, p);

  nmod_mat_init(Aip, n, n, p);
  nmod_mat_inv(Aip, Ap);
  nmod_mat_clear(Ap);

  fmpz_mat_init(Ai, n, n);
  fmpz_mat_set_nmod_mat(Ai, Aip);
  nmod_mat_clear(Aip);

  fmpz_mat_init(res, n, n);

  //for (i=0; i < n; i++)
  //  invworker(i, NULL);
  parallel_do_dyn((do_func_t)invworker, NULL, n, 
                       nthr-1, FLINT_PARALLEL_DYNAMIC);

  printf("TMPRES897966487097:=rec();\nTMPRES897966487097.invmat := \n");
  printtogapfmpzmat(res, n, n);
  printf(";\n\n");

  return 0;
}


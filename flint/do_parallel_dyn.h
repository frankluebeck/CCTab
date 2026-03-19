/* 
 * (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
 *
 * This file implements the missing case FLINT_PARALLEL_DYNAMIC
 * of the FLINT (https://flintlib.org/) function flint_parallel_do()
 */
void parallel_do_dyn(do_func_t f, void * args, slong n, int thread_limit, int flags);


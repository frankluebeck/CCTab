/* 
 * (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
 *
 * This file implements the missing case FLINT_PARALLEL_DYNAMIC
 * of the FLINT (https://flintlib.org/) function flint_parallel_do()
 */
#include <flint/flint.h>
#include <flint/thread_pool.h>
#include <flint/thread_support.h>
#include "do_parallel_dyn.h"

/*  ====================================================================== */
// dynamic variant of flint_parallel_do
//
// Note that 'mutex' must be initialized explicitly: with glibc a zero filled
// pthread_mutex_t happens to be the same as PTHREAD_MUTEX_INITIALIZER, but
// on other systems (e.g. macOS) it is not, and there pthread_mutex_lock()
// then fails with EINVAL and does not lock anything at all.
static slong next_i;
static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

typedef struct
{
    do_func_t f;
    void * args;
    slong a;
    slong b;
    slong step;
}
work_chunk_t;

static void
worker(void * _work)
{
    work_chunk_t work = *((work_chunk_t *) _work);
    slong i;

    for (i = work.a; i < work.b; i += work.step)
        work.f(i, work.args);
}
static void
worker_dyn(void * _work)
{
    work_chunk_t work = *((work_chunk_t *) _work);
    slong i, n;

    n = work.b;
    for (i = work.a; i < n; ) {
        work.f(i, work.args);
        pthread_mutex_lock(&mutex);
        i = next_i;
        next_i++;
        pthread_mutex_unlock(&mutex);
    }
}

void parallel_do_dyn(do_func_t f, void * args, slong n, int thread_limit, int flags)
{
    slong i;

    if (thread_limit <= 0)
        thread_limit = flint_get_num_threads();

    thread_limit = FLINT_MIN(thread_limit, n);

    if (thread_limit <= 1)
    {
        for (i = 0; i < n; i++)
            f(i, args);
    }
    else
    {
        slong i, num_threads, num_workers;
        thread_pool_handle * handles;

        num_workers = flint_request_threads(&handles, thread_limit);
        num_threads = num_workers + 1;

        if (flags & FLINT_PARALLEL_VERBOSE)
            flint_printf("parallel_do with num_threads = %wd\n", num_threads);

        if (num_workers < 1)
        {
            flint_give_back_threads(handles, num_workers);

            for (i = 0; i < n; i++)
                f(i, args);
        }
        else
        {
            work_chunk_t * work;
            slong chunk_size;
            TMP_INIT;
            TMP_START;

            work = TMP_ALLOC(num_threads * sizeof(work_chunk_t));

            if (flags & FLINT_PARALLEL_STRIDED)
            {
                for (i = 0; i < num_threads; i++)
                {
                    work[i].f = f;
                    work[i].args = args;
                    work[i].a = i;
                    work[i].b = n;
                    work[i].step = num_threads;
                }
            }
            else if (flags & FLINT_PARALLEL_UNIFORM)
            {
                chunk_size = (n + num_threads - 1) / num_threads;

                for (i = 0; i < num_threads; i++)
                {
                    work[i].f = f;
                    work[i].args = args;
                    work[i].a = i * chunk_size;
                    work[i].b = FLINT_MIN((i + 1) * chunk_size, n);
                    work[i].step = 1;
                }
            }
            else 
            {   // FLINT_PARALLEL_DYNAMIC   case
                for (i = 0; i < num_threads; i++)
                {
                    work[i].f = f;
                    work[i].args = args;
                    work[i].a = i;
                    work[i].b = n;
                    work[i].step = -1;
                }
            }

            if (flags & FLINT_PARALLEL_VERBOSE)
            {
                for (i = 0; i < num_threads; i++)
                {
                    flint_printf("thread #%wd allocated a = %wd, b = %wd, step = %wd\n", i, work[i].a, work[i].b, work[i].step);
                }
            }

            if (flags & FLINT_PARALLEL_DYNAMIC)
            {
                pthread_mutex_lock(&mutex);
                next_i = num_workers+1;
                for (i = 0; i < num_workers; i++)
                    thread_pool_wake(global_thread_pool, handles[i], 0, worker_dyn, &work[i]);
                pthread_mutex_unlock(&mutex);

                worker_dyn(&work[num_workers]);
            }
            else
            {
                for (i = 0; i < num_workers; i++)
                    thread_pool_wake(global_thread_pool, handles[i], 0, worker, &work[i]);

                worker(&work[num_workers]);
            }

            for (i = 0; i < num_workers; i++)
                thread_pool_wait(global_thread_pool, handles[i]);

            flint_give_back_threads(handles, num_workers);
            TMP_END;
        }
    }
}
/*  ====================================================================== */


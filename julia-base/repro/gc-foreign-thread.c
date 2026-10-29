/* Julia @cfunction wrappers perform adoption and GC-state transitions. This
 * helper only creates and joins pthreads; it never calls jl_* from C threads. */
#include <errno.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef uint64_t (*callback_t)(uint64_t, int, int);

typedef struct {
    callback_t callback;
    uint64_t seed;
    uint64_t checksum;
    int worker;
    int round;
    int failed;
} context_t;

static void *run_callback(void *argument)
{
    context_t *context = argument;
    uint64_t first = context->callback(context->seed, context->worker, 2 * context->round);
    uint64_t second = context->callback(context->seed, context->worker, 2 * context->round + 1);
    context->checksum = first ^ second;
    context->failed = first == 0 || second == 0;
    return NULL;
}

int gc_stress_foreign(callback_t callback, uint64_t seed, int workers,
                      int rounds, uint64_t *checksums)
{
    if (callback == NULL || checksums == NULL || workers < 1 || rounds < 1)
        return EINVAL;
    pthread_t *threads = calloc((size_t)workers, sizeof(*threads));
    context_t *contexts = calloc((size_t)workers, sizeof(*contexts));
    if (threads == NULL || contexts == NULL) {
        free(threads);
        free(contexts);
        return ENOMEM;
    }
    int result = 0;
    for (int round = 0; round < rounds && result == 0; round++) {
        int started = 0;
        for (int worker = 0; worker < workers; worker++) {
            contexts[worker] = (context_t){callback, seed, 0, worker, round, 0};
            result = pthread_create(&threads[worker], NULL, run_callback, &contexts[worker]);
            if (result != 0) {
                fprintf(stderr, "pthread_create failed: %d\n", result);
                break;
            }
            started++;
        }
        for (int worker = 0; worker < started; worker++) {
            int joined = pthread_join(threads[worker], NULL);
            if (joined != 0) {
                /* A failed join cannot establish that contexts are unused. */
                fprintf(stderr, "pthread_join failed: %d\n", joined);
                exit(2);
            }
            checksums[worker] ^= contexts[worker].checksum;
            if (contexts[worker].failed) {
                fprintf(stderr, "callback reported an invalid payload\n");
                result = EDOM;
            }
        }
    }
    free(threads);
    free(contexts);
    return result;
}

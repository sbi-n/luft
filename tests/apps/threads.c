// LUFT: {"args": ["threads"], "skip": ["x86_64-pe"]}
// POSIX threads: workers that share a mutex-protected total, a producer and consumers on a condition variable,
// thread-specific data, thread-local variables, pthread_once, recursive locking, and results passed through join.
// Every line printed is the same whatever order the threads run in.
#include <errno.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static long total;
static _Thread_local int localCounter = 5;
static pthread_key_t key;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static int onceCalls;

static void initOnce(void) { ++onceCalls; }

static void* worker(void* argument) {
    long id = (long)(intptr_t)argument;
    pthread_once(&once, initOnce);
    pthread_setspecific(key, (void*)(intptr_t)(id * 10));
    for (int i = 0; i < 1000; ++i) {
        pthread_mutex_lock(&lock);
        total += id;
        pthread_mutex_unlock(&lock);
        if (i % 100 == 0) sched_yield();
        localCounter += 1;
    }
    errno = (int)id;
    sched_yield();
    long result = (long)(intptr_t)pthread_getspecific(key) + localCounter + (errno == (int)id ? 1 : 0);
    return (void*)(intptr_t)result;
}

#define SLOTS 4
static int queue[SLOTS], head, tail, count, done;
static pthread_cond_t notEmpty = PTHREAD_COND_INITIALIZER, notFull = PTHREAD_COND_INITIALIZER;
static long consumed;

static void* producer(void* argument) {
    (void)argument;
    for (int value = 1; value <= 200; ++value) {
        pthread_mutex_lock(&lock);
        while (count == SLOTS) pthread_cond_wait(&notFull, &lock);
        queue[tail] = value;
        tail = (tail + 1) % SLOTS;
        ++count;
        pthread_cond_signal(&notEmpty);
        pthread_mutex_unlock(&lock);
    }
    pthread_mutex_lock(&lock);
    done = 1;
    pthread_cond_broadcast(&notEmpty);
    pthread_mutex_unlock(&lock);
    return NULL;
}

static void* consumer(void* argument) {
    long* mine = argument;
    for (;;) {
        pthread_mutex_lock(&lock);
        while (count == 0 && !done) pthread_cond_wait(&notEmpty, &lock);
        if (count == 0 && done) {
            pthread_mutex_unlock(&lock);
            return NULL;
        }
        int value = queue[head];
        head = (head + 1) % SLOTS;
        --count;
        consumed += value;
        *mine += 1;
        pthread_cond_signal(&notFull);
        pthread_mutex_unlock(&lock);
    }
}

int main(void) {
    pthread_key_create(&key, NULL);
    pthread_t threads[4];
    for (long i = 0; i < 4; ++i)
        if (pthread_create(&threads[i], NULL, worker, (void*)(intptr_t)(i + 1)) != 0) return 1;
    long results = 0;
    for (int i = 0; i < 4; ++i) {
        void* value;
        pthread_join(threads[i], &value);
        results += (long)(intptr_t)value;
    }
    printf("workers total %ld results %ld once %d main local %d main key %p\n", total, results, onceCalls, localCounter,
        pthread_getspecific(key));

    pthread_t made, used[3];
    long counts[3] = {0, 0, 0};
    pthread_create(&made, NULL, producer, NULL);
    for (int i = 0; i < 3; ++i) pthread_create(&used[i], NULL, consumer, &counts[i]);
    pthread_join(made, NULL);
    for (int i = 0; i < 3; ++i) pthread_join(used[i], NULL);
    printf("consumed %ld items %ld\n", consumed, counts[0] + counts[1] + counts[2]);

    pthread_mutexattr_t attributes;
    pthread_mutexattr_init(&attributes);
    pthread_mutexattr_settype(&attributes, PTHREAD_MUTEX_RECURSIVE);
    pthread_mutex_t recursive;
    pthread_mutex_init(&recursive, &attributes);
    pthread_mutex_lock(&recursive);
    pthread_mutex_lock(&recursive);
    printf("recursive %d %d\n", pthread_mutex_unlock(&recursive), pthread_mutex_unlock(&recursive));
    printf("equal %d %d\n", pthread_equal(pthread_self(), pthread_self()) != 0, pthread_equal(pthread_self(), made) != 0);
    return 0;
}

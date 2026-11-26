// LUFT: {"args": ["threads_cpp"], "skip": ["x86_64-pe"]}
// C++ threads: std::thread with mutexes, condition variables, atomics, thread_local, futures, and a thread pool
// whose workers wait for tasks. Every line printed is the same whatever order the threads run in.
#include <atomic>
#include <condition_variable>
#include <cstdio>
#include <functional>
#include <future>
#include <mutex>
#include <numeric>
#include <queue>
#include <thread>
#include <vector>

thread_local int perThread = 100;

class Pool {
public:
    explicit Pool(int size) {
        for (int i = 0; i < size; ++i)
            workers.emplace_back([this] {
                for (;;) {
                    std::function<void()> task;
                    {
                        std::unique_lock<std::mutex> hold(lock);
                        ready.wait(hold, [this] { return stopping || !tasks.empty(); });
                        if (stopping && tasks.empty()) return;
                        task = std::move(tasks.front());
                        tasks.pop();
                    }
                    task();
                }
            });
    }
    ~Pool() {
        {
            std::lock_guard<std::mutex> hold(lock);
            stopping = true;
        }
        ready.notify_all();
        for (auto& worker : workers) worker.join();
    }
    void submit(std::function<void()> task) {
        {
            std::lock_guard<std::mutex> hold(lock);
            tasks.push(std::move(task));
        }
        ready.notify_one();
    }

private:
    std::vector<std::thread> workers;
    std::queue<std::function<void()>> tasks;
    std::mutex lock;
    std::condition_variable ready;
    bool stopping = false;
};

int main() {
    std::atomic<long> sum{0};
    std::mutex lock;
    std::vector<int> seen;
    std::vector<std::thread> threads;
    for (int i = 1; i <= 6; ++i)
        threads.emplace_back([&, i] {
            perThread += i;
            sum.fetch_add(perThread, std::memory_order_relaxed);
            std::lock_guard<std::mutex> hold(lock);
            seen.push_back(i);
        });
    for (auto& thread : threads) thread.join();
    std::printf("threads sum %ld seen %d main local %d\n", sum.load(), int(seen.size()), perThread);

    auto future = std::async(std::launch::async, [] { return 6 * 7; });
    std::printf("async %d\n", future.get());

    std::atomic<int> completed{0};
    long total = 0;
    std::mutex totalLock;
    {
        Pool pool(3);
        for (int i = 1; i <= 50; ++i)
            pool.submit([&, i] {
                std::lock_guard<std::mutex> hold(totalLock);
                total += i * i;
                completed.fetch_add(1);
            });
    }
    std::printf("pool %d %ld\n", completed.load(), total);
    return 0;
}

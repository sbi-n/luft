// LUFT: {"args": ["exceptions", "2"]}
// C++ exceptions: throws through frames with destructors, catches by base class and value, rethrows, throws
// from catch blocks, deep recursion, virtual calls, and many throws caught in one frame.
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <new>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
struct Tracer {
    const char* name;
    explicit Tracer(const char* name) : name(name) { std::printf("enter %s\n", name); }
    ~Tracer() { std::printf("leave %s\n", name); }
};

struct Custom {
    int code;
};

[[gnu::noinline]] int thrower(int kind) {
    Tracer tracer("thrower");
    switch (kind) {
    case 0: throw std::runtime_error("runtime");
    case 1: throw std::out_of_range("range");
    case 2: throw Custom{42};
    case 3: throw 7;
    case 4: {
        // Thrown by the C++ library itself.
        std::vector<int> values(3);
        return values.at(std::size_t(kind) * 10);
    }
    case 5: throw std::string("text");
    default: return kind;
    }
}

[[gnu::noinline]] int middle(int kind) {
    Tracer tracer("middle");
    std::string text = "temporary";
    return thrower(kind) + int(text.size());
}

int classify(int kind) {
    try {
        return middle(kind);
    } catch (const std::out_of_range&) {
        std::printf("out_of_range\n");
        return -1;
    } catch (const std::exception& error) {
        std::printf("exception: %s\n", error.what());
        return -2;
    } catch (const Custom& custom) {
        std::printf("custom %d\n", custom.code);
        return -3;
    } catch (...) {
        std::printf("unknown\n");
        return -4;
    }
}

[[gnu::noinline]] void rethrower() {
    try {
        thrower(0);
    } catch (...) {
        std::printf("rethrowing\n");
        throw;
    }
}

[[gnu::noinline]] int nested() {
    try {
        try {
            thrower(2);
        } catch (const Custom& custom) {
            std::printf("inner custom %d\n", custom.code);
            throw std::logic_error("from catch");
        }
    } catch (const std::logic_error& error) {
        std::printf("outer %s\n", error.what());
        return 1;
    }
    return 0;
}

int live = 0;

struct Counted {
    Counted() { ++live; }
    ~Counted() { --live; }
};

[[gnu::noinline]] int recurse(int depth) {
    Counted counted;
    if (depth == 0)
        throw depth + 1000;
    return recurse(depth - 1) + 1;
}

struct Base {
    virtual ~Base() = default;
    virtual int run(int value) = 0;
};

struct Derived : Base {
    int run(int value) override {
        if (value > 2)
            throw std::invalid_argument("virtual " + std::to_string(value));
        return value * 2;
    }
};

[[gnu::noinline]] int viaPointer(int (*function)(int), int value) {
    return function(value);
}
}

int main(int argc, char** argv) {
    const int scale = argc > 1 ? std::atoi(argv[1]) : 1;
    for (int kind = 0; kind <= 6; ++kind)
        std::printf("classify %d -> %d\n", kind, classify(kind));
    try {
        rethrower();
    } catch (const std::runtime_error& error) {
        std::printf("caught rethrow %s\n", error.what());
    }
    std::printf("nested %d\n", nested());
    try {
        recurse(40);
    } catch (int value) {
        std::printf("recursion unwound with %d, %d live\n", value, live);
    }
    std::unique_ptr<Base> object = std::make_unique<Derived>();
    for (int value = 1; value <= 4; ++value) {
        try {
            std::printf("run %d -> %d\n", value, object->run(value));
        } catch (const std::invalid_argument& error) {
            std::printf("caught %s\n", error.what());
        }
    }
    try {
        viaPointer([](int value) -> int { throw value * 3; }, 5);
    } catch (int value) {
        std::printf("through pointer %d\n", value);
    }
    try {
        throw std::bad_alloc();
    } catch (const std::bad_alloc&) {
        std::printf("bad_alloc\n");
    }
    // Every catch resumes this frame; the translated program must not grow its stack per throw.
    long total = 0;
    for (int i = 0; i < 150 * scale; ++i) {
        try {
            if (i % 3 == 0)
                throw i;
            total += i;
        } catch (int value) {
            total -= value;
        }
    }
    std::printf("loop total %ld\n", total);
    return 0;
}

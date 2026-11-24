// LUFT: {"args": ["library", "alpha", "beta", "gamma"], "stdin": "3 1 4 1 5 9 2 6\nthe quick brown fox\n"}
// The C++ standard library: containers, algorithms, strings, streams, smart pointers, and type-erased calls.
#include <algorithm>
#include <cstdio>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

namespace {
struct Shape {
    virtual ~Shape() = default;
    virtual double area() const = 0;
    virtual std::string name() const = 0;
};

struct Rectangle : Shape {
    double width, height;
    Rectangle(double width, double height) : width(width), height(height) {}
    double area() const override { return width * height; }
    std::string name() const override { return "rectangle"; }
};

struct Circle : Shape {
    double radius;
    explicit Circle(double radius) : radius(radius) {}
    double area() const override { return 3.25 * radius * radius; }
    std::string name() const override { return "circle"; }
};

using Value = std::variant<long, double, std::string>;

std::string describe(const Value& value) {
    return std::visit([](const auto& item) -> std::string {
        using T = std::decay_t<decltype(item)>;
        if constexpr (std::is_same_v<T, long>)
            return "long " + std::to_string(item);
        else if constexpr (std::is_same_v<T, double>)
            return "double " + std::to_string(item);
        else
            return "string " + item;
    }, value);
}

std::optional<int> parse(const std::string& text) {
    if (text.empty() || text.find_first_not_of("0123456789") != std::string::npos)
        return std::nullopt;
    return std::stoi(text);
}
}

int main(int argc, char** argv) {
    std::vector<std::string> args(argv + 1, argv + argc);
    std::reverse(args.begin(), args.end());
    for (const auto& arg : args)
        std::cout << "arg " << arg << " (" << arg.size() << ")\n";

    std::string line;
    std::getline(std::cin, line);
    std::istringstream numbers(line);
    std::vector<int> values;
    for (int value; numbers >> value;)
        values.push_back(value);
    std::sort(values.begin(), values.end(), std::greater<>());
    std::cout << "sorted";
    for (const auto value : values)
        std::cout << ' ' << value;
    std::cout << "\nsum " << std::accumulate(values.begin(), values.end(), 0) << " unique "
              << std::set<int>(values.begin(), values.end()).size() << '\n';

    std::getline(std::cin, line);
    std::map<char, int> letters;
    std::unordered_map<std::string, int> words;
    std::istringstream text(line);
    for (std::string word; text >> word;) {
        ++words[word];
        for (const auto ch : word)
            ++letters[ch];
    }
    for (const auto& [letter, count] : letters)
        if (count > 1)
            std::cout << letter << '=' << count << ' ';
    std::cout << "\nwords " << words.size() << " has fox " << words.count("fox") << '\n';

    std::vector<std::unique_ptr<Shape>> shapes;
    shapes.push_back(std::make_unique<Rectangle>(3, 4));
    shapes.push_back(std::make_unique<Circle>(2));
    shapes.push_back(std::make_unique<Rectangle>(1.5, 2));
    std::stable_sort(shapes.begin(), shapes.end(),
        [](const auto& a, const auto& b) { return a->area() < b->area(); });
    for (const auto& shape : shapes)
        std::printf("%s %.2f\n", shape->name().c_str(), shape->area());

    std::vector<std::function<int(int)>> pipeline{
        [](int x) { return x + 3; },
        [](int x) { return x * 7; },
        [offset = int(args.size())](int x) { return x - offset; },
    };
    int accumulated = 2;
    for (const auto& step : pipeline)
        accumulated = step(accumulated);
    std::cout << "pipeline " << accumulated << '\n';

    for (const Value& value : {Value(42L), Value(2.5), Value(std::string("text"))})
        std::cout << describe(value) << '\n';
    for (const char* candidate : {"123", "12a", ""}) {
        const auto parsed = parse(candidate);
        std::cout << '"' << candidate << "\" -> " << (parsed ? std::to_string(*parsed) : std::string("none")) << '\n';
    }

    auto shared = std::make_shared<std::vector<int>>(5, 7);
    std::weak_ptr<std::vector<int>> weak = shared;
    {
        auto copy = shared;
        copy->push_back(int(copy.use_count()));
    }
    std::cout << "shared " << shared->size() << ' ' << shared->back() << ' ' << weak.use_count() << '\n';
    shared.reset();
    std::cout << "expired " << weak.expired() << '\n';

    std::ostringstream formatted;
    formatted.precision(3);
    formatted << std::fixed << 3.14159 << '|' << std::hex << 255 << '|' << std::dec << 12345.678;
    std::cout << formatted.str() << '\n';

    std::string sentence = "Luft translates machine code";
    std::transform(sentence.begin(), sentence.end(), sentence.begin(), [](unsigned char c) { return std::toupper(c); });
    const auto position = sentence.find("MACHINE");
    std::cout << sentence.substr(position) << ' ' << position << ' ' << sentence.rfind('A') << '\n';
    std::vector<int> big(10000);
    std::iota(big.begin(), big.end(), -5000);
    std::rotate(big.begin(), big.begin() + 4321, big.end());
    std::nth_element(big.begin(), big.begin() + 1234, big.end());
    std::cout << "nth " << big[1234];
    std::sort(big.begin(), big.end());
    std::cout << " binary " << std::binary_search(big.begin(), big.end(), 77) << '\n';
    return 0;
}

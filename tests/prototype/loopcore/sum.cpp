#include <iostream>
#include <vector>
int sum(const std::vector<int>& xs) {
  int s = 0;
  for (const auto& x : xs) s += x;
  return s;
}
int main() { std::cout << sum({1, 2, 3, 4}) << '\n'; }

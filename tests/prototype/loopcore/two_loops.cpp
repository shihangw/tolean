#include <iostream>
#include <vector>
int two_loops(const std::vector<int>& xs, int key) {
  int s = 0;
  for (const auto& x : xs) s += x;
  for (int x : xs) {
    if (x == key) return s + x;
  }
  return s;
}
int main() { std::cout << two_loops({1, 2, 3, 4}, 3) << '\n'; }

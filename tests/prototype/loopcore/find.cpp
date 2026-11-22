#include <iostream>
#include <vector>
int find(const std::vector<int>& xs, int key) {
  for (int x : xs) {
    if (x == key) return x;
  }
  return -1;
}
int main() { std::cout << find({1, 2, 3, 4}, 3) << '\n'; }

#include <stdio.h>
int clamp_sum(const int *xs, int n, int limit) {
  int s = 0;
  for (int i = 0; i < n; i++) {
    if (xs[i] < 0) continue;
    s += xs[i];
    if (limit < s) break;
  }
  return s;
}
int main(void) {
  int xs[] = {-1, 2, 3, 4};
  printf("%d\n", clamp_sum(xs, 4, 4));
}

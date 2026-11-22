#include <stdio.h>
int sum(const int *xs, int n) {
  int s = 0;
  for (int i = 0; i < n; i++) s += xs[i];
  return s;
}
int main(void) {
  int xs[] = {1, 2, 3, 4};
  printf("%d\n", sum(xs, 4));
}

#include <stdio.h>
int find(const int *xs, int n, int key) {
  for (int i = 0; i < n; i++) {
    if (xs[i] == key) return i;
  }
  return -1;
}
int main(void) {
  int xs[] = {1, 2, 3, 4};
  printf("%d\n", find(xs, 4, 3));
}

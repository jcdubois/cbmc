#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x; // = malloc(sizeof(long)*L);
  for (size_t i = 0; i < L; i++)
  {
    x[i] = i;
  }
  size_t i = nondet_int();
  // if (i < L) assert(x[i] == i);
  return 0;
}

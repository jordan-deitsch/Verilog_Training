#include <stdio.h>
#include <stdlib.h>

void init_rand() {
  printf("Init Rand\n");
  srand(12345);
}

int Crand() {
  printf("Generating random\n");
  return rand();
}


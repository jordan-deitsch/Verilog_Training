#include <stdio.h>
#include <stdlib.h>

// declare imported SV methods as extern
extern int SVrand();
extern void init_rand();

int my_C_task() {
  int num;
  printf("Starting C task\n");
  init_rand();
  num = SVrand();
  printf ("Got %d from SV\n",num);
  return 0;
}


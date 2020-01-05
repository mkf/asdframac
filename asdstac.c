#include <stdio.h>

typedef unsigned char value_t;
typedef int boolean_t;
typedef int index_t;

#define STACK_SIZE 10

value_t t[STACK_SIZE] = { 0 };
index_t c = -1;

/*@
  behavior limit_reached:
    assumes c==(STACK_SIZE-1);
    assigns \nothing;
  behavior regular:
    assumes c<(STACK_SIZE-1);
    assigns t[old(c)], c;
  requires w>0;
  complete behaviors limit_reached regular;
  disjoint behaviors limit_reached regular;
 */
boolean_t push(value_t w) {
  boolean_t res = c<(STACK_SIZE-1);
  if(res) t[++c] = w;
  return res;
}

value_t pop() {
  return c>=0 ? t[c--] : 0;
}

void print(value_t w);

void process(value_t w) {
  if(w==0) print(pop());
  else if(!push(w)) print(0);
}

void print(value_t w) {
  printf("%u\n", w);
}

int main() {
  int res;
  value_t w;
  while(res = scanf("%uhh", &w), res>0)
    process(w);
  return 0;
}

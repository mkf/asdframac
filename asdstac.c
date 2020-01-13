#include <stdio.h>

typedef unsigned char value_t;
typedef int boolean_t;
typedef int index_t;

#define STACK_SIZE 10

value_t t[STACK_SIZE] = { 0 };
index_t c = -1;

/*@
  requires w>0;
  requires c>=-1;
  requires c<STACK_SIZE;
  behavior limit_reached:
    assumes c==(STACK_SIZE-1);
    assigns \nothing;
    ensures \result==0;
  behavior regular:
    assumes c<(STACK_SIZE-1);
    assigns t[\old(c)], c;
    ensures c==\old(c)+1;
    ensures c<STACK_SIZE;
    ensures \result==1;
    ensures (\forall integer i; 0 <= i < STACK_SIZE ==> (i != \old(c) ==> \old(t[i])==t[i]));
  complete behaviors limit_reached, regular;
  disjoint behaviors limit_reached, regular;
 */
boolean_t push(value_t w) {
  boolean_t res = c<(STACK_SIZE-1);
  if(res) t[++c] = w;
  return res;
}

/*@
  requires c>=-1;
  requires c<STACK_SIZE;
  behavior empty:
    assumes c==-1;
    assigns \nothing;
    ensures \result==0;
  behavior regular:
    assumes c>=0;
    assigns c;
    ensures \result==\old(t[\old(c)]);
    ensures c==\old(c)-1;
  complete behaviors empty, regular;
  disjoint behaviors empty, regular;
 */
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

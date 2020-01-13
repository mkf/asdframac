#include <stdio.h>

typedef unsigned char value_t;
typedef int boolean_t;
typedef int index_t;

#define Q_SIZE 10

value_t t[Q_SIZE] = { 0 };
index_t c = 0;
index_t off = 0;

/*@
  requires w>0;
  requires c>=0;
  requires c<=Q_SIZE;
  requires off>=0;
  requires off<Q_SIZE;
  ensures c>=0;
  ensures c<=Q_SIZE;
  behavior limit_reached:
    assumes c==Q_SIZE;
    assumes (off+c)%Q_SIZE==off;
    assigns \nothing;
  behavior regular:
    assumes c<Q_SIZE;
    assumes (off+c)%Q_SIZE!=off;
    assigns t[\old((off+c)%Q_SIZE)], c;
  complete behaviors limit_reached, regular;
  disjoint behaviors limit_reached, regular;
 */
boolean_t enqueue(value_t w) {
  //@ assert (c==Q_SIZE) == ((off+c)%Q_SIZE==off);
  //@ assert (c<Q_SIZE) == ((off+c)%Q_SIZE!=off);
  boolean_t res = c<Q_SIZE;
  //@ assert res || (off+c)%Q_SIZE==off;
  index_t i = (off+c)%Q_SIZE;
  if(res) {
    t[i] = w;
    c++;
  }
  return res;
}
/*@
  requires c>=0;
  requires c<=Q_SIZE;
  requires off>=0;
  requires off<Q_SIZE;
  ensures c>=0;
  ensures c<=Q_SIZE;
  ensures off>=0;
  ensures off<Q_SIZE;
  behavior empty:
    assumes c==0;
    assigns \nothing;
    ensures \result==0;
  behavior regular:
    assumes c>0;
    assigns c, off;
    ensures \result==\old(t[\old(off)]);
    ensures c==\old(c)-1;
    ensures off==(\old(off)+1)%Q_SIZE;
  complete behaviors empty, regular;
  disjoint behaviors empty, regular;
 */
value_t dequeue() {
  index_t i = off;
  return c>0 ? (c--, (off=(off+1)%Q_SIZE), t[i]) : 0;
}

void print(value_t w);

void process(value_t w) {
  if(w==0) print(dequeue());
  else if(!enqueue(w)) print(0);
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

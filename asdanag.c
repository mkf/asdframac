#include <stdio.h>

char s[2][10001];

/*@
  axiomatic zalozenia_zadania {
    axiom null_terminated{L}:
      \forall integer i; 0 <= i < 2 ==> \exists integer n;
        0 <= n <= 10000 && s[n]==0;
  }
 */

/*@
  assigns \nothing;
  ensures 0 <= \result <= 10000 && s[\result]==0;
 */
int len(char s[]) {
  for(int i=0; i<10000; i++)
    if(s[i]==0) return i;
  return -1;
}

int c;
int n[2];

void swap(int w, int f, int t) {
  char tcc = s[w][t];
  s[w][t]=s[w][f];
  s[w][f]=tcc;
}

void heapify(int w) {
  while(1) {
    int i = c * 2 + 1;
    int nc;
  again:
    nc = c;
    if(i<n[w] && s[w][i] > s[w][nc]) nc = i;
    if(i%2) { i++; goto again; }
    if(c != nc) swap(w, c, nc);
    else break;
    c = nc;
  }
}

int lens[2];

void sort(int w) {
  n[w]=lens[w];
  for(c = lens[w] / 2 - 1; c >= 0; c--)
    heapify(w);
  for(n[w]--; n[w]>=0; n[w]--) {
    swap(w, 0, n[w]);
    c=0;
    heapify(w);
  }
}

/*@
  axiomatic Count_of {
    logic integer count_of_upto(integer w, char c, integer upto) =
      upto > 0 ? (s[w][upto]==c ? 1 : 0) + count_of_upto(w,c,upto-1)
               : (s[w][upto]==c ? 1 : 0);
    logic integer count_of(integer w, char c) = count_of_from(w,c,lens[w]-1);
  }
 */


  //ghost char cou[2][255];
  //ghost for(char cc = 0; cc <= 255; cc++) for(int i=0; i<len(s[0]); i++) for(int iw=0; iw<2; iw++) cou[iw][cc]++; 
  //predicate samecount = \forall char cc; 0 <= cc <= 255 ==> cou[0][cc]==cou[1][cc];
/*@
  predicate samecount = \forall char cc; 0 <= cc <= 255 ==>
    count_of(0, cc)==count_of(1, cc);
 */
/*@
  behavior len_mismatch:
    assumes len(s[0])!=len(s[1]);
    ensures \result == 0;
  behavior len_match:
    assumes len(s[0])==len(s[1]);
    ensures \result == (samecount ? 1 : 0);
  complete behaviors len_mismatch, len_match;
  disjoint behaviors len_mismatch, len_match;
 */
int anag() {
  lens[0] = len(s[0]);
  lens[1] = len(s[1]);
  if(lens[0]!=lens[1]) return 0;
  sort(0); sort(1);
  for(c = 0; c < lens[0]; c++)
    if(s[0][c]!=s[1][c]) return 0;
  return 1;
}

int main() {
  scanf("%s\n", s[0]);
  scanf("%s\n", s[1]);
  printf("%d\n", anag());
}

#include <stdio.h>

char s[2][10000];

int c;
int n[2];

void swap(int w, int f, int t) {
  char tcc = s[w][t];
  s[w][t]=s[w][f];
  s[w][f]=tcc;
}

void heapify(int w) {
  while(1) {
    int i = c * 2;
    int nc;
    do {
      i++;
      nc = c;
      if(i<n[w] && s[w][i] > s[w][nc]) nc = i;
    } while(i%2);
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
  logic integer count_of_upto(char sw[10000], char c, integer upto) = \numof(0, upto, (\lambda integer i; sw[i]==c));
  logic integer count_of(char sw[10000], char c, int n) = count_of_upto(sw,c,(int)(n-1));
  predicate samecount = \forall char cc; 0 <= cc <= 255 ==>
    count_of(s[0], cc, lens[0])==count_of(s[1], cc, lens[1]);
 */
/*@
  behavior len_mismatch:
    assumes lens[0]!=lens[1];
    ensures \result == 0;
  behavior len_match:
    assumes lens[0]==lens[1];
    ensures \result == 1 && samecount || \result == 0 && !samecount;
  complete behaviors len_mismatch, len_match;
  disjoint behaviors len_mismatch, len_match;
 */
int anag() {
  if(lens[0]!=lens[1]) return 0;
  sort(0); sort(1);
  for(c = 0; c < lens[0]; c++)
    if(s[0][c]!=s[1][c]) return 0;
  return 1;
}

int scans(char s[]) {
  int i = 0;
  char c = getchar();
  while(c != EOF && c != '\n') {
    s[i++] = c;
    c = getchar();
  }
  return i;
}

int main() {
  lens[0] = scans(s[0]);
  lens[1] = scans(s[1]);
  printf("%d\n", anag());
}

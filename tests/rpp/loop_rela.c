/* run.config
   OPT: -rpp
*/

/*@ requires n >= 0;
  @ assigns \result \from n;
  @ ensures  \result == (n*(n+1))/2;
*/
int f(int n){
  int i = 0;
  int x = 0;
  /*@ loop assigns x,i;
    @ loop invariant 0 <= i <= n + 1;
    @ loop invariant n == 0 ==> x == 0;
    @ loop invariant n > 0 ==> x == (i*(i-1))/2;
   */
  while(i <= n){
    x = x + i;
    i = i + 1;
  }
  return x;
}

/*@ requires n >= 0;
  @ assigns \result \from n;
  @ ensures  \result == (n*(n+1))/2;
  @ relational \forall int n; \callpure(f,n) == \callpure(g,n);
*/
int g(int n){
  int j = 1;
  int y = 0;
  /*@ loop assigns y,j;
    @ loop invariant 0 < j <= n + 1;
    @ loop invariant n == 0 ==> y == 0;
    @ loop invariant n > 0 ==> y == (j*(j-1))/2;
   */
  while(j <= n){
    y = y + j;
    j = j + 1;
  }
  return y;
}

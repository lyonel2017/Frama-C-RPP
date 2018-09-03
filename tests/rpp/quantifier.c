/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x;
  @ relational \forall int x;
  x < 2 ==> (\exists int y; y == x && \callpure(f,x+1) <= 3);
*/
int f(int x){
  return x + 1;
}

/*@ assigns \result \from x;
  @ relational \forall int x;
  x < 2 ==> (\forall int y; y == x && \callpure(f,x+1) <= 3);
*/
int g(int x){
  return x + 1;
}

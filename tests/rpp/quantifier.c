/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x; */
int f(int x){
  return x + 1;
}

/*@ relational
      \forall int x; x < 2 ==> (\exists int y; y == x && \callpure(f,x+1) <= 3);
*/

/*@ assigns \result \from x; */
int g(int x){
  return x + 1;
}

/*@ relational
      \forall int x; x < 2 ==> (\forall int y; y == x && \callpure(f,x+1) <= 3);
*/

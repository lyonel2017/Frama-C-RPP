/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x;
  @ relational \forall int x1,x2; x1 < x2 ==> \callpure(f,x1) < \callpure(f,x2);
*/
int f(int x);

/*@ assigns \result \from x;
  @ relational \forall int x1,x2; x1 < x2 ==> \callpure(g,x1) < \callpure(g,x2);
*/
int g(int x){
  return f(x);
}

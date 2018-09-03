/* run.config
   OPT: -rpp
*/

/*@ axiomatic test{
  logic integer f(integer x) = x + 1;
}*/

/*@ relational \forall int x; \callpure(f1,x) == f(x);
  @ assigns \result \from x;
*/
int f1(int x){
	return x + 1;
}

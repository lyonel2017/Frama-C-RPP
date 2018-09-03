/* run.config
   OPT: -rpp -rpp-pro
*/
int y = 0;

/*@ relational \forall int x1,x2; x1 < x2 ==> \callpure(f1,x1) < \callpure(f1,x2);
  @ assigns \result \from x;
*/
int f1(int x){
	return x + 1;
}

/*@ relational \forall int x1,x2; x1 < x2 ==> \callpure(f2,x1) < \callpure(f2,x2);
  @ assigns \result \from x;
*/
int f2(int x){
  return f1(x);
}

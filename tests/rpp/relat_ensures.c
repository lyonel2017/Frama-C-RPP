/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x;
  @ relational \forall int x1; x1 > 0 ==> \callpure(g,x1) == x1 + 2;*/
int g(int x){
	return 2 + x;
}

/*@ assigns \result \from x;
  @ relational \forall int x1; x1 > 0 ==> \callpure(f,x1) == x1 + 5;*/
int f(int x){
	return x + 5;
}

/*@ assigns \result \from x;
  @ relational \forall int x1; x1 > 0 ==> \callpure(f,x1) < \callpure(h,x1);*/
int h(int x){
	return f(x) + g(x);
}

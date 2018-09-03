/* run.config
   OPT: -rpp
*/

/*@ relational \forall int x1,x2; x1 < x2 ==> \callpure(f1,x1) < \callpure(f1,x2);
  @ assigns \result \from x;*/
int f1(int x){
	return x + 1;
}

/*@ relational \forall int x1,x2; x1 < x2 ==> \callpure(f2,x1) < \callpure(f2,x2);
  @ assigns \result  \from y;*/
int f2(int y){
  return 2+y;
}

/*@ relational \forall int x1,x2; x1 < x2 ==> \callpure(g,x1) < \callpure(g,x2);
  @ relational \forall int x1; x1 > 0 ==> \callpure(f1,x1) < \callpure(f2,x1) < \callpure(g,x1);
  @ assigns \result \from x;
*/
int g(int x){
  return f1(x)+f2(x);
}

/*@ relational \forall int x1,x2; x1 < x2 ==> \callpure(h,x1) < \callpure(h,x2);
  @ assigns \result \from x;*/
int h(int x){
  return f1(f2(x));
}

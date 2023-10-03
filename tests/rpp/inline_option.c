/* run.config
   OPT: -rpp
*/

/*@ requires x > 0;
  @ assigns \result \from x;*/
int f1(int x){
	return x + 1;
}

/*@ relational \forall int x1; \callpure(f1,x1) > 0; */

/*@ requires y > 0;
  @ assigns \result \from y;*/
int f2(int y){
  return 2+y;
}

/*@  assigns \result \from x; */
int g(int x){
  return f1(x)+f2(x);
}

/*@ relational
      \forall int x1; \callpure(0,f1,x1) < \callpure(0,f2,x1) < \callpure(g,x1);
*/

/*@ assigns \result \from x; */
int fact(int x) {
	if(x <= 1){
		return 1;
	}
	else{
		return x*fact(x-1);
	}
}

/*@ relational \forall int x1; x1 <= 1 ==> \callpure(fact,x1) == 1; */

/*@ relational
      \forall int x1; x1 > 1 ==>
      \callpure(fact,x1+1) == \callpure(0,fact,x1)*(x1+1);
*/

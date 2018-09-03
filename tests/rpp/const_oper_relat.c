/* run.config
   OPT: -rpp
*/

/*@ requires x > 0;
  @ relational \forall int x1,x2; x1<=x2  ==> \callpure(f,x1) < \callpure(f,x1+\callpure(f,x2));
  @ relational \callpure(f,2) == 4;
  @ assigns \result \from x;
*/
int f(int x){
	return x*x; 
}

/* run.config
   OPT: -rpp
*/

/*@ requires \let y = x + 1; y > 0;
  @ assigns \result \from x;
*/
int f(int x){
  return x;
}

/*@ relational \forall int x1; \callpure(f,x1) == 2;*/

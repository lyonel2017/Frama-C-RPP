/* run.config
   OPT: -rpp
*/


/*@ requires \valid(x);
  @ assigns \result \from *x;
*/
int k(int *x){
  return *x + 5;
}


/*@ requires \valid(x);
  @ assigns *x \from *x;
  @ relational \forall int *x; \callset(\call(f,x,id1),\call(k,x,id2)) ==> \at(*x,Post_id1) == \callresult(id2);
*/
void f(int *x){
  *x = *x + 5;
}

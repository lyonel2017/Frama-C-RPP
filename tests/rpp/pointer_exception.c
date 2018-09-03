/* run.config
   OPT: -rpp
*/

/*@ requires \valid(x);
  @ assigns *x \from *x;
  @ relational \forall int *x; \callset(\call(f,x,id1),\call(f,x,id2)) ==> \at(*x,Pre_id1) < \at(*x,Pre_id2) ==> \at(*x,Post_id1) < \at(*x,Post_id2);
*/
void f(int *x){
  *x = *x + 5;
}

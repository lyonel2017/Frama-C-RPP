/* run.config
   OPT: -rpp
*/

int *y;

/*@ requires \valid(y);
  @ requires *y > 0;
  @ assigns *y \from *y,x;
  @ relational \forall int x;\rela(\callset(\call(k,x,id1),\call(k,x,id2)), \at(*y,Pre_id1) < \at(*y,Pre_id2) && x > 0==> \at(*y,Post_id1) < \at(*y,Post_id2));
*/
void k(int x){
  *y = *y + x;
}

/*@ requires \valid(x);
  @ assigns *x \from *x;
  @ relational \forall int *x1,*x2; \rela(\callset(\call(f,x1,id3),\call(f,x2,id4)), \at(*x1,Pre_id3) < \at(*x2,Pre_id4) ==> \at(*x1,Post_id3) < \at(*x2,Post_id4));
*/
void f(int *x){
  *x = *x + 5;
}

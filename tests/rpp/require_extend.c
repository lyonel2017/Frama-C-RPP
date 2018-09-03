/* run.config
   OPT: -rpp
*/

/*@ requires x <  10000- 10;
  @ assigns \result \from x;
  @ relational \forall int x1,x2; \callset(\call(f,x1,id1),\call(f,x2+1,id2)) ==>  x1 < x2 ==> \callresult(id1) < \callresult(id2);
  @ relational \forall int x1,x2; x1 < x2 ==> \callpure(f,x1) < \callpure(f,x2+1);

*/
int f(int x){
  int a = 10;
  return x + a;
}

/* run.config
   OPT: -rpp
*/

int y;

/*@ assigns \result \from x,y;
  @ relational \forall int x1,x2; \rela(\callset(\call(f,x1,id1),\call(f,x2,id2)), \at(y,Pre_id1) < \at(y,Pre_id2) && x1 < x2 ==> \callresult(id1) < \callresult(id2));
*/
int f(int x){
  return x + y;
}

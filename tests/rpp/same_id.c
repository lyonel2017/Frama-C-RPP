/* run.config
   OPT: -rpp
*/

int y;

/*@ assigns \result \from y;
  @ relational \callset(\call(g,id1)) ==> 0 == 0;*/
int g(){
  return y ;
}

/*@ assigns \result \from y;
  @ relational \callset(\call(k,id1)) ==> \callresult(id1) == \at(y,Pre_id1);*/
int k(){
  return y;
}

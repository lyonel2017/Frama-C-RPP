/* run.config
   OPT: -rpp
*/

int y;

/*@ assigns \result \from y; */
int g(){
  return y ;
}

/*@ relational \callset(\call(g,id1)) ==> 0 == 0;*/

/*@ assigns \result \from y; */
int k(){
  return y;
}

/*@ relational \callset(\call(k,id1)) ==> \callresult(id1) == \at(y,Pre_id1);*/

/* run.config
   OPT: -rpp
*/

int y;
int z;


/*@ assigns \result \from y;
  @ relational \callset(\call(g,id1)) ==> \callresult(id1) == 1;*/
int g(){
  return y;
}


/*@ assigns \result \from z;
  @ relational \callset(\call(f,id2)) ==> \callresult(id2) == 1;*/
int f(){
  return y+z;
  }

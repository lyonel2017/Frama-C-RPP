/* run.config
   OPT: -rpp
*/

int y;
int z;


/*@ assigns \result \from y; */
int g(){
  return y;
}

/*@ relational \callset(\call(g,id1)) ==> \callresult(id1) == 1;*/


/*@ assigns \result \from z; */
int f(){
  return y+z;
  }

/*@ relational \callset(\call(f,id2)) ==> \callresult(id2) == 1;*/

/* run.config
   COMMENT: we can't generate the self-composed function if we don't have assigns \from info
   EXIT: 1
   OPT: -rpp
*/
int y;

int g(){
  return y;
}

/*@ assigns \result \from x,y; */
int f(int x){
  return x;
}

/*@ relational
     \callset(\call(g,id1),\call(g,id2)) ==>
     \callresult(id1) < \callresult(id2);
*/

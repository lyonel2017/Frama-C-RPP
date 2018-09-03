/* run.config
   OPT: -rpp
*/
int y;

int g(){
  return y;
}

/*@ assigns \result \from x,y;
  @ relational \callset(\call(g,id1),\call(g,id2)) ==> \callresult(id1) < \callresult(id2);
*/
int f(int x){
  return x;
}

/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x;
  @ relational \forall int * x1,* x2; \callset(\call(f,x1,id1),\call(f,x2,id2)) ==> x1 == x2 ==> \callresult(id1) == \callresult(id2);*/
int f(int *x){
  return *x;
}

int *y;

/*@ assigns \result \from *y;
  @ relational \callset(\call(h,id3),\call(h,id4)) ==> \at(*y,Pre_id3) == \at(*y,Pre_id4) ==> \callresult(id3) == \callresult(id4);*/
int h(){
  return *y;
}


/*@ assigns \result \from y;
  @ relational \callset(\call(l,id5),\call(l,id6)) ==> \at(y,Pre_id5) == \at(y,Pre_id6) ==> \callresult(id5) == \callresult(id6);*/
int l(){
  return y;
}

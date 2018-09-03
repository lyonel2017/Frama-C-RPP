/* run.config
   OPT: -rpp
*/

int y;


/*@ assigns y \from y,x;*/
void k (int x){
  y = y + x;
  return;
}


/*@ assigns y \from y,x;
  @ relational \forall int x ;\callset(\call(p,x,id3),\call(p,x,id4)) ==> \at(y,Pre_id3) < \at(y,Pre_id4) ==> \at(y,Post_id3) < \at(y,Post_id4);
*/
void p (int x){
  y = y + x;
  return;
}

/*@ assigns y \from y;
  @ relational \callset(\call(f,id1),\call(f,id2)) ==> \at(y,Pre_id1) < \at(y,Pre_id2) ==> \at(y,Post_id1) < \at(y,Post_id2);
*/
void f(){
  int x = 5;
  k(x);
  p(x);
  return;
}

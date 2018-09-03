/* run.config
   OPT: -rpp
*/

int y;

/*@ assigns \result \from x;*/
int f(int x){
  return x + 1;
}

/*@ assigns y \from y,x;
  @ relational \forall int x,k; \rela(\callset(\call(g,x,id1),\call(g,\callpure(f,k),id2)),\at(y,Pre_id1) == \at(y,Pre_id2) && x > 0 && \at(y,Pre_id1) > 0 && \at(y,Pre_id2) > 0 && k == \callresult(id1) ==> \at(y,Post_id1) < \at(y, Post_id2));
*/
int g(int x){
  y = y + x;
  return y;
}

int l;

/*@ assigns l \from x;*/
void j(int x){
  l = x;
}

/*@ assigns l \from l;
  @ relational \forall int x; \rela(\callset(\call(p,id3),\call(j,x,id4),\call(p,id5)), x == \at(l,Post_id3) && \at(l, Pre_id3) == \at(l,Pre_id5) ==> \at(l,Post_id4) == \at(l,Post_id5));*/
void p(){
  l = l + 1;
}

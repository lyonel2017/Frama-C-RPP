/* run.config
   OPT: -rpp
*/

int y;

/*@ assigns \result \from x;
  @ relational \forall int x3;\rela(\callset(\call(g,\callpure(g,x3),id11)), \callresult(id11) == \callpure(g,\callpure(g,x3)));
  @ relational \forall int x1,x2; x1 < x2 ==> \callpure(g,x1) < \callpure(g,x2);
  @ relational \forall int x1,x2; \rela(\callset(\call(g,x1,id3),\call(g,x2,id4)), x1 < x2 ==> \callresult(id3) < \callresult(id4));
*/
int g(int x){
  return x + 1;
}

/*@ relational \rela(\callset(\call(f,id1),\call(f,id2)), \at(y,Pre_id1) < \at(y,Pre_id2) ==> \at(y,Post_id1) < \at(y,Post_id2));
  @ relational \forall int x3;\rela(\callset(\call(f,id8)),x3 == \at(y,Pre_id8) ==> \at(y,Post_id8) == \callpure(g,x3));
  @ relational \rela(\callset(\call(f,id5)),\at(y,Pre_id5) < \at(y,Post_id5));
  @ assigns y \from y;
*/
void f(){
  y = y + 1;
}

/*@ assigns y \from y;
  @ relational \rela(\callset(\call(f,id6),\call(k,id7)), \at(y,Pre_id6) == \at(y,Pre_id7) ==> \at(y,Post_id6) < \at(y,Post_id7));
*/
void k(){
  y = y + 5;
}

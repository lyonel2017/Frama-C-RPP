/* run.config
   OPT: -rpp
*/

int y;

/*@ requires y > 0;
  @ assigns y \from y;
  @ relational \rela(\callset(\call(k,id1),\call(k,id2)), \at(y,Pre_id1) < \at(y,Pre_id2) ==> \at(y,Post_id1) < \at(y,Post_id2));
*/
void k(){
  y = y + 5;
}

int g;
int j;

/*@ requires j > 0;
  @ requires g > 0;
  @ assigns j \from g,j;
  @ relational \rela(\callset(\call(f,id3),\call(f,id4)), \at(j,Pre_id3) < \at(j,Pre_id4) && \at(g, Pre_id3) == \at(g,Pre_id4) ==> \at(j,Post_id3) < \at(j,Post_id4));
*/
void f(){
  j = j + g + 5;
}



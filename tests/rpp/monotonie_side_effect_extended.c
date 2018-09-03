/* run.config
   OPT: -rpp
*/


int g;
int j;

/*@ requires j > 0;
  @ requires g > 0;
  @ assigns j \from x,j;
  @ assigns g \from g,x;
  @ relational \forall int x; \rela(\callset(\call(f,x,id3),\call(f,x,id4)), \at(j,Pre_id3) < \at(j,Pre_id4) && \at(g, Pre_id3) > \at(g,Pre_id4) && x > 0 ==> \at(j,Post_id3) < \at(j,Post_id4) && \at(g,Post_id3) > \at(g,Post_id4));
*/
void f(int x){
  j = j + x;
  g = g - x;
}

/* run.config
   OPT: -rpp
*/

int x;
int y;

/*@ requires x > 0;
  @ assigns x \from x;
  @ ensures x > 0;
*/
int f1(){
  x = x + 1;
  return x;
}

/*@ requires y > 0;
  @ assigns y \from y;*/
int f2(){
  y = 2 + y;
  return y;
}

/*@ requires x > 0;
  @ requires y > 0;
  @ assigns y \from y;
  @ assigns x \from x;
  @ relational \rela(\callset(\call(1,f1,id1),\call(1,f2,id2),\call(2,g,id3)),
    \at(x,Pre_id1) == \at(x,Pre_id3) && \at(y,Pre_id2) == \at(y,Pre_id3) && \at(x,Pre_id1) == \at(y,Pre_id2)  ==> \callresult(id1) < \callresult(id2) < \callresult(id3));
*/
int g(){
  return f1()+f2()+f1();
}

/* run.config
   OPT: -rpp
*/

int y;

/*@ assigns y \from y; */
void h(){
  int a = 10;
  y = y + a;
  return;
}

/*@ relational
      \callset(\call(h,id1),\call(h,id2)) ==>
        \at(y,Pre_id1) < \at(y,Pre_id2) ==> \at(y,Post_id1) < \at(y,Post_id2);
*/

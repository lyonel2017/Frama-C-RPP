/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x,y; */
int f (int x, int y){
  return x + y;
}

/*@ relational
     \forall int x1, y1, x2, y2;
        \callset(\call(f,x1,y1,id1), \call(f,x2,y2,id2)) ==>
         x1 < x2 && y1 < y2 ==>  \callresult(id1) < \callresult(id2);
*/

int k;

/*@ assigns k \from k,x; */
void g(int x){
  k = k + x;
}

/*@ relational
     \forall int x1, x2;
       \callset(\call(g,x1,id3), \call(g,x2,id4)) ==>
       x1 < x2 && \at(k,Pre_id3) < \at(k,Pre_id4)
       ==>  \at(k,Post_id1) < \at(k,Post_id4);
*/

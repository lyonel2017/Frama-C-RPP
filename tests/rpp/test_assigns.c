/* run.config
   OPT: -rpp
*/

int y;

/*@ assigns \result \from y,x; */
int f(int x){
	return x + y;
}

/*@ relational
      \forall int x1,x2;
        \callset(\call(f,x1,id1),\call(f,x2,id2)) ==>
        \at(y,Pre_id1) < \at(y,Pre_id2) && x1 < x2 ==>
        \callresult(id1) < \callresult(id2);
*/

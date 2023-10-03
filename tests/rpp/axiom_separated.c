/* run.config
   OPT: -rpp
*/

int *y;

/*@ requires \separated(t+(0..n),y);
  @ requires n > 0;
  @ assigns \result \from n,t[0..n],*y;
*/
int k(int* t, int n){
  return t[1] + t[n-1] + *y;
}

/*@ relational \forall int x,*tb;
      \callset(\call(k,tb,x,id1)) ==>
      \callresult(id1) == \at(tb[1],Pre_id1) + \at(tb[x-1],Pre_id1);
*/

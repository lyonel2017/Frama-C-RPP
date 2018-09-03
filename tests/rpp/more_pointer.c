/* run.config
   OPT: -rpp
*/

/*@ predicate is_eq{L1,L2}(int *q, int *p, integer b) = \forall integer i; 0 <= i < b ==> \at(q[i],L1) == \at(p[i],L2); */

/*@ requires \valid(x+(0..1));
  @ assigns x[0..1] \from x[0..1];
  @ relational \forall int *x1,*x2; \callset(\call(f,x1,id1),\call(f,x2,id2)) ==> is_eq{Post_id1,Pre_id2}(x1,x2,2) ==> is_eq{Pre_id1,Post_id2}(x1,x2,2);
*/
void f(int *x){
  int temp = 0;
  temp = *x;
  *x = *(x+1);
  *(x+1) = temp;
}

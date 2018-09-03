/* run.config
   OPT: -rpp
*/

int x;

/*@ assigns \result \from x,b;
  @ relational \forall int return_variable_relational_1; \callset(\call(h,return_variable_relational_1,id1)) ==> return_variable_relational_1 == 0 ==> \callresult(id1) == 0;
  @ relational \forall int x_id2; \callset(\call(h,x_id2,id2)) ==> x_id2 == 0 ==> \callresult(id2) == 0;*/
int h(int b){
  return x+b;
}

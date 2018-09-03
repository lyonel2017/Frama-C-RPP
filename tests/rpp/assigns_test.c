/* run.config
   OPT: -rpp
*/


int y;

/*@ assigns y \from x;
  @ relational \forall int x; \rela(\callset(\call(f,x,id1)),\at(y,Post_id1) == x);
*/
void f(int x){
  y = x;
  return;
}

/* run.config
   OPT: -rpp
*/

int y;

/*@ assigns \result \from x;*/
int g(int x){
  return x + 1;
}

/*@ relational \forall int x3;\rela(\callset(\call(f,id9),\call(g,x3,id10)),\at(y,Pre_id5) == \callresult(id10));
  @ assigns y \from y;
*/
void f(){
  y = y + 1;
}

/* run.config
   COMMENT: we're using an inexistent id (Pre_id5) that should raise an error
   EXIT: 1
   OPT: -rpp
*/

int y;

/*@ assigns \result \from x;*/
int g(int x){
  return x + 1;
}

/*@ assigns y \from y; */
void f(){
  y = y + 1;
}

/*@ relational
     \forall int x3;
       \rela(\callset(\call(f,id9),\call(g,x3,id10)),
             \at(y,Pre_id5) == \callresult(id10));
*/

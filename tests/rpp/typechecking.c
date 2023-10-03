/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x,y; */
int f(int x, float y){
  return x + y;
}

/*@ relational
      \forall int x1,x2,float y1,y2;
      y1 == y2 && x1 < x2 ==> \callpure(f,x1,x2) < \callpure(f,x2,y2);
*/


/*@ assigns \result \from x,y; */
int g(int x, float y){
  return x + y;
}

/*@ relational
      \forall int x,float y;
      \rela(\callset(\call(g,x,y,id1)),\callresult(id1) == 0);
*/


/*@ assigns \result \from \nothing; */
int k(){
  return 5;
}

/*@ relational \rela(\callset(\call(k,id2)),\callresult(id1) == 5); */

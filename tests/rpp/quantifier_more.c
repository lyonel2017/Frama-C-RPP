/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x;*/
int g(int x){
  return x;
}

/*@ assigns \result \from x; */
int f(int x){
  return x;
}

/*@ relational
      \forall int x,y;
        \callset(\call(f,x,id1),\call(g,y,id2)) ==>
          \exists int a,b,c,d;
            a > 10 && b < 2 && d > c &&
            (x == a ==> d == \callresult(id1)) &&
            (y == b ==> c == \callresult(id2));
*/

/* run.config
   COMMENT: the first \callpure is ill-typed and should be rejected.
   EXIT: 1
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

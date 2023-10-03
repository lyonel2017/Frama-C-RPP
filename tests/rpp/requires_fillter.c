/* run.config
   OPT: -rpp
*/

/*@ requires x >= 0;
  @ assigns \result \from x;*/
int g(int x){
  return x;
}

/*@ requires 0 <= x && 0 <= y;
  @ assigns \result \from x,y;
*/
int f(int x, int y){
  return x <= y ? x :y;
}

/*@ relational
      \forall int x,y; x >= 0 ==>
        \callpure(f,\callpure(g,x),y) == \callpure(g,x);
*/

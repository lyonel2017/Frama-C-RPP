/* run.config
   OPT: -rpp
*/


/*@ requires y >=0 && x >=0;
  @ assigns \result \from x,y;
  @ relational \forall int x,y; x <= 0 ==> \callpure(g,x,y) == 0;
  @ relational \forall int x,y; x > 0 ==> \callpure(g,x,y) == x*y;
  @ relational \forall int x1,x2,y; x1 > 0 && x2 > 0 ==> \callpure(0,g,x1+x2,y) == \callpure(0,g,x1,y) + \callpure(0,g,x2,y);
 */
int g(int x, int y){
  if (x <= 0){
    return 0;
  }
  else{
    return y + g(x-1,y);
  }
}

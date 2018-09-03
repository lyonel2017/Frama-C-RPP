/* run.config
   OPT: -rpp
*/

/*@ requires x > 0 && z < 15;
  @ assigns \result \from x,z;*/
int f (int x, int z){
  return x + 5 + z;
}

/*@ requires y < 0 && h > 100;
  @ assigns \result \from y,h;
  @ relational \forall int k,h; \callpure(g,\callpure(f,k,h),h) == 0;
*/
int g (int y, int h){
  return y - 5 + h;
}

/* run.config
   OPT: -rpp
*/

/*@ requires x > 0 && z > 15;
  @ assigns \result \from x,z;*/
int f (int x, int z){
  return x + 5 + z;
}

/*@ requires y > 0 && h > 100;
  @ relational \forall int x,z,y,h; \callpure(g,y,h) + \callpure(f,x,z) > 125;
  @ assigns \result \from y,h;
*/
int g (int y, int h){
  return y + 5 + h;
}

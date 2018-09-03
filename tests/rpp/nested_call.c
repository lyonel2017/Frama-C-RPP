/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x,y;*/
int f(int x, int y){
  return x+y;
}

/*@ relational \forall int x,y; \callpure(g,\callpure(f,x,y),y)==x;
  @ assigns \result \from x,y;*/
int g(int x, int y){
  return x-y;
}

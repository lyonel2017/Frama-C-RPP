/* run.config
   OPT: -rpp
*/

/*@ assigns  \result \from x;*/
int abs (int x){
  return (x >= 0) ? x : (-x);
}


/*@ assigns \result \from x,y;*/
int max(int x,int y){
  return (x >= y) ? x : y;
}

/*@ assigns \result \from x,y;
  @ relational R1: \forall int x,y;
     \callpure(max,x,y) == (x+y+\callpure(abs,x - y))/2;
  @ relational R2: \forall int x,y;
     \callpure(min,x,y) == (x+y-\callpure(abs,x - y))/2;*/
int min(int x,int y){
  return (x >= y) ? y : x;
}

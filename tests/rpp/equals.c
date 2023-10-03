/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x;*/
int f(int x){
  return x;
}

/*@ assigns \result \from x;*/
int g(int x){
  return x;
}

/*@ assigns \result \from x; */
int h(int x){
  return x;
}

/*@ relational \forall int x; \callpure(h,x) == \callpure(g,x); */
/*@ relational \forall int x; \callpure(f,x) == \callpure(g,x); */
/*@ relational \forall int x; \callpure(0,h,x) == \callpure(0,f,x);*/

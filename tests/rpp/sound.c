/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from i,n;
  @ relational \callpure(f,0,0) != \callpure(f,0,0);
  @ relational \forall int n; n > 0 ==> \callpure(f,0,n) != \callpure(f,0,n);*/
int f(int i, int n){
  if (i >= n){
    return 0;
  }
  else{
    return f(i + 1,n);
  }
}

/*@ assigns \result \from n;
  @ relational \forall int n; \callpure(g,n) != \callpure(g,n);*/
int g(int n){
    return 0;
}

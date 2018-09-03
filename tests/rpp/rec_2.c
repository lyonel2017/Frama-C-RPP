/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from i;
  @ relational \callpure(f,0) == 0;
  @ relational \callpure(f,1) == \callpure(f,0);
  @ relational \forall int n; n > 0 ==> \callpure(f,n+1) == \callpure(f,n);*/
int f(int i){
  if (i <= 0){
    return 0;
  }
  else{
    return f(i - 1);
  }
}

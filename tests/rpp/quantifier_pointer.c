/* run.config
   OPT: -rpp
*/

/*@ requires n > 0;
  @ requires \valid(t+(0..n));
  @ assigns t[0..n] \from t[0..n],n;
*/
void f (int n,int t[]){
  int i;
  /*@ loop invariant \forall int k; 0 <= k < i ==> \at(t[k],Here) == \at(t[k],Pre) + 1;
    @ loop invariant \forall int k; i <= k < n ==> \at(t[k],Here) == \at(t[k],Pre);
    @ loop invariant 0 <= i <= n;
    @ loop assigns t[0..n],i;
    @ loop variant n-i;
  */
  for(i=0; i < n; i++){
    t[i] = t[i] + 1;
  }
  return;
}

/*@ relational
      \forall int n,*t1,*t2;
        \callset(\call(f,n,t1,id1),\call(f,n,t2,id2))
        ==> (\forall int i; 0 <= i < n ==>
               \at(t1[i],Pre_id1) <= \at(t2[i],Pre_id2))
             ==>
            (\forall int i; 0 <= i < n ==>
               \at(t1[i],Post_id1) <= \at(t2[i],Post_id2));
*/

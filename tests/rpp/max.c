/* run.config
   OPT: -rpp
*/

/*@ requires \valid(t+(0..n));
  @ requires n >= 1;
  @ requires \forall integer k; 0 <= k < n ==> 0 <= t[k];
  @ requires \separated(t+(0..n));
  @ assigns \result \from t[0..n];
  @ ensures \forall integer k; 0 <= k < n ==> \result >= t[k];
  @ ensures \exists integer k; 0 <= k < n && \result == t[k];
*/
int f(int t[], int n){
  int max = t[0];
  int i = 0;
  /*@ loop assigns i,max;
    @ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer k; 0 <= k < i ==> max >= t[k];
    @ loop invariant \exists integer k; 0 <= k < n && max == t[k];
    @ loop variant n-i;
  */
  while(i < n){
    if(t[i] > max){
      max = t[i];
    }
    i++;
  }
 return max;
}

/*@ relational
      \forall int *t1,*t2,*tn,*t;
      \callset(\call(0,f,t1,2,id1),
               \call(0,f,t2,2,id2),\call(0,f,tn,2,id3),\call(0,f,t,4,id4))
      ==>
      (\at(tn[0],Pre_id3) == \callresult(id1) &&
       \at(tn[1],Pre_id3) == \callresult(id2) &&
       \at(t[0],Pre_id4) == \at(t1[0],Pre_id1) &&
       \at(t[1],Pre_id4) == \at(t1[1],Pre_id1) &&
       \at(t[2],Pre_id4) == \at(t2[0],Pre_id2) &&
       \at(t[3],Pre_id4) == \at(t2[1],Pre_id2)) ==>
       \callresult(id3) == \callresult(id4);
*/

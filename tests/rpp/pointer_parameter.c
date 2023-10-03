/* run.config
   OPT: -rpp
*/

/*@ axiomatic Sum {
  @   // sum(t,i,j) denotes t[i]+...+t[j-1]
  @   logic integer sum{L}(int *t, integer i, integer j)
  @        reads i,j,t, t[..] ;
  @   axiom sum1{L} :
  @     \forall int *t, integer i, j; i >= j ==> sum(t,i,j) == 0;
  @   axiom sum2{L} :
  @     \forall int *t, integer i, j; i <= j ==>
  @       sum(t,i,j+1) == sum(t,i,j) + t[j];
  @ }
  @*/

/*@ lemma sum3{L} :
  @     \forall int *t, integer i, j, k;
  @       i <= j <= k ==>
  @         sum(t,i,k) == sum(t,i,j) + sum(t,j,k);
  @*/

/*@ lemma sum_footprint{L} :
  @     \forall int *t1,*t2, integer i, j;
  @       (\forall integer k; i<=k<j ==> t1[k] == t2[k]) ==>
  @       sum(t1,i,j) == sum(t2,i,j);
  @*/

/*@ requires n > 0;
  @ requires \valid(t+(0..n));
  @ assigns \result \from n,t[0..n];
*/
int f (int n, int t[]){

  int i = 0;
  int s = 0;

  /*@ loop invariant 0 <= i <= n && s == sum(t,0,i);
    @ loop assigns s,i;
    @ loop variant n-i;
  */
  for(i=0; i < n; i++){
    s = s + t[i];
  }
  return s;
}

/*@ relational
     \forall int n, int *t1,*t2;
     \callset(\call(f,n,t1,id1),\call(0,f,n,t2,id2)) ==>
     (\forall int k; 0 <= k < n ==> \at(t1[k],Pre_id1) == \at(t2[k],Pre_id2))
     ==>
     \callresult(id1) == \callresult(id2) + \at(t2[n-1],Pre_id1);
*/


/*@ requires n > 0;
  @ requires \valid(t+(0..n));
  @ assigns \result \from n,t[0..n];
*/
int g (int n, int t[]);

/*@ relational
      \forall int n, int *t1,*t2;
       \callset(\call(g,n,t1,id3),\call(0,g,n,t2,id4)) ==>
       (\forall int k; 0 <= k < n ==>
           \at(t1[k],Pre_id3) == \at(t2[k],Pre_id4))
       ==>
       \callresult(id3) == \callresult(id4) + \at(t2[n-1],Pre_id4);
*/

/*@ requires 10 > n > 0;
  @ requires \valid(t+(0..n));
  @ assigns \result \from n,t[0..n];
*/
int k (int t[],int n);

/*@ relational
      \forall int *t1; \callset(\call(k,t1,t1[9],id5)) ==>
        \callresult(id5) == \at(t1[10],Pre_id5);
*/


/*@ requires 10 > n > 0;
  @ requires \valid(t+(0..n));
  @ assigns \result \from n,t[0..n];
*/
int p (int t[], int n){
  return t[n];
}

/*@ relational \forall int *t1; \callset(\call(p,t1,t1[9],id6)) ==>
  \callresult(id6) == \at(t1[10],Pre_id6);
*/

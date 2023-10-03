/* run.config
   OPT: -rpp
*/

/*@ requires x >= 0;
  @ assigns \result \from x; */
int fact(int x) {
  if(x <= 1){
      return 1;
    }
else{
  return x*fact(x-1);
 }
}

/*@ relational \forall int x1; x1 <= 1 ==> \callpure(1,fact,x1) == 1; */
/*@ relational \forall int x1; x1 > 1 ==>
      \callpure(1,fact,x1) == \callpure(0,fact,x1-1)*(x1); */
/*@ relational
      \forall int x1; x1 > 1 ==>
      \callpure(1,fact,x1) == \callpure(1,fact,x1-1)*(x1);
*/
/*@ relational \forall int x1; \callpure(2,fact,x1+1) == 1; */
/*@ relational \forall int x1;
      x1 > 1 ==> \callpure(0,fact,x1-1)*(x1) == \callpure(1,fact,x1);
*/

/*@ requires x >= 0;
  @ assigns \result \from x;
*/
int fact_exact(int x) {
  if(x <= 1){
      return 1;
    }
else{
  return x*fact_exact(x-1);
 }
}

/*@ relational \forall int x1; x1 <= 1 ==> \callpure(1,fact_exact,x1) == 1; */
/*@ relational \forall int x1; x1 == 2 ==> \callpure(1,fact_exact,x1) == \callpure(1,fact_exact,x1-1)*(x1); */
/*@ relational \forall int x1; x1 > 3 ==> \callpure(1,fact_exact,x1) == \callpure(1,fact_exact,x1-1)*(x1); */


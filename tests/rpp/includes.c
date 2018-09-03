/* run.config
   OPT: -rpp
*/

#include <stdint.h>

uint8_t y;

/*@ requires x > 0;
  @ assigns \result \from x;
  @ relational \forall uint32_t x1, x2; x1 < x2 ==> \callpure(f,x1) < \callpure(f,x2);*/
uint32_t f(uint32_t x){
  return x + 1;
}

/*@ assigns \result \from y;
  @ relational \callset(\call(g,id1)) ==> 0 == 0;*/
uint32_t g(){
  return y ;
}

/*@ assigns \result \from y;
  @ relational \callset(\call(k,id1)) ==> \callresult(id1) == 0;*/
uint32_t k(){
  return y;
}

uint8_t *x;

/*@ assigns \result \from *x;
  @ relational \callset(\call(h,id1)) ==> \callresult(id1) == 0;*/
uint8_t h(){
  return *x;
}

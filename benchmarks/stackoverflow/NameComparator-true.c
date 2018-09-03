/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.xluat.com/questions/31235938/java-order-by-priority-list
 *
 */

struct MyClass{
  int Name;
};

/*@ assigns \result \from x,y;
  @ ensures x < y ==> \result == -1;
  @ ensures x > y ==> \result == 1;
  @ ensures x == y ==> \result == 0;
*/
int IntCompare(int x, int y);

/*@ requires \valid(t+(0..2));
  @ assigns \result \from o1,o2,t[0..2];
  @ relational \forall struct MyClass x1,x2, int * t; \callpure(compare,x1,x2,t) == -(\callpure(compare,x2,x1,t));
  @ relational \forall struct MyClass x1,x2,x3, int *t; (\callpure(compare,x1,x2,t) > 0 && \callpure(compare,x2,x3,t) > 0) ==> \callpure(compare,x1,x3,t) > 0;
  @ relational \forall struct MyClass x1,x2,x3, int *t; \callpure(compare,x1,x2,t) == 0 ==> (\callpure(compare,x1,x3,t) == \callpure(compare,x2,x3,t));
*/
int compare(struct MyClass o1, struct MyClass o2, int *t){
  int x = o1.Name;
  int y = o2.Name;
  if (x == y) {
    return 0;
  }

  int i = 0;
  /*@ loop invariant 0 ≤ i ≤ 3;
      loop invariant ∀ ℤ k; 0 ≤ k < i ⇒ *(t + k) ≢ x ∧ *(t + k) ≢ y;
      loop assigns i;
  */
  while (i < 3) {
    if (*(t + i) == x) {
      return 1;
    }
    if (*(t + i) == y) {
      return -1;
    }
    i ++;
  }
  return IntCompare(x,y);
}

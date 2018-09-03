/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/23907134/comparing-two-arrays-using-dictionary-order-in-an-array-of-arrays-java
 *
 */

struct AInt{
  int t[1000];
  int length;
};


/*@ requires 0 <= o1.length && o1.length < 1000;
  @ requires 0 <= o2.length && o2.length < 1000;
  @ assigns \result \from o1,o2;
  @ relational \forall struct AInt x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct AInt x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct AInt x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct AInt o1, struct AInt o2){
    int index, aentry, bentry;
    index = 0;
    /*@ loop invariant 0 <= index && index <= o2.length && index <= o1.length;
      @ loop invariant \forall integer k; 0 <= k < index ==> o1.t[k] == o2.t[k];
      @ loop assigns index,aentry,bentry;*/
    while ((index < o1.length) && (index < o2.length)) {
      aentry = o1.t[index];
      bentry = o2.t[index];
      if (aentry < bentry) {
	return -1;
      }
      if (aentry > bentry) {
	return 1;
      }
      index++;
    }
    return 0;
  }

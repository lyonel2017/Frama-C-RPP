/* run.config
   OPT: -rpp
*/

/*
 * Based on http://codedbot.com/questions/5112702/comparison-method-violates-its-general-contractarraylist-comprasion
 *
 */

struct Word{
  int count;
  int i[1000];
  int length;
};

/*@ type invariant NzbFile_is_bool(struct Word s) =
  s.length >= 0 && s.length < 1000;*/

/*@ assigns \result \from x,y;
  @ ensures x < y ==> \result == -1;
  @ ensures x > y ==> \result == 1;
  @ ensures x == y ==> \result == 0;
*/
int IntCompare(int x, int y);

/*@ requires 0 <= o1.length && o1.length < 1000;
  @ requires 0 <= o2.length && o2.length < 1000;
  @ assigns \result \from o1,o2;
  @ relational \forall struct Word x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct Word x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct Word x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct Word o1, struct Word o2) {
  int left = o1.count;
  int right = o2.count;

  if (left == right) {
    if(o1.length > o2.length){
      int i1 = 0;
      /*@ loop assigns i1;
	@ loop invariant \forall integer k; 0 <= k < i1 ==> o1.i[k] >= o2.i[k];
	@ loop invariant 0 <= i1 <= o1.length;*/
      while (i1 < o1.length){
	if(IntCompare(o1.i[i1], o2.i[i1]) < 0)
	  return 1;
	i1++;
      }
      return -1;
    }
    else {
      int i2 = 0;
      /*@ loop assigns i2;
	@ loop invariant \forall integer k; 0 <= k < i2 ==> o1.i[k] >= o2.i[k];
	@ loop invariant 0 <= i2 <= o2.length;*/
      while(i2 < o2.length){
	if(IntCompare(o1.i[i2], o2.i[i2]) < 0)
	  return -1;
	i2++;
      }
      return 1;
    }
  }
  else return (left > right)? 1:-1;
}

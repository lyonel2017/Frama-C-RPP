/* run.config
   OPT: -rpp
*/

/* http://stackoverflow.com/questions/30449488/comparison-method-violates-its-general-contract-everything-seems-ok */

struct PokerHand{
  int hand[13];
};

/*@ assigns \result \from o1,val;
  @ behavior some:
  assumes \exists integer i; 0 <= i < 13 && o1.hand[i] == val;
  assigns \result \from o1,val;
  ensures 0 <= \result < 13;
  ensures o1.hand[\result] == val;
  ensures \forall integer i; 0 <= i < \result ==> o1.hand[i] != val;
  @ behavior none:
  assumes \forall integer i; 0 <= i < 13 ==> o1.hand[i] != val;
  assigns \result \from o1,val;
  ensures \result == -1;*/
int indexOf(struct PokerHand o1, int val);

/*@ assigns \result \from o1,val;
  @ behavior some:
  assumes \exists integer i; 0 <= i < 13 && o1.hand[i] == val;
  assigns \result \from o1,val;
  ensures 0 <= \result < 13;
  ensures o1.hand[\result] == val;
  ensures \forall integer i; \result < i < 13  ==> o1.hand[i] != val;
  @ behavior none:
  assumes \forall integer i; 0 <= i < 13 ==> o1.hand[i] != val;
  assigns \result \from o1,val;
  ensures \result == -1;*/
int lastIndexOf(struct PokerHand o1, int val);

/*@ axiomatic CountAxiomatic{
  logic integer Count{L}(struct PokerHand a, integer n, int v)
  reads a.hand[0..n-1];
  axiom CountEmpty: \forall struct PokerHand a, int v, integer n;  n <= 0 ==>  Count(a, n, v) == 0;
  axiom CountOneHit: \forall struct PokerHand a, int v, integer n; a.hand[n] == v  ==>  Count(a, n + 1, v) == Count(a, n, v) + 1;
  axiom CountOneMiss: \forall struct PokerHand a, int v, integer n; a.hand[n] != v  ==>  Count(a, n + 1, v) == Count(a, n, v);
  }
*/

/*@ assigns \result \from o1, val;
  @ ensures \result == Count(o1, 13, val);
  @ ensures 0 <= \result <= 13;*/
int countOccurrencesOf(struct PokerHand o1, int val);

/*@ assigns \result \from o1,i;
  @ ensures \result == o1.hand[i];*/
int charAt(struct PokerHand o1, int i);

/*@ assigns \result \from o1,o2;
  @ relational \forall struct PokerHand x1,x2; \callpure(compare1,x1,x2) == -(\callpure(compare1,x2,x1));
  @ relational \forall struct PokerHand x1,x2,x3; (\callpure(compare1,x1,x2) > 0 && \callpure(compare1,x2,x3) > 0) ==> \callpure(compare1,x1,x3) > 0;
  @ relational \forall struct PokerHand x1,x2; \callpure(indexOf,x1,4) != \callpure(indexOf,x2,4) ==> \callpure(1,compare1,x1,x2) == \callpure(indexOf,x1,4) - \callpure(indexOf,x2,4);
  @ relational \forall struct PokerHand x1,x2,x3; \callpure(compare1,x1,x2) == 0 ==> (\callpure(compare1,x1,x3) == \callpure(compare1,x2,x3));
*/
int compare1(struct PokerHand o1, struct PokerHand o2){
  if (indexOf(o1,4) == indexOf(o2,4)) {
    int i1 = 0;
    /*@ loop invariant 0 <= i1 <= 13;
      @ loop assigns i1;
      @ loop invariant \forall integer k; 0 <= k < i1 ==> ((o1.hand[k] == 0) || (o1.hand[k] == 4)) && ((o2.hand[k] == 0) || (o2.hand[k] == 4));*/
    while(i1 <= 12){
      if ((charAt(o1,i1) != 0) && (charAt(o1,i1) != 4) && (charAt(o2,i1) != 0) && (charAt(o2,i1) != 4)) {
	return 0;
      }
      if ((charAt(o1,i1) != 0) && (charAt(o1,i1) != 4)) {
	return -1;
      }
      if ((charAt(o2,i1) != 0) && (charAt(o2,i1) != 4)) {
	return 1;
      }
      i1++;
    }
  }
  return indexOf(o1,4) - indexOf(o2,4);
}

/*@ assigns \result \from o1,o2;
  @ relational \forall struct PokerHand x1,x2; \callpure(compare2,x1,x2) == -(\callpure(compare2,x2,x1));
  @ relational \forall struct PokerHand x1,x2,x3; (\callpure(compare2,x1,x2) > 0 && \callpure(compare2,x2,x3) > 0) ==> \callpure(compare2,x1,x3) > 0;
  @ relational \forall struct PokerHand x1,x2,x3; \callpure(compare2,x1,x2) == 0 ==> (\callpure(compare2,x1,x3) == \callpure(compare2,x2,x3));
*/
int compare2(struct PokerHand o1, struct PokerHand o2) {
  int higherTriple = lastIndexOf(o1,3);
  if (higherTriple == lastIndexOf(o2,3)) {
    int i2=0;
    /*@ loop invariant 0 <= i2 <= 13;
      @ loop assigns i2;
      @ loop invariant \forall integer k; 0 <= k < i2 ==>
      (k == higherTriple) || (((o1.hand[k] != 2) && (o1.hand[k] != 3)) && ((o2.hand[k] != 2) && (o2.hand[k] != 3)));*/
    while(i2 <= 12){
      if ((i2 != higherTriple) && (((charAt(o1,i2) == 2) || (charAt(o1,i2) == 3)) && ((charAt(o2,i2) == 2) || (charAt(o2,i2) == 3)))) {
	return 0;
      }
      if ((i2 != higherTriple) && ((charAt(o1,i2) == 2) || (charAt(o1,i2) == 3))) {
	return -1;
      }
      if ((i2 != higherTriple) && ((charAt(o2,i2) == 2) || (charAt(o2,i2) == 3))) {
	return 1;
      }
      i2++;
    }
  }
  return higherTriple - lastIndexOf(o2,3);
}

/*@ assigns \result \from o1,o2;
  @ relational \forall struct PokerHand x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct PokerHand x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct PokerHand x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct PokerHand o1, struct PokerHand o2) {
  if ((indexOf(o1,4) != -1) || (indexOf(o2,4) != -1)) {  // Four of a kind
    return compare1(o1,o2);
  }
  int tripleCount1 = countOccurrencesOf(o1,3);
  int tripleCount2 = countOccurrencesOf(o2,3);
  if ((tripleCount1 > 1) || ((tripleCount1 == 1) && (indexOf(o1,2) != -1)) || (tripleCount2 > 1) || ((tripleCount2 == 1) && (indexOf(o2,2) != -1))) {  // Full house
    return compare2(o1,o2);
  }
  return 0;
}

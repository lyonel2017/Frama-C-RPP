/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/11441666/java-error-comparison-method-violates-its-general-contract
 *
 */

struct CollectionItem{
    int cardSet;
    int cardRarity;
    int cardId;
    int cardType;
};

/*@ assigns \result \from o1,o2; */
int compare (struct CollectionItem o1, struct CollectionItem o2) {
    if (o1.cardSet > o2.cardSet) {
	return 1;
    }
    if (o1.cardSet < o2.cardSet) {
	return -1;
    }
    if (o1.cardRarity < o2.cardRarity) {
	return 1;
    }
    if (o1.cardRarity > o2.cardRarity) {
	return -1;
    }
    if (o1.cardId > o2.cardId) {
	return 1;
    }
    if (o1.cardId < o2.cardId) {
	return -1;
    }
    return o1.cardType - o2.cardType;  //watch out for overflow!
}

/*@ relational
      \forall struct CollectionItem x1,x2;
      \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
*/

/*@ relational
      \forall struct CollectionItem x1,x2,x3;
      (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0)
      ==> \callpure(compare,x1,x3) > 0;
*/

/*@ relational
      \forall struct CollectionItem x1,x2,x3;
      \callpure(compare,x1,x2) == 0 ==>
      (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/

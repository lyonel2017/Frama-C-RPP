/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.xluat.com/questions/30824837/using-comparable-to-compare-different-variables
 *
 */

struct IsoSprite{
  int minX;
  int maxX;
  int minY;
  int maxY;
  int minZ;
  int maxZ;
};

/*@ assigns \result \from o1,o2;
  @ relational \forall struct IsoSprite x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct IsoSprite x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct IsoSprite x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct IsoSprite o1, struct IsoSprite o2){
  if ((o2.maxX > o1.minX) && (o2.maxY > o1.minY) && (o2.minZ < o1.maxZ)){
    return -1;
  }else if((o2.maxX < o1.minX) && (o2.maxY < o1.minY) && (o2.minZ > o1.maxZ)){
    return 1;
  }

  return 0;
}

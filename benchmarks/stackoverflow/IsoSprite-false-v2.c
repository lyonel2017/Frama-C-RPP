/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.xluat.com/questions/30824837/using-comparable-to-compare-different-variables
 *
 */

#include <stdio.h>

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
  if ((o2.maxX > o1.minX) && (o2.maxY > o1.minY) && (o2.minZ < o1.maxZ)) {
    return -1;
  } else if ((o2.maxX > o1.minX) && (o2.maxY > o1.minY) && (o2.minZ > o1.maxZ)) {
    return 1;
  }else if ((o2.maxX < o1.minX) && (o2.maxY > o1.minY) && (o2.minZ > o1.maxZ)) {
    return 1;
  }else if ((o2.maxX < o1.minX) && (o2.maxY < o1.minY) && (o2.minZ > o1.maxZ)) {
    return 1;
  }else if ((o2.maxX < o1.minX) && (o2.maxY > o1.minY) && (o2.minZ < o1.maxZ)) {
    return 1;
  }else if ((o2.maxX > o1.minX) && (o2.maxY < o1.minY) && (o2.minZ > o1.maxZ)) {
    return 1;
  }else if ((o2.maxX < o1.minX) && (o2.maxY < o1.minY) && (o2.minZ > o1.maxZ)) {
    return 1;
  }else if ((o2.maxX > o1.minX) && (o2.maxY < o1.minY) && (o2.minZ < o1.maxZ)) {
    return 1;
  }else if ((o2.maxX < o1.minX) && (o2.maxY > o1.minY) && (o2.minZ < o1.maxZ)) {
    return 1;
  }else if(&o1 != &o2){
        return 1;
  }
  return 0;
}

int main(){
  struct IsoSprite x1 = {1,1,1,1,1,1};
  struct IsoSprite x2 = {2,2,2,2,1,-1};
  struct IsoSprite x3 = {1,3,1,3,0,1};
  int test1 = compare(x1,x2);
  int test2 = compare(x1,x3);
  int test3 = compare(x2,x3);
  printf("First compare %d \n",test1);
  printf("Second compare %d \n",test2);
  printf("Third compare %d \n",test3);
  return 1;
}

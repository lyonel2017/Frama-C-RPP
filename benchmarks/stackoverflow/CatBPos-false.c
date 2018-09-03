/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/22768302/why-i-get-comparison-method-violates-its-general-contract
 *
 */

struct CatBPos{
  int getHdopBPosGetTime;
  int getBPosGetTime;
  int getBPosGetStat;
  int getBPosIsDeparture;
  int getBPosIsVacation;
  int getBPosIsArrival;
  int getHdopBPosGetTimeIsNotVoid;
};

/*@ assigns \result \from x,y;
  @ relational \forall int x1,x2; \callpure(IntCompare,x1,x2) == -(\callpure(IntCompare,x2,x1));
  @ relational \forall int x1,x2,x3; (\callpure(IntCompare,x1,x2) > 0 && \callpure(IntCompare,x2,x3) > 0) ==> \callpure(IntCompare,x1,x3) > 0;
  @ relational \forall int x1,x2,x3; \callpure(IntCompare,x1,x2) == 0 ==> (\callpure(IntCompare,x1,x3) == \callpure(IntCompare,x2,x3));
*/
int IntCompare(int x, int y){
  if (x < y){
    return -1;
  }
  if(x > y){
    return 1;
  }

  return 0;
}

/*@ assigns \result \from o1,o2;
  @ relational \forall struct CatBPos x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct CatBPos x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct CatBPos x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct CatBPos o1, struct CatBPos o2) {
  int lCompare;

  if (o1.getHdopBPosGetTimeIsNotVoid && o2.getHdopBPosGetTimeIsNotVoid) {
    lCompare = IntCompare(o1.getHdopBPosGetTime, o2.getHdopBPosGetTime);
    if (lCompare != 0) {
      return lCompare;
    }
  }

  lCompare = IntCompare(o1.getBPosGetTime, o2.getBPosGetTime);
  if (lCompare != 0) {
    return lCompare;
  }

  if (o1.getBPosIsDeparture && o2.getBPosIsVacation) {
    return 1;
  } else if (o1.getBPosIsVacation && o2.getBPosIsArrival) {
    return 1;
  }

  // Ankunft und Abfahrt für denselben Bahnhof sollen in der richtigen Reihenfolge sein
  if (o1.getBPosIsDeparture && o2.getBPosIsArrival && (o1.getBPosGetStat == o2.getBPosGetStat)) {
    return 1;
  }

  return 0;
}

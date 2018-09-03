/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/26322215/comparison-logic-error-with-economic-data-comparison-method-violates-its-gener
 *
 */

struct DataPoint{
  int fiscalQuarter;
  int sectorCode;
  int industryCode;
};

/*@ assigns \result \from x,y;
  @ ensures x < y ==> \result == -1;
  @ ensures x > y ==> \result == 1;
  @ ensures x == y ==> \result == 0;
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
  @ relational \forall struct DataPoint x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct DataPoint x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct DataPoint x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct DataPoint o1, struct DataPoint o2) {
  int fiscalResult = IntCompare(o1.fiscalQuarter,o2.fiscalQuarter);
  if (fiscalResult > 0) {
    return fiscalResult;
  }
  if (fiscalResult < 0) {
    return fiscalResult;
  }
  if (o1.sectorCode > 0) {
    if (o1.sectorCode > o2.sectorCode) {
      return o1.sectorCode - o2.sectorCode;
    }
    else {
      if (o1.sectorCode < o2.sectorCode){
	return o2.sectorCode - o1.sectorCode;
      } else {
	return 0; // Should never happen
      }
    }
  } else {
    if (o1.industryCode > 0) {
      if (o1.industryCode > o2.industryCode) {
	return o1.industryCode - o2.industryCode;
      }
      else {
	if (o1.industryCode < o2.industryCode) {
	  return o2.industryCode - o1.industryCode;
	} else {
	  return 0; // Should never happen
	}
      }
    }// These should never be reached
    else {
      if (o1.sectorCode > 0) {
	return -1;
      } else {
	if (o2.industryCode > 0) {
	  return -1;
	} else {
	  return 0;
	}
      }
    }
  }
}

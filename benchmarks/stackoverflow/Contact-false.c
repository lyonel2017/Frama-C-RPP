/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/26336978/comparison-method-violates-its-general-contract-and-method-compareto
 *
 */
struct Contact{
  int getFirstName;
  int getLastName;
  int getEmails;
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
  @ relational \forall struct Contact x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct Contact x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct Contact x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct Contact o1, struct Contact o2) {
  int compareFirstName = 0;
  if ((o1.getFirstName != 0) && (o2.getFirstName != 0)) {
    compareFirstName = IntCompare(o1.getFirstName, o2.getFirstName);

    if (compareFirstName == 0) {
      int compareLastName = 0;
      if ((o1.getLastName != 0) && (o2.getLastName != 0)) {
	compareLastName = IntCompare(o1.getLastName, o2.getLastName);

	if (compareLastName == 0) {
	  int compareEmail = 0;
	  if ((o1.getEmails != 0) && (o2.getEmails != 0)) {
	    compareEmail = IntCompare(o1.getEmails, o2.getEmails);
	    return compareEmail;
	  } else {
	    return 0;
	  }
	} else {
	  return compareLastName;
	}
      } else {
	int compareEmail = 0;
	if ((o1.getEmails != 0) && (o2.getEmails != 0)) {
	  compareEmail = IntCompare(o1.getEmails, o2.getEmails);
	  return compareEmail;
	} else {
	  return 0;
	}
      }
    } else {
      return compareFirstName;
    }
  } else {
    int compareLastName = 0;
    if ((o1.getLastName != 0) && (o2.getLastName != 0)) {
      compareLastName = IntCompare(o1.getLastName, o2.getLastName);

      if (compareLastName == 0) {
	int compareEmail = 0;
	if ((o1.getEmails != 0) && (o2.getEmails != 0)) {
	  compareEmail = IntCompare(o1.getEmails, o2.getEmails);
	  return compareEmail;
	} else {
	  return 0;
	}
      } else {
	return compareLastName;
      }
    } else {
      int compareEmail = 0;
      if ((o1.getEmails != 0) && (o2.getEmails != 0)) {
	compareEmail = IntCompare(o1.getEmails, o2.getEmails);
	return compareEmail;
      } else {
	return 0;
      }
    }
  }
}

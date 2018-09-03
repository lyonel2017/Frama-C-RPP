/* run.config
   OPT: -rpp
*/

/* 
 * Based on http://stackoverflow.com/questions/20970217/why-does-my-comparison-method-violate-its-general-contract
 *
 */

struct Container{
    int departureTime;
    int departureMaxDuration;
    int departureTransportCompany;
    int departureTransportType;
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
  @ relational \forall struct Container x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct Container x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct Container x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct Container o1, struct Container o2) {
      int rv;

      // Times
      rv = IntCompare(o1.departureTime, o2.departureTime);
      if (rv == 0) {
          // Duration
          if (o1.departureMaxDuration < o2.departureMaxDuration) {
              rv = -1;
          }
          else if (o1.departureMaxDuration > o2.departureMaxDuration) {
              rv = 1;
          }
          else {
              // Transport company
              rv = IntCompare(o1.departureTransportCompany, o2.departureTransportCompany);
              if (rv == 0) {
                  // Transport type
                  rv = IntCompare(o1.departureTransportType, o2.departureTransportType);
              }
          }
      }
      return rv;
  }

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

/*@ assigns \result \from time1,time2;
  @ ensures \result == 1 || \result == 0;*/
int departureTimeIsBefore(int time1, int time2);

/*@ assigns \result \from o1,o2;
  @ relational \forall struct Container x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct Container x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct Container x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct Container o1, struct Container o2) {
    if (departureTimeIsBefore(o1.departureTime,o2.departureTime))
        return -1;
    else if ((o1.departureTime == o2.departureTime) &&
	     (o1.departureMaxDuration == o2.departureMaxDuration) &&
	     (o1.departureTransportCompany == o2.departureTransportCompany) &&
	     (o1.departureTransportType == o2.departureTransportType))
	return 0;
    else
	return 1;
}

/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/10234038/compare-method-throw-exception-comparison-method-violates-its-general-contract
 *
 */

struct Time {
  int ora;
  int volume_totale;
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
  @ relational \forall struct Time x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct Time x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct Time x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare (struct Time o1, struct Time o2) {
  int time1 = o1.ora;
  int time2 = o2.ora;

  int cmp = IntCompare(time1, time2);
  if (cmp == 0){
    int voltot1 = o1.volume_totale;
    int voltot2 = o2.volume_totale;

    cmp = IntCompare(voltot1, voltot2);
  }
  return cmp;
}

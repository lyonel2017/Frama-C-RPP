/* run.config
   OPT: -rpp
*/

/*
 * Based on http://codedbot.com/questions/402185/java-comparator-violates-general-contract
 *
 */

struct SolutionComparator {
  int getValue;
  int solutionCost;
};

/*@ requires \valid(t+(0..1));
  @ assigns \result \from o1,o2,t[0..1];
  @ relational \forall struct SolutionComparator x1,x2, int * t; \callpure(compare,x1,x2,t) == -(\callpure(compare,x2,x1,t));
  @ relational \forall struct SolutionComparator x1,x2,x3, int *t; (\callpure(compare,x1,x2,t) > 0 && \callpure(compare,x2,x3,t) > 0) ==> \callpure(compare,x1,x3,t) > 0;
  @ relational \forall struct SolutionComparator x1,x2,x3, int *t; \callpure(compare,x1,x2,t) == 0 ==> (\callpure(compare,x1,x3,t) == \callpure(compare,x2,x3,t));
*/
int compare(struct SolutionComparator o1, struct SolutionComparator o2, int *t) {
  int v1 = o1.getValue;
  int v2 = o2.getValue;
  if ((v1 == -1) && (v2 == -1))
    return 0;
  else if (v1 == -1)
    return 1;
  else if (v2 == -1)
    return -1;
  else if (v1 == v2){
    //return (int)Math.signum(solutionCost(o1) - solutionCost(o2));
    int comp = o1.solutionCost - o2.solutionCost;
    if (comp > 0)
      return 1;
    else if (comp < 0)
      return -1;
    else
      return 0;
  }
  else {
    //return (int)Math.signum(Math.abs(target-v1) - Math.abs(target-v2));
    int target = t[0];
    int comp1 = target-v1;
    int abscomp1 = 0;
    if (comp1 >= 0)
      abscomp1 = comp1;
    else
      abscomp1 = -comp1;

    int comp2 = target-v2;
    int abscomp2 = 0;
    if (comp2 >= 0)
      abscomp2 = comp2;
    else
      abscomp2 = -comp2;
    int comp3 = abscomp1 - abscomp2;
    if (comp3 > 0)
      return 1;
    else if (comp3 < 0)
      return -1;
    else
      return 0; 
  }
}

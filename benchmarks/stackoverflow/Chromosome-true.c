/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/16809000/how-to-make-the-compareto-method-respect-the-general-contract
 *
 */
struct Chromosome{
  int score[7];
  int isNull;
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

/*@ requires o1.isNull != 0;
  @ assigns \result \from o1,o2;
  @ relational \forall struct Chromosome x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct Chromosome x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct Chromosome x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
  */
int compare(struct Chromosome o1, struct Chromosome o2) {
    if(o2.isNull == 0)
	return(1);
    int comp = 0;
    int i = 0;
    /*@ loop invariant 0 <= i <= 5;
      @ loop invariant \forall integer k; 0 <= k < i ==> o1.score[k] == o2.score[k];
      @ loop assigns comp,i;*/
    while(i < 5){
	comp = IntCompare(o1.score[i], o2.score[i]);
	if (comp!=0)
	    return comp;
	i++;
    }

    return 0;
}

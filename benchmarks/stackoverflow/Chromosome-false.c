/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/16809000/how-to-make-the-compareto-method-respect-the-general-contract
 *
 */

struct Chromosome{
  int score[5];
  int isNull;
};


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
  comp += o1.score[0] == o2.score[0] ? 0 : o1.score[0] > o2.score[0] ? 1 : -1;
  comp += o1.score[1] == o2.score[1] ? 0 : o1.score[1] > o2.score[1] ? 1 : -1;
  comp += o1.score[2] == o2.score[2] ? 0 : o1.score[2] > o2.score[2] ? 1 : -1;
  comp += o1.score[3] == o2.score[3] ? 0 : o1.score[3] > o2.score[3] ? 1 : -1;
  comp += o1.score[4] == o2.score[4] ? 0 : o1.score[4] > o2.score[4] ? 1 : -1;
  if(comp == 0)
    return(0);
  if(comp > 0)
    return(1);
  else
    return(-1);
}

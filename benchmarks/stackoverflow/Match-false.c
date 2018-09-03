/* run.config
   OPT: -rpp
*/

/*
 * Based on http://codedbot.com/questions/5138521/comparison-method-violates-its-general-contract-overlapping-conditions 
 * 
 */

struct Match{
  int score;
  int seq1start;
  int seq2start;
};

/*@ assigns \result \from o1,o2;
  @ relational \forall struct Match x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct Match x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct Match x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct Match o1, struct Match o2) {
  if(o1.score > o2.score)
    return -1;
  if((o1.score == o2.score) && ((o1.seq1start < o2.seq1start) && (o1.seq2start < o2.seq2start))) 
    return -1;
  if((o1.score == o2.score) && !((o1.seq1start < o2.seq1start) && (o1.seq2start < o2.seq2start)))
    return 0;
  return 1;
}

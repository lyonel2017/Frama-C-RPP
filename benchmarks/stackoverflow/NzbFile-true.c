/* run.config
   OPT: -rpp
*/

/*
 * Based on http://sohu.io/questions/2211707/comparison-method-violates-its-general-contract
 * Not working yet: the first hyper property cannot be valid in the implement given be Marcelo Sousa and Isil Dillig.
                    The return value must be symetric.
 */

#include <stdio.h>

struct NzbFile{
  int* FileName;
  int getFileName_toLowerCase_endsWith[5];
  int Subject;
};

/*@ type invariant NzbFile_is_bool(struct NzbFile s) =
  \forall integer k; 0 <= k < 5
  ==> (s.getFileName_toLowerCase_endsWith[k] == 0 || s.getFileName_toLowerCase_endsWith[k] == 1);*/

/*@ assigns \result \from x,y;
  @ ensures x < y ==> \result == -1;
  @ ensures x > y ==> \result == 1;
  @ ensures x == y ==> \result == 0;
*/
int IntCompare(int x, int y);

/*@ assigns \result \from o1,o2;
  @ relational \forall struct NzbFile x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct NzbFile x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct NzbFile x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare(struct NzbFile o1, struct NzbFile o2){
  if ((o1.FileName != NULL) && (o2.FileName != NULL)){
    int i = 0;
    /*@ loop assigns i;
      @ loop invariant 0 <= i <= 5;
      @ loop invariant \forall integer k; 0 <= k < i ==> o1.getFileName_toLowerCase_endsWith[k] == 0 && o2.getFileName_toLowerCase_endsWith[k] == 0;
    */
    while (i < 5){
      if(o1.getFileName_toLowerCase_endsWith[i] && o2.getFileName_toLowerCase_endsWith[i]){
	return 0;
      }
      if(o1.getFileName_toLowerCase_endsWith[i]){
	return -1000 - i;
      }
      if(o2.getFileName_toLowerCase_endsWith[i]){
	return 1000 + i;
      }
      i++;
    }
    return IntCompare(o1.FileName, o2.FileName);
  }
  else if ((o1.FileName != NULL) && (o2.FileName == NULL))
    {
      return -1005;
    }
  else if ((o1.FileName == NULL) && (o2.FileName != NULL))
    {
      return 1005;
    }
  else
    {
      return IntCompare(o1.Subject, o2.Subject);
    }
}

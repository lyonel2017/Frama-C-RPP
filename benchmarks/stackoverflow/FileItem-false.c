/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/30458633/why-does-my-compare-methd-throw-illegalargumentexception-sometimes
 *
 */

#include <stdio.h>

struct FileItem{
  int *FileName;
  int *toInt;
};

/*@ assigns \result \from o1,o2;
  @ relational \forall struct FileItem x1,x2; \callpure(compare,x1,x2) == -(\callpure(compare,x2,x1));
  @ relational \forall struct FileItem x1,x2,x3; (\callpure(compare,x1,x2) > 0 && \callpure(compare,x2,x3) > 0) ==> \callpure(compare,x1,x3) > 0;
  @ relational \forall struct FileItem x1,x2,x3; \callpure(compare,x1,x2) == 0 ==> (\callpure(compare,x1,x3) == \callpure(compare,x2,x3));
*/
int compare (struct FileItem o1, struct FileItem o2) {
  int result = 0;
  if ((o1.toInt != NULL) && (o2.toInt != NULL)) {

    int* n1 = o1.FileName;
    int* n2 = o2.FileName;

    if ((n1 != NULL) && (n2 != NULL))
      result = n1 - n2; //n1.compareTo(n2);
  }

  return result;
}

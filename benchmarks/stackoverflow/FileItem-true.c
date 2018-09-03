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
  if (o1.toInt == NULL){
    if (o2.toInt == NULL){
      return 0;
    } else {
      return 1;
    }
  } else if (o2.toInt == NULL) {
    return -1;
  }

  int* n1 = o1.FileName;
  int* n2 = o2.FileName;

  if (n1 == NULL) {
    if (n2 == NULL) {
      return 0;
    } else {
      return 1;
    }
  } else if (n2 == NULL) {
    return -1;
  }
  return n1 - n2;
}

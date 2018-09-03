/* run.config
   OPT: -rpp
*/

/*
 * Based on http://sohu.io/questions/2211707/comparison-method-violates-its-general-contract
 *
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
    if (o1.getFileName_toLowerCase_endsWith[0]) // ".nfo"
      return -1000;
    else if (o2.getFileName_toLowerCase_endsWith[0]) // ".nfo"
      return 1000;
    else if (o1.getFileName_toLowerCase_endsWith[1]) // ".sfv"
      return -999;
    else if (o2.getFileName_toLowerCase_endsWith[1]) // ".sfv"
      return 1001;
    else if (o1.getFileName_toLowerCase_endsWith[2]) // ".srr"
      return -998;
    else if (o2.getFileName_toLowerCase_endsWith[2]) // ".srr"
      return 1002;
    else if (o1.getFileName_toLowerCase_endsWith[3]) // ".nzb"
      return -997;
    else if (o2.getFileName_toLowerCase_endsWith[3]) // ".nzb"
      return 1003;
    else if (o1.getFileName_toLowerCase_endsWith[4]) //".srt"
      return -996;
    else if (o2.getFileName_toLowerCase_endsWith[4]) // ".srt"
      return 1004;
    else
      return IntCompare(o1.FileName, o2.FileName);
  }
  else if ((o1.FileName != NULL) && (o2.FileName == NULL))
    {
      return -995;
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

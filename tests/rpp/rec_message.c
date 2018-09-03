/* run.config
   OPT: -rpp
*/

int message;

/*@ assigns message \from x,message;
  @ relational \forall int x1; \callset(\call(f,x1,id2), \call(f,x1-1,id3)) ==> x1 > 0 ==> \at(message,Pre_id2) == \at(message,Pre_id3) ==> \at(message,Post_id2) == 1 + \at(message,Post_id3);
  @ ensures x <= 0 ==> \at(message,Post) == \at(message,Pre);
  @ ensures x > 0 ==> \at(message,Pre) + x == \at(message,Post);
*/
void f(int x){
  if(x > 0){
    f(x-1);
    message = message + 1;
  }
  return;
}

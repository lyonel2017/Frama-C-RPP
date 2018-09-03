/* run.config
   OPT: -rpp
*/

int message;

/*@ assigns message \from message,key;*/
void Cryptage(int key){
	message =  message + key;
}
/*@ assigns message \from message,key;
  @ relational \forall int key; \rela(\callset(\call(Cryptage,key,id1),\call(DeCryptage,key,id2)), \at(message,Post_id1) == \at(message,Pre_id2) ==> \at(message,Pre_id1) == \at(message,Post_id2));*/
void DeCryptage(int key){
	message = message - key;
}

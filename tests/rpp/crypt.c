/* run.config
   OPT: -rpp
*/

/*@ requires key >= 0 && t > 0;
  @ assigns \result \from t, key;
*/
int Cryptage(int t,int key){
	return t + key;
}

/*@ requires key >= 0 && t > 0;
  @ relational \forall int t,key; \callpure(DeCryptage,\callpure(Cryptage,t,key),key) == t;
  @ relational \forall int t,key; \callpure(Cryptage,t,key) > 0;
  @ assigns \result \from t, key;
 */
int DeCryptage(int t, int key){
	return t - key;
}

/*@ requires x > 0;
  @ ensures \result == x;
*/
int main(int x){
  int k = 5;
  int inter;
  inter = Cryptage(x,k);
  inter = DeCryptage(inter,k);
  return inter;
}

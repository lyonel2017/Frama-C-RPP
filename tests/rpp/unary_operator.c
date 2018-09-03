/* run.config
   OPT: -rpp
*/

/*@ relational \forall int x1,x2; x1 == -x2 && x1 != 0 ==> \callpure(f,x1) + \callpure(f,x2) == 1;
  @ relational \forall int x1; x1 != 0 ==> \callpure(f,x1) + \callpure(f,-x1) == 1;
  @ assigns \result \from x;
*/
int f( int x){
	if(x > 0)return 0;
	else return 1;
}

/* run.config
   OPT: -rpp
*/
int y = 0;

/*@ assigns \result \from x; */
int f1(int x){
	return x + 1;
}

/*@ relational
      \forall int x1,x2; x1 < x2 ==> \callpure(f1,x1) < \callpure(f1,x2);
*/

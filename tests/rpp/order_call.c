/* run.config
   OPT: -rpp
*/

/*@ relational \forall int n; \callpure(f,n) == \callpure(f,\callpure(f,n));
  @ assigns \result \from a;*/
int f (int a){
	return 2;
}

/*@ relational \forall int n; \callpure(toupper,n) == \callpure(toupper,\callpure(toupper,n));
  @ assigns \result \from c;*/
int toupper(int c) {
	if(c>='a' && c<='z') return('A' + c - 'a');
	else return(c);
}

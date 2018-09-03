/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x;
  @ relational \forall int x1; \callpure(f,\callpure(f,x1)) == \callpure(f,x1);*/
int f(int x){
	int buff = -1;
	if(x >= 0) {
	  buff = 1;
	  goto end;
	}
	goto end;

	end: return buff;
}

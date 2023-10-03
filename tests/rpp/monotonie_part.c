/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x; */
int f(int x){
	int buff = 10;
	if(x > 10) goto end;

	buff = x + 2*x + x*75;
	goto end;

	end: return buff;
}

/*@ relational
      \forall int x1,x2;
         x1 < x2 && x1 > 0 && x2 < 10 ==> \callpure(f,x1) < \callpure(f,x2);
*/

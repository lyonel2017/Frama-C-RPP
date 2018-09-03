/* run.config
   OPT: -rpp
*/

/*@ relational \forall int a,b,c; \callpure(trityp,a,b,c) == \callpure(trityp,a,c,b);
  @ assigns \result \from i,j,k;
*/
int trityp(i,j,k){
	int trityp = 0;

	if(i==0 || j==0 || k==0) return 4;
	else {
		trityp=0;
		if(i==j) trityp = trityp+1;
		if(i==k) trityp = trityp+2;
		if(j==k) trityp = trityp+3;
		if(trityp==0){
			if((i+j)<=k || (j+k)<=i || (i+k) <=j)
				trityp = 4;
			else 
				trityp = 1;
		}
		else {
			if(trityp>3) trityp = 3;
			else {
				if(trityp==1 && (i+j)>k){
					trityp = 2;
				}
				else {
					if(trityp==2 && (i+k)>j){
						trityp = 2;
					}
					else {
						if(trityp==3 && (j+k)>i){
							trityp = 2;
						}
						else {
							trityp = 4;
						}
					}
				}
			}
		}
		return trityp;
	}
}

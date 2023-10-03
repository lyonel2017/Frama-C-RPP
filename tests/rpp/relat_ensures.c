/* run.config
   OPT: -rpp
*/

/*@ assigns \result \from x; */
int g(int x){
	return 2 + x;
}

/*@ relational \forall int x1; x1 > 0 ==> \callpure(g,x1) == x1 + 2;*/

/*@ assigns \result \from x; */
int f(int x){
	return x + 5;
}

/*@ relational \forall int x1; x1 > 0 ==> \callpure(f,x1) == x1 + 5;*/

/*@ assigns \result \from x; */
int h(int x){
	return f(x) + g(x);
}

/*@ relational \forall int x1; x1 > 0 ==> \callpure(f,x1) < \callpure(h,x1);*/

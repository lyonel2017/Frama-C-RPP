/* run.config
   OPT: -rpp -rpp-pro
   OPT: -rpp -rpp-hyp
   OPT: -rpp
*/

/*@ assigns \result \from x; */
int f(int x);

/*@ relational
     \forall int x1,x2; x1 < x2 ==> \callpure(f,x1) < \callpure(f,x2);
*/


/*@ assigns \result \from x; */
int g(int x){
  return f(x);
}

/*@ relational
      \forall int x1,x2; x1 < x2 ==> \callpure(g,x1) < \callpure(g,x2);
*/

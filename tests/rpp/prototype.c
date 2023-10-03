/* run.config
   OPT: -rpp -rpp-hyp
   OPT: -rpp -rpp-pro
   OPT: -rpp
*/

int x;

/*@ assigns \result \from x; */
int f(int x);

/*@ relational 1 < 2; */
/*@ relational
      \forall int x1,x2; x1 < x2 ==> \callpure(f,x1) < \callpure(f,x2);
*/

/*@ assigns \result \from x; */
int g(int x);

/*@ relational \forall int x1,x2; x1 < x2 ==> \callpure(f,x1) < \callpure(g,x2);
*/


/*@ assigns x \from x; */
int k();

/*@ relational
      \rela(
        \callset(\call(k,id1),\call(k,id2)),
        \at(x,Pre_id1) < \at(x,Pre_id2) ==>
          \at(x,Post_id1) < \at(x,Post_id2) &&
          \callresult(id1) == \callresult(id2));
*/

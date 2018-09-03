/* run.config
   OPT: -rpp
*/

/*@ relational \forall int x1,x2; x1 < x2 ==> \callpure(f1,x1) < \callpure(f1,x2);
  @ assigns \result \from x;
*/
int f1(int x){
    return x + 1;
}

/*@ relational \forall int x1,x2; \callset(\call(f2,x1,id1),\call(f2,x2,id2)) ==> x1 < x2 ==> \callresult(id1) < \callresult(id2);
  @ assigns \result \from x;*/
int f2(int x){
    return f1(x);
}


/*@ relational \forall int x1,x2; \callset(\call(f3,x1,id3),\call(f3,x2,id4)) ==> x1 < x2 ==> \callresult(id3) < \callresult(id4);
  @ assigns \result \from x;*/
int f3(int x){
    return x + 1;
}

/*@ relational \forall int x1,x2; x1 < x2 ==> \callpure(f4,x1) < \callpure(f4,x2);
  @ assigns \result \from x;
*/
int f4(int x){
    return f3(x);
}

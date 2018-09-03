/* run.config
   OPT: -rpp
*/

/*@ requires x > 0;
  @ relational \forall int x1; \callpure(f1,x1) > 0;
  @ assigns \result \from x;*/
int f1(int x){
	return x + 1;
}

/*@ requires y > 0;
  @ assigns \result \from y;*/
int f2(int y){
  return 2+y;
}

/*@ relational \forall int x1; \callpure(f1,x1) < \callpure(f2,x1) < \callpure(2,g,x1);
  @ assigns \result \from x;
*/
int g(int x){
  return f1(x)+f2(x)+f1(x);
}

/*@ assigns \result \from x;*/
int k1(int x){
 int temp = 0;
 
 not_good:if(x > 0){
    goto good;
  }
  else{
    temp = temp +1;
    goto not_good;
  }
 good:return temp;
}

/*@ assigns \result \from \nothing;
  @ relational \callpure(2,l) == \callpure(2,l);
*/
int l(){
  return k1(10)+k1(10);
}


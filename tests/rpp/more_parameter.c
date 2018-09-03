/* run.config
   OPT: -rpp
*/

struct s {
  int s1;
  int s2;
};

int i[10];

/*@ assigns \result \from x;
  @ relational \forall struct s var; \callpure(f,var.s1) == \callpure(f, var.s1);
*/
int f(int x){
  return x;
}

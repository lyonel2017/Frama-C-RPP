/* run.config
   OPT: -rpp
*/

struct matrix {
	int m[100];
};
/*@ predicate is_eq(struct matrix q, struct matrix p, integer l) = \forall integer i; 0 <= i < l && l < 100 ==> q.m[i] == p.m[i];*/
/*@ predicate is_eq_test(struct matrix q, struct matrix p, integer l) =  0 <= l < 100 ==> q.m[l] == p.m[l];*/
/*@ predicate is_trans(struct matrix q, struct matrix p, integer l) = \forall int k,g; 0 <= k < l && 0 <= g < l && l < 100 ==> q.m[g*l + k] == p.m[k*l+g];*/

/* lemma help: \forall struct matrix m,m1,m2,int n; is_trans(m1,m,n) && is_trans(m2,m,n) && 0< n < 100 ==> is_eq(m1,m2,n);*/

/*@ assigns \result \from m;*/
struct matrix trans2(struct matrix m){	
  struct matrix m_t;
  m_t.m[0] = m.m[0];
  m_t.m[1] = m.m[2];
  m_t.m[2] = m.m[1];
  m_t.m[3] = m.m[3];
  /*@ assert is_trans(m_t,m,2);*/
  return m_t;
}

/*@ assigns \result \from m;
  @ relational \forall struct matrix m; is_eq(\callpure(trans2,m), \callpure(trans,m),4); 
*/
struct matrix trans( struct matrix m){
	int i = 0;
	int j = 0;
	struct matrix m_t;
	/*@ loop assigns i,j;
	  @ loop assigns m_t;
	  @ loop invariant 0 <= i <= 2; 
	  @ loop invariant 0 <= j <= 2;    
	  @ loop invariant \forall int k; 0 <= k < 2 && i>0 ==> m_t.m[(i-1)*2+k] == m.m[k*2+(i-1)];
	  @ loop invariant \forall int k,g; 0 <= k < 2 && 0 <= g < i ==> m_t.m[g*2 + k] == m.m[k*2+g];
          @ loop variant 2 - i;
	*/
	for(i = 0; i < 2; i++){
	  /*@ loop assigns j;
	    @ loop assigns m_t;
	    @ loop invariant 0 <= j <= 2;
	    @ loop invariant 0 <= i < 2;
	    @ loop invariant \forall int k,g; 0 <= k < 2 && 0 <= g < i ==> m_t.m[g*2 + k] == m.m[k*2+g];
	    @ loop invariant \forall int k; 0 <= k < j  ==> m_t.m[i*2+k] == m.m[k*2+i];
	    @ loop variant 2 - j;
	  */
	  for(j = 0; j < 2; j++){
	       m_t.m[i*2+j] = m.m[j*2+i];
	  }
	}
	/*@ assert is_trans(m_t,m,2);*/
	return m_t;
}

/*@ assigns \result \from m_a,m_b;
  @ relational \forall struct matrix m1, m2; is_eq(\callpure(trans2,\callpure(sum,m1,m2)),\callpure(sum,\callpure(trans2,m1),\callpure(trans2,m2)),4);
  @ relational \forall struct matrix m1, m2; is_eq(\callpure(trans,\callpure(sum,m1,m2)),\callpure(sum,\callpure(trans,m1),\callpure(trans,m2)),4);
  @ relational \forall struct matrix m1, m2; is_eq_test(\callpure(trans,\callpure(sum,m1,m2)), \callpure(sum,\callpure(trans,m1),\callpure(trans,m2)),0);
  @ relational \forall struct matrix m1, m2; is_eq_test(\callpure(trans,\callpure(sum,m1,m2)), \callpure(sum,\callpure(trans,m1),\callpure(trans,m2)),1);
  @ relational \forall struct matrix m1, m2; is_eq_test(\callpure(trans,\callpure(sum,m1,m2)), \callpure(sum,\callpure(trans,m1),\callpure(trans,m2)),2);
  @ relational \forall struct matrix m1, m2; is_eq_test(\callpure(trans,\callpure(sum,m1,m2)), \callpure(sum,\callpure(trans,m1),\callpure(trans,m2)),3);
*/
struct matrix sum(struct matrix m_a,struct matrix m_b){
  struct matrix m_s;
  int i = 0;

  /*@ loop assigns m_s,i;
    @ loop invariant 0 <= i <= 4; 
    @ loop invariant \forall int k; 0 <= k < i ==> m_s.m[k] == m_a.m[k] + m_b.m[k];
  */
  for(i = 0; i < 4; i++){
    m_s.m[i] = m_a.m[i] + m_b.m[i];
  }
  return m_s;
}


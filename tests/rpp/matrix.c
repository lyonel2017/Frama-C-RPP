/* run.config
   OPT: -rpp
*/

typedef struct matrix2{
	int t[4];
};

/*@ assigns \result \from m_t;*/
struct matrix2 trans(struct matrix2 m_t){
        struct matrix2 m_t_2;
	
	m_t_2.t[0] = m_t.t[0];
	m_t_2.t[1] = m_t.t[2];
	m_t_2.t[2] = m_t.t[1];
	m_t_2.t[3] = m_t.t[3];

	return m_t_2;
}



/*@ relational \forall struct  matrix2 m; \callpure(det_two,m) == \callpure(det_two,\callpure(trans,m));
  @ assigns \result \from m_d;*/
int det_two(struct matrix2 m_d){
	return m_d.t[0]*m_d.t[3] - m_d.t[1]*m_d.t[2];
}

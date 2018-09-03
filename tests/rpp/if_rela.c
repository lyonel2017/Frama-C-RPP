/* run.config
   OPT: -rpp
*/

/*@ relational \forall int a,b,c; \callpure(Med,a,b,c) == \callpure(Med,a,c,b);
  @ relational \forall int a,b,c; \callpure(Med,a,b,c) == \callpure(Med,b,a,c);
  @ assigns \result \from u,v,w;
  @ behavior id1:
  @  assumes v<w && u<v;
  @  assigns \result \from u,v,w;
  @  ensures \result == v;
  @ behavior id2:
  @  assumes v<w && u<w && u>v;
  @  assigns \result \from u,v,w;
  @  ensures \result == u;
  @ behavior id3:
  @  assumes v>w && u>v;
  @  assigns \result \from u,v,w;
  @  ensures \result == v;
  @ behavior id4:
  @  assumes v>w && u<v && u>w;
  @  assigns \result \from u,v,w;
  @  ensures \result == u;
*/
int Med(int u, int v, int w){
  int med;
  med = w;
  if(v<w)
    if(u<v)
      med=v;
    else {
      if(u<w)
	med=u;}
  else 
    if(u>v)
      med=v;
  else{
      if(u>w)
	med=u;}
  return med;
}

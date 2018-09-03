/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/19325256/java-lang-illegalargumentexception-comparison-method-violates-its-general-contr
 *
 */

struct Node{
  int ID;
};

/*@ requires 0 <= id < 1000;
  @ assigns \result \from id,t[0..1000];
  @ ensures t[id] != -1 ==> \result == 1;
  @ ensures t[id] == -1 ==> \result == 0;*/
int containsKey(int id,int *t);

/*@ requires 0 <= id < 1000;
  @ assigns \result \from id,t[0..1000];
  @ ensures \result == t[id];*/
int get(int id, int *t);

/*@ assigns \result \from o1;
  @ ensures \result == o1.ID;
  @ ensures 0 <= \result < 1000;*/
int getID(struct Node o1);

/*@ requires \valid(Map+(0..1000));
  @ assigns \result \from o1,o2,Map[0..100];
  @ relational \forall struct Node x1,x2, int *Map; \callpure(compare,x1,x2,Map) == -(\callpure(compare,x2,x1,Map));
  @ relational \forall struct Node x1,x2,x3, int *Map; (\callpure(compare,x1,x2,Map) > 0 && \callpure(compare,x2,x3,Map) > 0) ==> \callpure(compare,x1,x3,Map) > 0;
  @ relational \forall struct Node x1,x2,x3, int *Map; \callpure(compare,x1,x2,Map) == 0 ==> (\callpure(compare,x1,x3,Map) == \callpure(compare,x2,x3,Map));
*/
int compare(struct Node o1, struct Node o2, int *Map){
  if(containsKey(getID(o1),Map) && containsKey(getID(o2),Map)){
    int order1 = get(getID(o1),Map);
    int order2 = get(getID(o2),Map);

    if(order1 < order2)
      return -1;
    else if(order1 > order2)
      return 1;
    else
      return 0;
  }
  return get(getID(o1),Map) - get(getID(o2),Map);
}

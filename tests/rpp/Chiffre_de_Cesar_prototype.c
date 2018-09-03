/* run.config
   OPT: -rpp
*/

struct tableau {
	int s[100];
};

/*@ predicate is_eq(struct tableau q, struct tableau p, int l) = \forall integer i; 0 <= i < l && l < 100 ==> q.s[i] == p.s[i];
  @ predicate is_good(struct tableau q,int l) = \forall integer k; 0 <= k < l && l < 100  ==> 0 <= q.s[k] <= 126;
*/

/*@ requires 1 <= length <= 100;
  @ requires 0 < PubKey < 127; 
  @ requires is_good(Message,length);
  @ assigns \result \from Message,length,PubKey;
 */
struct tableau Cryptage(struct tableau Message, int length, int PubKey);

/*@ requires 1 <= length <= 100;
  @ requires 0 < PubKey < 127; 
  @ requires is_good(Message,length);
  @ assigns \result \from Message,length,PubKey;
  @ relational \forall struct tableau message,int key,length; is_good(\callpure(Cryptage,message,length,key),length);
  @ relational \forall struct tableau message ,message_beta1,message_beta2,int key,length; 
  is_eq(message_beta2,message_beta1,length)  ==> 
  (message_beta1 == \callpure(Cryptage,message,length,key) ==> 
  is_eq(\callpure(Decryptage,message_beta2,length,key),message,length));
 */
struct tableau Decryptage(struct tableau Message, int length, int PubKey);

/*@ ensures is_eq(\result,message,len);
  @ assigns \nothing;
*/
struct tableau do_something_with_message(struct tableau message, int len);

/*@ requires 1 <= len <= 100;
  @ requires is_good(message,len);
  @ ensures is_eq(\result,message,len);*/
struct tableau f(struct tableau message, int len) {
	int key = 120;
	struct tableau ret;

	ret = Cryptage(message,len,key);
	ret = do_something_with_message(ret,len);
	ret = Decryptage(ret,len,key);
	return ret;
}

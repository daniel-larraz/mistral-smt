/*
 * UniversalInstantiator.h
 *
 *  Created on: Sep 12, 2008
 *      Author: tdillig
 */

#ifndef UNIVERSALINSTANTIATOR_H_
#define UNIVERSALINSTANTIATOR_H_
#include <map>
#include <set>
using namespace std;

class CNode;
class Connective;
class EqLeaf;
class ILPLeaf;
class VarMap;
class Term;
class SubstitutionExpression;
class QuantifiedLeaf;

/*
 * Struct used to reperesent a quantified variable.
 * The orig_id is the unique id associated with the whole
 * quantifier leaf to differentiate between variables that
 * appear in different quantified clauses.
 */
struct qvar{
	long int id;
	int var_id;
	bool operator<(const qvar & other) const
	{
		if(id!=other.id)
			return id < other.id;
		return var_id<other.var_id;
	}
};
// --------------------------------------

class UniversalInstantiator {
private:
	bool *success;
	/*
	 * Used for numbering renamed existentially quantified variables.
	 */
	int cur_varindex;

	/*
	 * A mapping from a universally quantified variable
	 * to the function id and argument number in which it appears.
	 * For instance, Ai. ( ...f(a,i, b)), we would have
	 * a mapping from i to (f's id, arg# 1).
	 * Note: A universally quantified variable
	 * is not allowed to appear as different arguments
	 * inside a given function.
	 */
	map<qvar, map<int, int>* > fun_arg_universal;
	map<pair<int, int>,set<qvar>* > reverse_fun_arg_universal;

	/*
	 * A mapping from universally quantified variables
	 * to a set of SubstitutionExpression's it needs
	 * to be instantiated with.
	 */
	map<qvar, set<Term*>* > index_set;

	/*
	 * A mapping from SubstituionExpression's to what variables
	 * they need to be instantiated with. If a subsitution expression
	 * is a just a variable or constant, the int will be either
	 * the constant or variable id associated with the constant or variable.
	 * For complex expressions, this will be the var id for
	 * some fresh temporary.
	 */
	map<Term*, int> sub_exp_to_var_id;

	/*
	 * The resulting node after instantiating universals.
	 */
	CNode* new_conn;



public:
	/*
	 * In the constructor, success can be used to indicate a parse
	 * error in the index guard.
	 */
	UniversalInstantiator(CNode* node, bool * success = NULL);

	/*
	 * Returns the resulting constraint after instantiating the quantified
	 * variables. The return value must be deleted by whoever calls this method.
	 */
	CNode* get_constraint();
	virtual ~UniversalInstantiator();
private:
	CNode* process_clause(CNode* c);
	bool contains_quantifier(CNode* c);
	bool preprocess_constraint(CNode* c);
	CNode* rec_preprocess_constraint(CNode* c, bool phase,
			map<int,int> & var_subs, QuantifiedLeaf* ql);
	CNode* process_eq_leaf(EqLeaf* l, map<int,int> & var_subs,
			QuantifiedLeaf* ql);
	CNode* process_ilp_leaf(ILPLeaf*l, map<int,int> & var_subs,
			QuantifiedLeaf* ql);
	Term* process_term(Term* t, map<int,int> & var_subs, int fun_id,
			int arg_num, QuantifiedLeaf* ql);
	bool build_index_set(CNode* clause, set<int> &qvars);
	bool build_index_set_index_guard(CNode* c, set<int> &qvars,
			QuantifiedLeaf *ql);
	bool build_index_set_term(Term* t, set<int> &qvars, int fun_id, int arg_num);
	void delete_fun_arg_universal();
	void error();
	void add_to_index_set(qvar qv, Term* t);
	bool process_eq_leaf_in_index_guard(EqLeaf* eq, set<int> &qvars,
			QuantifiedLeaf* ql);
	bool process_ilp_leaf_in_index_guard(ILPLeaf* ilp, set<int> &qvars,
				QuantifiedLeaf* ql);
	void get_equivalence_class(qvar qv, set<qvar>& eq_class);
	CNode* instantiate_universals(CNode *c,
			map<int, Term*> & sub_map);
	Term* instantiate_term(Term* t,
			map<int, Term*> &sub_map);


};

#endif /* UNIVERSALINSTANTIATOR_H_ */

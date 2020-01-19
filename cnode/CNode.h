/*
 * CNode.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef CNODE_H_
#define CNODE_H_
#include <string>
using namespace std;
#include <map>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <set>
using namespace std;

#include "SatValue.h"

#include <boost/serialization/list.hpp>
#include <boost/serialization/string.hpp>
#include <boost/serialization/version.hpp>
#include <boost/serialization/split_member.hpp>
#include <boost/serialization/shared_ptr.hpp>
#include <boost/serialization/base_object.hpp>
#include <boost/serialization/export.hpp>


enum cnode_type
{
	FALSE_NODE,
	TRUE_NODE,
	BOOLEAN_VAR,
	EQ,
	ILP,
	MOD,
	UNIVERSAL,
	NOT,
	AND,
	OR,
	IMPLIES
};

class VarMap;
class Term;
class Leaf;

/*
 * A CNode is either a connective (and, or, not, implies) or a leaf node
 * (EqLeaf, ILPLeaf, ModLeaf, QuantifiedLeaf.)
 *
 * Among the connective nodes, all implications x->y
 * are first converted to !x | y during the preprocessing stage;
 * hence we assume all connectives are and, or, or not.
 *
 * All nodes are shared and created by calling their factory method make.
 *
 */


class CNode;

namespace std {
template <>
struct hash<CNode*> {
        size_t operator() (const CNode* const & x) const;
};

template <>
struct hash<pair<int, CNode*> > {
        size_t operator() (const pair<int, CNode*>  & x) const;
};

}



/*
 * Simplification level for cnodes:
 * UNSAT_SIMPLIFY: Only guarantees constraints that are unsat are false,
 * 				   nothing else.
 * LAZY_SIMPLIFY: Only simplifies part of the constraint necessary to prove
 * 					the constraint SAT.
 * FULL_SIMPLIFY: Simplifies all parts of the constraint, not just the part
 * 				  necessary to prove it SAT.
 * SEMANTIC SIMPLIFY: Doesn't just simplify the constraint locally, but does a
 * 					global simplification.
 *
 */
enum simplification_level {
	UNSAT_SIMPLIFY,
	BOOLEAN_SIMPLIFY,
	HYBRID_SIMPLIFY,
	THEORY_SIMPLIFY,
	/*-----------*/
	_END_SIMPLIFY_
};

struct node_eq
{
  bool operator()(const CNode* l1, const CNode* l2) const;
};



class CNode;

class CNode {
	friend class Term;
	friend class boost::serialization::access;
public:
	static VarMap vm;
	static unordered_set<CNode*, std::hash<CNode*>, node_eq> nodes;
	static bool delete_nodes;

	static unordered_map<pair<int,CNode*>, CNode*> simp_map;
	size_t hash_c;
	cnode_type node_type;

private:

	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & node_type;
		ar & negations_folded;

	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		CNode* cur_folded;
		ar & node_type;
		ar & cur_folded;
		negations_folded = cur_folded;
		negation = NULL;
		factorization = NULL;

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()

	struct refactor_lessthan
	{
		  inline bool operator()(const pair<CNode*, set<CNode*> >& ref1,
				  const pair<CNode*, set<CNode*> >& ref2) const;
	};

public:
	/*
	 * The canonical node to be used when interpreting the CNode as
	 * part of a clause. This is may only be different for negations of
	 * ILP_LEQ leafes.
	 */
	CNode* negations_folded;

	CNode* negation;

	CNode* factorization;


protected:
	CNode();
	virtual ~CNode();
	static CNode* get_node(CNode* node);
	static set<CNode*> to_delete;
	static CNode* uniquify_cnode_rec(CNode* node);
public:
	static CNode* uniquify_cnode(CNode* node);
	static VarMap& get_varmap();
	static CNode* true_node();
	static CNode* false_node();
	CNode* get_simplification(simplification_level min_level);
	void set_simplification(CNode* simplified_node, simplification_level level);



	/*
	 * Refactors this constraint in a locally optimal way.
	 */
	CNode* refactor();

	/*
	 * Making canonical means reconstructing this CNode with ILP leaves
	 * having the invariant that their first element always has
	 * positive coefficient.
	 */
	CNode* make_canonical();
	bool check_canonical();

	/*
	 * Return the conjunction of the constraint
	 * representing restrictions on terms that appear in
	 * this formula.
	 */
	CNode* get_attribute_constraints();


	virtual CNode* substitute(map<Term*, Term*>& subs) = 0;
	CNode* substitute(Term* (*sub_func)(Term* t));
	CNode* substitute(Term* t1, Term* t2);

	CNode* substitute(Term* (*sub_func)(Term* t, void* data), void* my_data);


	CNode* substitute(map<CNode*, CNode*> & subs);
	inline cnode_type get_type() const
	{
		return node_type;
	}
	virtual bool operator==(const CNode& other) = 0;
	virtual string to_string()=0;
	string to_prefix_notation();

	/*
	 * A leaf is either True, False,
	 * EqLeaf, ILPLeaf, or a universally quantified leaf.
	 */
	bool is_leaf() const;

	/*
	 * A literal is either a leaf or the negation of a leaf.
	 */
	bool is_literal() const;

	/*
	 * And, or, not.
	 */
	bool is_connective() const;

	/*
	 * If a node is a conjunct, it contains no or's.
	 */
	bool is_conjunct() const;

	/*
	 * If a node is a disjunct, it does not contain and's.
	 */
	bool is_disjunct() const;

	/*
	 * Does this node contain a (universal) quantifier?
	 */
	bool has_quantifier() const;

	/*
	 * Does this constraint contain <, <=, >, >=?
	 */
	bool contains_inequality();

	/*
	 * True or false.
	 */
	bool is_constant() const;
	size_t hash_code();
	static void clear();
	void get_vars(set<string>& vars);
	void get_vars(set<int>& vars);
	void get_vars(set<Term*>& vars);
	bool contains_var(int var_id);
	bool contains_term(Term* t);
	bool contains_term(set<Term*>& terms);
	CNode* rename_variable(int old_var_id, int new_var_id);
	CNode* rename_variables(map<int, int>& replacements);

	void get_nested_terms(set<Term*> & terms, bool include_function_subterms,
			bool include_constants = true);

	/*
	 * Returns another CNode that explicitly includes attributes on the
	 * terms nested in this CNode. One can specify that only attributes on certain
	 * terms be added by passing in a valid set of "which_terms".
	 */
	CNode* add_attributes(set<Term*>* which_terms = NULL);

	/*
	 * If this node entails an equality constraint on the given term t, returns
	 * another term t' such that t=t'; otherwise NULL.
	 */
	Term* contains_term_equality(Term* t);

	/*
	 * Set of all equalities involving t.
	 */
	void collect_term_equalities(Term* t, set<Term*>& eqs);

	/*
	 * If a given leaf contains the term t, this function replaces that leaf
	 * with the provided replacement node.
	 */
	CNode* replace_leaves_containing_term(Term* t, CNode* replacement);

	CNode* replace(CNode* orig, CNode* replacement);

	/*
	 * Returns the number of leaves that contain the given term
	 */
	int num_leaves_containing_term(Term* t);

	void get_all_literals(set<CNode*> & literals);
	void get_all_leaves(set<CNode*>& leaves);
	void get_literals_containing_term(Term* t, set<CNode*>& leaves);

	inline CNode* fold_negated_ilps()
	{
		return negations_folded;
	}

	int get_size();

	CNode* evaluate_assignment(map<Term*, SatValue>& assignment);
	CNode* evaluate_assignment(map<CNode*, bool>& assignments);


	void get_all_fun_ids(set<int> & ids);


	void get_all_arguments(int fun_id, int arg_num, set<Term*> & args);

	CNode* replace_first_argument(map<int, Term*>& fun_id_to_replacement);
	void get_all_first_arguments(set<int>& fn_ids, map<int, set<Term*> >&
			fn_id_to_first_arg);

	/*
	 * Fills a set with all terms appearing in ilp leaves
	 */
	void get_all_ilp_terms(set<Term*>& ilp_terms);
	/*
	 * Rewrites a disequality t1 != t2 as t1<t2 or t1>t2
	 * if at least one terms is an ilp term.
	 */
	CNode* rewrite_ilp_neqs(set<Term*>& ilp_terms);


	/*
	 * Integer division on elements in ILP leaf
	 */
	virtual CNode*  divide(long int c, Term* t);

	/*
	 * Converts this formula to an equivalence-preserving CNF
	 * (does not introduce new variables!!)
	 */
	CNode* to_cnf();

	/*
	 * Returns the number of disjuncts in CNode
	 */
	int num_disjuncts();


private:
	void to_prefix_notation_rec(string& output);
	Term* contains_term_equality_internal(Term* t, bool phase);
	void collect_term_equalities_internal(Term* t, bool phase, set<Term*> &
			equalities);
	void get_attributes(set<CNode*>& attributes);

	template<cnode_type node_type, cnode_type refactor_type>
	static CNode* connective_refactor(const set<CNode*>& children);
};

class CompareCNode:public binary_function<CNode*, CNode*, bool> {

public:
	bool operator()(const CNode* b1, const CNode* b2) const;
};






#endif /* CNODE_H_ */

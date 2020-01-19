/*
 * ConstraintSolver.h
 *
 *  Created on: Sep 16, 2008
 *      Author: tdillig
 */

#ifndef CONSTRAINTSOLVER_H_
#define CONSTRAINTSOLVER_H_


#include "CNode.h"
#include <map>
#include <set>
#include <vector>


enum atom_op_type
{
	ATOM_EQ,
	ATOM_NEQ,
	ATOM_LEQ,
	ATOM_LT,
	ATOM_GT,
	ATOM_GEQ,
	ATOM_MOD
};

using namespace std;

typedef pair<CNode*, CNode*> constraint_type;
typedef int c_id;

class VariableTerm;


using namespace __gnu_cxx;

struct cnode_eq
{
  bool operator()(const CNode *const l1, const CNode*const l2) const
  {
    return *(CNode*)l1==*(CNode*)l2;
  }
};

struct fun_bg
{
	CNode* key;
	Term* quantified_var;
	CNode* nc_val;
	CNode* sc_val;
};

class AccessPath;
class IndexVarManager;
class Constraint;
class FunctionTerm;


class ConstraintSolver {
	friend class Constraint;
	friend class Term;
private:
	map<c_id, constraint_type> constraints;
	map<constraint_type, c_id > reverse_constraints;
	int id_count;


	bool bg_false;

	/*
	 * General background constraint, such as the constraint under which
	 * this function continues executing or the constraint under which
	 * loop terminates and so on.
	 */
	CNode *general_background;

	/*
	 * A mapping from literals L introduced as placeholders
	 * for imprecise constraints to an (NC, SC) pair
	 * such that L => NC and SC => L
	 * L is either of the form d=c, d>=c, or d(i)=c,
	 * and d(i)>c. If L constaints a function term d,
	 * then the meaning of this background constraint
	 * is really a universally quantified axiom, i.e.,
	 * Ai. SC(i) => L(i) => NC(i).
	 */
	map<CNode*, pair<CNode*, CNode*> > background;

	/*
	 * A mapping from from function terms to their
	 * universally quantified arguments.
	 */
	map<int, Term*> fn_to_qvars;
	set<int> fn_ids;


	map<CNode*, CNode*> nc_reps;
	map<CNode*, CNode*> sc_reps;

	/*
	 * The set of keys in the background_map
	 */
	set<CNode*> bg_keys;


	vector<pair<int, string> > hardest;

	vector<pair<int, string> > hardest_eliminate_overapproximate;

	vector<pair<int, string> > hardest_eliminate_underapproximate;

	bool bg_enabled;




public:
	ConstraintSolver();
	virtual ~ConstraintSolver();
	void clear();
	void clear_local_data();
	void clear_stats();

	int num_sat_queries;
	int num_bg_queries;
	int solve_time;

	int eq_time;
	int num_eqs;

	int bg_simp_time;


	int num_eliminate_over_queries;
	int num_eliminate_under_queries;
	int eliminate_over_time;
	int eliminate_under_time;



	string stats_to_string();


private:
	c_id get_true_constraint();
	c_id get_false_constraint();
	c_id get_atom(Term* t1, Term* t2, atom_op_type op);
	c_id get_constraint_from_cnode(CNode* n);
	c_id get_constraint_from_string(string & s);

	c_id nc(c_id id);
	c_id sc(c_id id);
	CNode* get_nc(c_id& id);
	CNode* get_sc(c_id& id);

	bool is_sat(c_id & id);
	bool is_sat_discard(c_id & id);

	inline CNode* is_sat(CNode* node,
			simplification_level level, bool use_nc,
			void* assignments = NULL);

	inline CNode* is_sat(CNode* node, CNode* assumption,
			simplification_level level, bool use_nc,
			void* assignments = NULL);

	bool is_valid(c_id id);
	bool is_valid_discard(c_id id);
	inline CNode* is_valid(CNode* node, simplification_level level);
	bool implies(c_id c1, c_id c2);

	c_id and_constraint(c_id id1, c_id id2);
	c_id or_constraint(c_id id1, c_id id2);
	c_id not_constraint(c_id id);
	c_id make_ncsc(c_id nc, c_id sc);

	void clear_bg();

	string constraint_to_string(c_id id);

	/*
	 * is nc1==nc2 && sc1 == sc2 ?
	 */
	bool is_equal(c_id id1, c_id id2);

	/*
	 * does c1=>c2 && c2 >= c1 ?
	 */
	bool is_equivalent(c_id id1, c_id id2);
	bool is_precise(c_id id) const;

	bool implies(CNode* n1, CNode* n2);

	c_id get_id(constraint_type& c);


	void get_free_vars(c_id id, set<Term*>& vars);

	void get_terms(c_id id, set<Term*>& terms, bool include_nested_terms);



	/*
	 * Functions for eliminating existentially quantified variables.
	 */
	c_id eliminate_evar(c_id id, VariableTerm* var);
	c_id eliminate_evars(c_id id, set<VariableTerm*>& vars);

	/*
	 * Functions for eliminating universally quantified variables.
	 */
	c_id eliminate_uvar(c_id id, VariableTerm* var);
	c_id eliminate_uvars(c_id id, set<VariableTerm*>& vars);

	c_id divide(c_id id, long int c, Term* t);


	/*
	 * Functions for eliminating free variables
	 */
	c_id eliminate_free_var(c_id id, VariableTerm* var);
	c_id eliminate_free_vars(c_id id, set<VariableTerm*>& vars);
	CNode* eliminate_free_var_nc(CNode* nc, VariableTerm* v);
	CNode* eliminate_free_var_sc(CNode* sc, VariableTerm* v);


	bool get_assignment(c_id it, set<pair<string, string> > & assignments);

	bool get_assignment(c_id it, map<Term*, SatValue> & assignments);


	bool contains_inequality(c_id id);




	Term* find_equality(c_id id, Term* t);

	void find_equalities(c_id id, Term* t, set<Term*> & eqs);

	c_id replace_constraint(c_id old_id, c_id to_replace, c_id replacement);


	/*
	 * Determines if t1 and t2 have a linear equality relation.
	 */
	bool has_equality_relation(c_id id, Term* t1, Term* t2);


	void get_disjunctive_equalities(c_id id, Term* var,
			map<Term*, Constraint> & equalities);


	c_id replace_term(c_id old_id, Term* to_replace, Term*
			replacement);
	c_id replace_terms(c_id old_id, map<Term*, Term*>& replacements);

	c_id replace_terms(c_id old_id, Term* (*sub_func)(Term* t, void* data),
			void* my_data)
	{
		constraint_type ct = constraints[old_id];
		CNode* nc= ct.first;
		CNode* sc = ct.second;
		CNode* new_nc = nc->substitute(sub_func, my_data);
		if(nc == sc) {
			if(nc == new_nc) return old_id;
			constraint_type ct(new_nc, new_nc);
			return get_id(ct);
		}

		CNode* new_sc = sc->substitute(sub_func, my_data);
		ct = constraint_type(new_nc, new_sc);
		return get_id(ct);
	}

	bool contains_term(c_id id, Term* t);
	bool contains_term(c_id id, set<Term*>& terms);

	c_id replace_constraints(c_id old_id, map<Constraint, Constraint>& replacements);

	//c_id increment_index(c_id old_id, AccessPath* base, AccessPath* delta);



	/*
	 * key_id => value_id
	 * Note that if key_id contains a function term f(i), then this is
	 * a univerally quantified axiom of the form Ai. key(i) => value_id(i)
	 * If a formula contains any instantiation of key(i), we need to
	 * conjoin all relevant instantiations of value(i).
	 */
	void add_axiom(c_id key_id, c_id value_id, bool check_function_term);


	void replace_term_in_axioms(Term* old_t, Term* new_t);

	/*
	 * For any SAT query, the constraint identified
	 * by id should be taken into account.
	 */
	void set_background_knowledge(c_id id);




	CNode* eliminate_var(CNode* n, VariableTerm* var,
			simplification_level level, bool over);

	CNode* eliminate_var(CNode* n, vector<VariableTerm*> & vars,
			simplification_level level, bool over);

	void add_to_hardest(vector<pair<int, string> > & hardest, int time,
			const string& cur);

	string get_hardest(vector<pair<int, string> > & hardest);

	c_id assume(c_id id, c_id other);

	string bg_to_string();
	c_id get_general_background();

	int nc_size(c_id id);
	int sc_size(c_id id);

	c_id propagate_background(c_id id);

	/*
	 * If background is disabled, sat and validity queries do not
	 * take background axioms into account.
	 */
	void disable_background();

	int msa(set<VariableTerm*> & msa, c_id id, map<VariableTerm*, int>& costs);
	int msa(set<VariableTerm*> & msa, c_id id, set<c_id>& bg,
			map<VariableTerm*, int>& costs);

	pair<CNode*, CNode*> get_cnodes(c_id id);

private:

	bool is_mod_term(Term* t);

	// Valid mod term for us means its second operand is a constant
	bool is_valid_mod_term(Term* t);

	/*
	 * If some  literal such as d=1 implies a formula containing
	 * a key in the bg_keys set, then this function also adds
	 * additional dependencies. For example, if d=1 -> d2=2 & flag and
	 *  d2=2 -> x=5, then include_background_dependencies(d2=2 & flag)
	 *  yields d2=2 & flag & d2=2->x=5.
	 */
	CNode* include_background_dependencies(CNode* bg_value, bool use_nc = true);

	/*
	 * Like the one above, but only returns the dependencies without
	 * including the node.
	 */
	CNode* get_background_dependencies(CNode* node, bool use_nc = true);

	void get_relevant_axioms(CNode* constraint, set<CNode*>& relevant_axioms);

	/*
	 * Adds the axioms sc => key => nc to the background.
	 */
	void add_background(CNode* key, CNode* nc, CNode* sc);

	/*
	 * Updates the nc_reps and sc_reps maps which store
	 * nc and sc without their dependencies expanded.
	 */
	void add_to_rep_map(CNode* key, CNode* nc, CNode* sc);

	CNode* simplify(CNode* c);

	/*
	 * Given a map from d(i) to its NC(i) or SC(i), returns (by reference)
	 * another map that contains the relevant instantiations of this map
	 * according to terms used in c.
	 */
	void instantiate_axioms(CNode* c, map<CNode*, CNode*>& axioms,
			map<CNode*, CNode*> & instantiated_axioms);


	c_id get_new_id(c_id old_id);


	void to_dnf(c_id c, set<c_id> & dnf);








};

#endif /* CONSTRAINTSOLVER_H_ */

/*
 * VariableEliminator.h
 *
 *  Created on: Feb 8, 2009
 *      Author: tdillig
 */

#ifndef VARIABLEELIMINATOR_H_
#define VARIABLEELIMINATOR_H_

#include <vector>
#include <set>
#include <map>
#include "Solver.h"
using namespace std;
class CNode;
class Term;
class FunctionTerm;
class Clause;
class VariableTerm;
class EqLeaf;
class ModLeaf;

/*
 * Eliminates existentially quantified variables.
 */
class VariableEliminator:public Solver {
private:

	int fresh_var_counter;
	bool over_approximate;
	bool track_new_inequalities;

	/*
	 * Is it (potentially) necessary to simplify the constraint
	 * after we eliminated a variable?
	 */
	bool simplify;

	bool large_lcm;

	CNode* orig_c;

	/*
	 * A mapping from the var id to be eliminated to the set of pairs
	 * that this var is "sandwiched" between when applying Cooper's method.
	 * This is used by the EqualityFinder to find inferred
	 * equalities in the ILP domain.
	 */
	map<VariableTerm*, set<pair<Term*, Term*> > > new_inequality_terms;

public:
	VariableEliminator(CNode *n, vector<VariableTerm*> & to_eliminate,
			simplification_level level,
			bool over_approximate, bool track_new_inequalities = false);
	VariableEliminator(CNode *n, VariableTerm* to_eliminate,
			simplification_level level,
			bool over_approximate, bool track_new_inequalities = false);


	const map<VariableTerm*, set<pair<Term*, Term*> > > & get_new_inequalities();

	virtual ~VariableEliminator();
private:
	CNode* eliminate_var(CNode* node, VariableTerm* var);
	CNode* eliminate_var_rec(CNode* node, VariableTerm* var, CNode* active_constraint);
	CNode* eliminate_var_conjunct(CNode* node, VariableTerm* var);
	void get_direct_parents(Term* t, set<FunctionTerm*>& parents,
	 		map<Term*, set<Term*> >& eq_members);

	/*
	 * Used for existential variable elimination. If x is a term to be
	 * eliminated and has no members in its equivalence class, replace all
	 * function terms it appears in with a fresh variable term.
	 */
	void introduce_fresh_vars_for_function_terms(Clause& cl,
		VariableTerm* elim_t,
		set<FunctionTerm*>& direct_parents,
		map<VariableTerm*, FunctionTerm*>& fresh_vars_to_functions,
		map<FunctionTerm*, VariableTerm*>& functions_to_fresh_vars,
		map<int, set<FunctionTerm*> >& function_id_to_functions);

	VariableTerm* introduce_fresh_var_for_function_term(Clause& cl,
		VariableTerm* elim_term, FunctionTerm* ft,
		map<VariableTerm*, FunctionTerm*>& fresh_vars_to_functions,
		map<FunctionTerm*, VariableTerm*>& functions_to_fresh_vars,
		map<int, set<FunctionTerm*> >& function_id_to_functions);

	void replace_function_with_freshvar_in_clause(Clause& cl, FunctionTerm* ft,
			VariableTerm* fresh_var);

	CNode* replace_function_with_freshvar_in_leaf(EqLeaf* eq, FunctionTerm* ft,
			VariableTerm* fresh_var);
	void get_function_terms_in_clause(Clause& cl, map<int, set<FunctionTerm*> >&
			functions_in_clause);

	CNode* eliminate_var_from_ilp_domain(Clause& cl, VariableTerm* evar, set<CNode*>&
			mod_constraints);
	ILPLeaf* find_ilp_equality_with_evar(Clause& cl, VariableTerm* evar_id);
	Term* get_ilp_substitution(ILPLeaf* eq_ilp, Term* evar );
	void apply_ilp_substitution(Clause& cl, Term* evar, Term* sub, long int coef);
	CNode* apply_ilp_substitution(ILPLeaf* ilp, Term* evar, Term* sub,
			long int coef);
	void separate_equations_by_sign(Clause& cl, Term* evar,
			set<ILPLeaf*>& positive, set<ILPLeaf*>& negative);
	void get_neq_equations_with_evar(Clause& cl, Term* evar, set<Leaf*> & neqs);
	CNode* expand_neq_constraints(Clause& cl, set<Leaf*>& neqs);
	bool expand_neq_constraints_with_bound(Clause& cl, set<Leaf*>& neqs,
			set<ILPLeaf*>& result, Term* evar, bool lt);

	bool contains_related_var(set<Leaf*> neq, VariableTerm* evar_id);
	CNode* apply_cooper(Clause& cl, Term* evar, set<ILPLeaf*>& positive,
			set<ILPLeaf*>& negative);
	CNode* eliminate_denestings(CNode* node, map<Term*, Term*>& denestings,
			VariableTerm* evar_id, int initial_count, bool include_evar);
	CNode* eliminate_mod_temps(CNode* node, set<VariableTerm*>& to_eliminate);

	void update_denestings(map<Term*, Term*>& denestings, map<Term*, Term*>&
			substitutions);
	CNode* remove_eq_var_with_no_parents(Clause& cl, VariableTerm* evar);

	/*
	 * Checks if the evar is only contained in a single
	 * mod leaf. If this is the case, returns this mod constraint,
	 * otherwise null.
	 */
	ModLeaf* find_single_mod_constraint(Clause& cl, VariableTerm* evar);

	inline void add_new_inequality(Term* t, ILPLeaf* t1, ILPLeaf* t2);





};

#endif /* VARIABLEELIMINATOR_H_ */

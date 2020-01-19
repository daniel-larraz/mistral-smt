/*
 * ClauseSolve.h
 *
 *  Created on: Feb 8, 2009
 *      Author: tdillig
 */

#ifndef CLAUSESOLVE_H_
#define CLAUSESOLVE_H_

#include <set>
#include <vector>
#include <map>
#include <list>
using namespace std;
#include "InteractionManager.h"
#include "util.h"
#include "bignum.h"



class CNode;
class VarMap;
class NormalForm;
class Clause;
class Term;
class ILPLeaf;
class EqLeaf;
class Leaf;
class FunctionTerm;
class Matrix;
class Equation;
class Solver;
class ModLeaf;

#include "bignum.h"
#include "SatValue.h"




class ClauseSolve {
	 friend class InteractionManager;
	 friend class QueryComparator;
	 friend class VariableEliminator;
	 friend class EqualityFinder;

private:
	bool repeated_solve;

	bool sat;
	Clause* cl;
	map<Term*, SatValue>* assignments;

	map<Term*, bignum> ilp_assignments;


	/*
	 * All members in an equivalence class, indexed by the representative.
	 */
	map<Term*, set<Term*> >  eq_members;

	/*
	 * Tracks size of each equivalence class; used for
	 *  deciding which representative to pick
	 */
	map<Term*, int> eq_size;

	/*
	 * Tracks the constant in each eqv class, if any.
	 *  This is used to detect contradictions during union.
	 */
	map<Term*, int> eq_class_const;

	/*
	 * Used for propagating equalities during union
	 */
	map<Term*, set<Term*> > eq_parents;

	/*
	 * Mapping from variables to their columns in the matrix
	 */
	map<int, int>  var_to_col_map;

	/*
	 * Names of the ilp variables
	 */
	vector<string> vars;

	/*
	 * Set of id's of ILP variables
	 */
	set<int> ilp_vars;

	/*
	 * Set of variables that appear inside a function symbol.
	 */
	set<int> function_vars;

	/*
	 * Matrix representing the ilp constraints
	 */
	Matrix* m;

	/*
	 * A set of disjunctive ILP disequalities ( { {<a, b>, <c, d>}, {e,f} }
	 * means (a!=b | c!= d) & (e!=f).
	 */
	set< set< pair<Equation*, bignum> > > neq_constraints;



	/*
	 * The top level terms in the original clause (before denesting).
	 * This ivar is only initialized if assignments is non-null because
	 * it is only used for generating satisfying assignments.
	 * For us, a top level term either occurs inside an arithmetic expression or
	 * does not have parent terms.
	 */
	set<Term*> top_level_terms;

	/*
	 * This map is only filled if assignments is non-null.
	 */
	map<Term*, Term*> denestings;

	/*
	 * A set of all constants
	 */
	set<Term*> constants;



	/*
	 * An auxiliary struct to help us undo a conditional union operation.
	 * - old_rep denotes a term that was a representative, but that became
	 * a non-representative during this undo operation.
	 * - eq_members is the set of elements in old_rep's equivalence class
	 * before this union operation.
	 * - has_constant/constant denote whether this congruence class had
	 * a constant before the union operation, and if so what this constant is.
	 * NOTE: Although the maps eq_size and eq_parents are updated during
	 * a normal union operation, they are not updated during a conditional
	 * union because both are only necessary for performing multiple union
	 * operations whereas we assume conditional unions are performed once and
	 * then immediately undone.
	 *
	 */
	struct history_elem {
		Term* old_rep;
		set<Term*>* eq_members;
		bool has_constant;
		int constant;

		history_elem(Term* old_rep, set<Term*>& eq_members):old_rep(old_rep),
				eq_members(&eq_members)
		{

		}

	};

	/*
	 * This is used for undo'ing a single conditional union.
	 */
	vector< history_elem > undo_buffer;

	/*
	 * STATS
	 */
	int time_denesting;
	int time_initial_ilp;
	int time_initial_union_find;
	int time_total_ilp;
	int time_total_union_find;
	int time_preparing_queries;
	int start;
	int num_interaction_queries;



public:
	ClauseSolve(CNode* node, map<Term*, SatValue>* assignments = NULL);
	ClauseSolve(Clause* clause,  map<Term*, SatValue>* assignments = NULL);
	~ClauseSolve();
	bool is_sat();
	void print_stats();



private:
	bool solve(CNode* node);
	bool clause_sat();
	void init_congruence_classes_term(Term *t, Term* parent,
		 set<Term*> & cur_parents, set<int> & function_ids);
	void init_congruence_classes(set<int> & function_ids,
			set<Term*> & eq_terms);
	void clear_ilp_representatives(set<ILPLeaf*> & leaves);
	void clear_mod_representatives(set<ModLeaf*> & leaves);
	//bool minimize_shared_ilp_vars(set<ILPLeaf*>& ilp_leaves, bool pos,
	//		set<int>& function_terms, set<Term*> &eq_terms);
	//bool minimize_shared_mod_vars(set<ModLeaf*>& mod_leaves, bool pos);
	bool process_equalities();
	bool perform_union(Term* t1, Term* t2);
	Term* find_representative(Term* t);
	bool congruent(FunctionTerm* f1, FunctionTerm* f2);
	string terms_to_string(set<Term*>& eq_class );
	bool have_contradictory_constants(Term* rep1, Term* rep2);
	bool has_contradiction();

	/*
	 * Perform conditional union supports the ability to undo the union by
	 * keeping some scratch state around. However, only the representative
	 * fields and eq_members maps are updated while performing the union
	 * because it is assumed that the union will be undone.
	 * changed_eq_classes contains the representatives of the congruence classes
	 * changed by the union.
	 */
	bool perform_conditional_union(Term* t1, Term* t2,
			set<Term*>& changed_eq_classes, bool& used_function_axiom);
	void undo_conditional_union();

	void compute_ilp_var_ids();
	void build_var_to_col_map();
	void construct_ilp_matrix();
	void populate_matrix_row(ILPLeaf* l, bool sign);
	bool add_inequality(set<pair<Term*, Term*> > disjunctive_ineq,
			set< pair<Equation*, bignum> > & new_inequality);
	void add_inequality(ILPLeaf* ilp);
	void generate_sat_assignment(vector<bignum>* ilp_assignments);
	void add_equality(Term* t1, Term* t2);
	void print_neq_matrix();
	void add_ilp_vars_in_mod_leaf(ModLeaf* ml, bool pos, int counter);
	void convert_mod(ModLeaf* ml, bool pos, int counter);
	inline void add_ilp_to_matrix(ILPLeaf* ilp);
	inline void init_top_level_terms();
	inline void init_top_level_terms_eq(set<EqLeaf*>& eq_leaves);
	inline void init_top_level_terms_ilp(set<ILPLeaf*>& ilp_leaves);
	inline void init_top_level_terms_mod(set<ModLeaf*>& mod_leaves);
	void init_top_level_terms_term(Term* t);
	void print_congruence_classes();
	void clear();
	void get_ilp_assignment(vector<bignum>& ilp_assign);
	void init(set<VariableTerm*>& vars );

	/*
	 * Checks whether the given ilp assignments cause any contradiction
	 * in the eq domain. If they don't, we are done.
	 */
	bool check_assignment();

	void print_eq_classes();
	string eq_classes_to_string();

	void init_stats();

	//bool minimize_shared_variables(set<int> & function_terms, set<Term*> &eq_terms);


};

#endif /* CLAUSESOLVE_H_ */

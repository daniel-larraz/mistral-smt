/*
 * MSAFinder.h
 *
 *  Created on: Aug 22, 2011
 *      Author: isil
 */

#ifndef MSAFINDER_H_
#define MSAFINDER_H_
#include <set>
#include <vector>
#include <map>
#include <string>
#include <deque>
using namespace std;

class CNode;
class Term;
class VariableTerm;
class FunctionTerm;
class ConstantTerm;
#include "SatValue.h"

typedef  pair<VariableTerm*, int> var_cost_pair;

class MSAFinder {

public:
	CNode* node;
	map<VariableTerm*, int>& costs;
	int min_estimate;
	set<VariableTerm*> msa;
	map<VariableTerm*, Term*> var_to_fun_map;

	/*
	 * If <t, {S1, S2, ...}> is in this map, this means that t cannot be
	 * universally quantified if all variables in Si
	 * have been universally quantified.
	 */
	map<Term*, set<set<Term*> > > dependencies;

	int mpi_estimate;


	int fun_counter;
	int num_e_elims;
	int e_elim_time;
	int num_a_elims;
	int a_elim_time;
	int a_approximate;
	int a_approximate_time;
	int num_unsat_universal;
	int num_unsat_approx_universal;
	int dependence_time;
	int num_dep_success;
	int simplify_time;
	int mpi_time;
	int prune1_solve;
	int prune2_solve;

	int e_only;
	int a_only;
	int total;
	int cost_pruned;
	int max_cost;

	set<Term*> vars_in_min_pi; // vars in minimum prime implicant


public:
	MSAFinder(CNode* node, map<VariableTerm*, int>& costs);
	MSAFinder(CNode* c, set<CNode*>& background,
			map<VariableTerm*, int>& costs);

	const set<VariableTerm*>& get_vars_in_msa();
	int get_cost();
	string get_stats();
	string res_to_string();
	~MSAFinder();

private:

	void find_msa(CNode* c, set<CNode*>& background,
			map<VariableTerm*, int>& costs);

	int compute_msa(CNode* constraint, set<CNode*>& background,
			int cur_cost, set<VariableTerm*>& cur_msa,
			set<Term*>& cur_universal);



	int get_cheapest_cost(const vector<VariableTerm*>& vars);

	/*
	 * Result of universally quantifying v in c and performing
	 * quantifier elimination
	 */
	CNode* universally_quantify(CNode* c, VariableTerm* v);

	/*
	 * Test if Av. c is UNSAT by plugging in a few "relevant" values for v
	 * and seeing if any of them is UNSAT.
	 */
	bool quick_test_universal_unsat(CNode* c, VariableTerm* v);

	/*
	 * Result of existentially quantifying v in c and performing
	 * quantifier elimination
	 */
	CNode* existentially_quantify(CNode* c, VariableTerm* v);

	/*
	 * Sums up costs of all remaining vars
	 */
	int get_max_remaining_cost(deque<VariableTerm*>& unassigned_vars);

	/*
	 * Initialize var_to_fun_map containing a unique function term for each
	 * variable
	 */
	void init_var_to_fun_map(set<Term*> vars);

	/*
	 * Gives the currently unassigned variables in constraint
	 */
	void get_unassigned_vars(CNode* constraint, deque<VariableTerm*>& vars);


	/*
	 * Gives the cost of this variable
	 */
	int get_cost(VariableTerm* vt);


	/*
	 * Computes a conservative estimate for the cost of the minimum
	 * satisfying assignment. This is done by computing the cost of the
	 * minimum sized prime implicant of the formula.
	 */
	void compute_initial_bound(set<CNode*>& background);


	// ------------------------------

	int compute_msa_naive(CNode* constraint, set<VariableTerm*> & msa);
	void compute_subsets(set<Term*> vars,
			set<set<Term*> >& subsets);

	void get_candidate_msa(set<Term*>& vars, const set<Term*>& quantified,
			set<Term*>& candidate_msa);
	int get_cost(const set<Term*>& vars);
	CNode* universally_quantify(CNode* c, set<Term*> vars);

	void get_constants_to_check(CNode* c, vector<Term*>& constants);

	VariableTerm* pick_next_unassigned_var(CNode* c,
			deque<VariableTerm*>& unassigned_vars);

	void compute_dependencies(CNode* c);
	void compute_dependencies_rec(CNode* context, CNode* c);
	void print_dependencies();

	bool is_subset_of(const set<Term*>& s1, const set<Term*>& s2);
	bool is_subset_of(const set<VariableTerm*>& s1,
			const set<VariableTerm*>& s2);

	CNode* propagate_dependencies(CNode* c, set<VariableTerm*>& cur_msa,
			const set<Term*>& cur_universals, int& cur_cost);

	int compute_msa_using_blocking_clause(CNode* c, set<VariableTerm*>& msa);
	void compute_msa_bc(CNode* c, CNode* bc,
			int& best_cost, set<VariableTerm*>& msa);

	bool bc_conjunct_redundant(set<VariableTerm*>& v_bar, VariableTerm* vt);

	void randomize_order(map<Term*, SatValue>& assignment,
			deque<pair<Term*, SatValue> >& new_order);

	void order_assignments(map<Term*, SatValue>& assignment,
				deque<pair<Term*, SatValue> >& new_order);




};

#endif /* MSAFINDER_H_ */

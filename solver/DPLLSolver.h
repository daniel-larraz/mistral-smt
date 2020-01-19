/*
 * DPLLSolver.h
 *
 *  Created on: Jul 30, 2009
 *      Author: tdillig
 */

#ifndef DPLLSOLVER_H_
#define DPLLSOLVER_H_

#include <set>
#include <string>
#include <vector>
#include <map>
using namespace std;

#include "bignum.h"
#include "ClauseSolve.h"
#include "SkeletonSolver.h"
#include "True.h"

class CNode;
class Term;



class DPLLSolver {


private:

	enum elem_status
	{
		SAT,
		UNSAT,
		NOT_QUERIED
	};

	struct stack_elem
	{
		CNode* constraint;
		CNode* cumulative_constraint;
		set<CNode*> leaves;
		elem_status status;
		map<Term*, SatValue> assignment;

		stack_elem(CNode* node)
		{
			constraint = node;
			cumulative_constraint = node;
			constraint->get_all_leaves(leaves);
			status = NOT_QUERIED;
		}

	};



	CNode* assumptions;
	bool sat;

	int total_ticks;
	int check_prev_ticks;
	int num_sat_calls;
	int num_delta;
	int ticks_delta;
	int clause_ticks;
	int sat_clause_ticks;
	int num_clause;
	int num_sat_clauses;
	int num_sat_by_prev_assignment;
	int num_unknown_by_prev_assignment;
	map<set<CNode*>, int> sat_clauses_with_same_leaves;
	map<set<CNode*>, vector<map<CNode*, bool> > >  leaves_to_assignments;

	int num_consecutive_boolean_complete;

	vector<stack_elem> stack;

	CNode* current_assignment;

	SkeletonSolver s;

	map<Term*, SatValue>* assignments;

	set<Term*>& ilp_terms;


public:
	DPLLSolver(set<Term*>& ilp_terms, map<Term*, SatValue>* assignments = NULL);

	/*
	 * Constructor to be used if a set of theory-specific axioms are known.
	 */
	DPLLSolver(CNode* theory_tautologies, set<Term*>& ilp_terms,
			map<Term*, SatValue>* assignments = NULL);

	void push(CNode* c);
	void pop();
	CNode* get_stack();

	/*
	 * Sat assignment should respect the specified background.
	 * This function can only be called before additional constraints are
	 * pushed on the stack and it cannot be popped.
	 */
	void restrict(CNode* background);

	bool is_sat();
	CNode* get_background_assumptions();
	~DPLLSolver();
	string get_stats();
	CNode* get_current_assignment();

	inline int get_num_consecutive_boolean_complete() const
	{
		return num_consecutive_boolean_complete;
	}
	inline double boolean_complete_ratio() const
	{
		return ((double)num_sat_clauses)/((double)(num_clause));
	}
	inline double time_verifying_boolean_assignment() const
	{
		return ((double)clause_ticks)/((double)(CLOCKS_PER_SEC));
	}

	inline int num_clauses_checked_in_theory() const
	{
		return this->num_clause;
	}

	/*
	 * Substitutes the current assignment of the stack into the given constraint.
	 * This may be either a full or partial assignment for the constraint, or
	 * it may not satisfy the constraint.
	 */
	CNode* substitute_partial_assignment(CNode* constraint);


private:
	/*
	 * Initializes various ivars.
	 */
	void init();

	/*
	 * Checks if we encountered a constraint with same leaves and whether any
	 * of the previous assignments satisfies this formula
	 */
	inline bool satisfied_by_prev_assignment(CNode* formula);
	inline bool satisfied_by_prev_assignment_internal(CNode* formula);

	string stack_to_string();
};

#endif /* DPLLSOLVER_H_ */

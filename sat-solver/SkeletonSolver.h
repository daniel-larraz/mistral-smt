/*
 * SkeletonSolver.h
 *
 *  Created on: Jul 29, 2009
 *      Author: tdillig
 */

#ifndef SKELETONSOLVER_H_
#define SKELETONSOLVER_H_

#include <vector>
#include <map>
#include <set>
#include <unordered_map>
using namespace std;


#include "SatSolver.h"
#include "SolverTypes.h"
#include "Vec.h"

#define FALSE_CLAUSE ((vec<minisat::Lit>*)((0) | 1))
#define STACK_DELIMITER ((vec<minisat::Lit>*)NULL)

class CNode;

class SkeletonSolver {
	map<CNode*, minisat::Var> node_to_var_map;
	map<minisat::Var, CNode*> var_to_node_map;

	/*
	 * Every push adds a set of clauses, and the set of clauses
	 * added by every different push are delimited by STACK_DELIMITER.
	 */
	vector<vec<minisat::Lit>* > stack;

	/*
	 * i'th entry of the vector contains the set of minisat literals
	 * that have the appropriate clauses associated with them so that
	 * we do not need to re-insert their clauses.
	 */
	vector<set<int> > vars_stack;

	set<int> permanent_vars;

	/*
	 * permanant_clauses cannot be popped and result from
	 * calls to add().
	 */
	vector<vec<minisat::Lit>*> permanent_clauses;

	/*
	 * The next variable number we can assign to a new variable.
	 * Variable numbers are consecutive.
	 */
	unsigned int next_var;

	/*
	 * Number of false clauses pushed on the stack.
	 */
	unsigned short int num_false_clauses;

	/*
	 * The solver that was used after the last sat query.
	 */
	minisat::Solver* last_solver;

	/*
	 * Ivars for printing stats.
	 */
	int cnf_time;
	int solve_time;
	int num_sat_queries;



public:
	SkeletonSolver();
	void push(CNode* node);
	void pop();
	bool sat();

	/*
	 * If a node is added to the SkeletonSolver, it cannot be popped.
	 */
	void add(CNode* node);

	/*
	 * Makes a conjunct out of the literals consistent with
	 * the model found by the sat solver.
	 */
	CNode* make_conjunct_from_sat_assignment(set<CNode*>& relevant_leaves);

	string stats_to_string();
	~SkeletonSolver();

private:
	void cnode_to_clause_set(CNode* node, vec<minisat::Lit>* antecedent,
			bool use_stack);
	void print_stack();

	string model_to_string(minisat::Solver& s);

};

#endif /* SKELETONSOLVER_H_ */

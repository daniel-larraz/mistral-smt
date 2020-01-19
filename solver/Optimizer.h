/*
 * Optimizer.h
 *
 *  Created on: Nov 15, 2011
 *      Author: isil
 */

#ifndef OPTIMIZER_H_
#define OPTIMIZER_H_

#include "SatValue.h"
#include <map>
using namespace std;

class CNode;
class Term;

class Optimizer {

private:
	CNode* c;
	Term* cost_fn;
	long int upper_bound;
	int opt_cost;
	map<Term*, SatValue> assignments;
	bool min;
	int num_iterations;

	int num_solves;
	int ticks;



public:
	/*
	 * Optimizes the value of cost_fn subject to constraint c.
	 * The boolean min specifies whether we want to minimize cost_fn
	 * (min = true), or whether we want to maximize it (min = false).
	 * The integer bound specifies an upper bound for maximization
	 * problems, and a lower bound for minimization problems.
	 */
	Optimizer(CNode* c, Term* cost_fn, bool min, long int bound,
			int num_iterations = -1);

	/*
	 * If c is unsatisfiable, the optimal cost will be higher than max cost
	 * for maximization problems and lower than min cost for minimization
	 * problems.
	 */
	long int get_optimal_cost();

	const map<Term*, SatValue>& get_assignment();
	~Optimizer();

	string get_stats();

private:
	void maximize();
};

#endif /* OPTIMIZER_H_ */

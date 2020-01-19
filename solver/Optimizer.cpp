/*
 * Optimizer.cpp
 *
 *  Created on: Nov 15, 2011
 *      Author: isil
 */

#include "Optimizer.h"
#include "cnode.h"
#include "term.h"
#include "Solver.h"

Optimizer::Optimizer(CNode* c, Term* cost_fn, bool min, long int bound,
		int num_iterations)
{
	num_solves = 0;
	ticks = 0;

	if(min) {
		cost_fn = cost_fn->multiply(-1);
		bound = -bound;
	}

	this->c = c;
	this->cost_fn = cost_fn;
	this->upper_bound = bound;
	this->min = min;
	this->num_iterations = num_iterations;

	int start = clock();
	maximize();
	int end = clock();
	ticks = end-start;

}

string Optimizer::get_stats()
{
	string res;
	res += "Time (s): " + float_to_string(((double)ticks)/((double)CLOCKS_PER_SEC));
	res +="\nNum Solves: " + int_to_string(num_solves);
	return res;
}

void Optimizer::maximize()
{
	/*
	 * Solve constraint to get initial estimate
	 */
	Solver s(c, UNSAT_SIMPLIFY, &assignments);
	num_solves++;
	CNode* res = s.get_result();

	/*
	 * Constraint is unsat, cost function cannot be optimized
	 */
	if(res->get_type() == FALSE_NODE) {
		opt_cost = upper_bound+1;
		return;
	}

	/*
	 * Evaluate cost function for current assignment;
	 * if it does not evaluate to integer, cost function is not
	 * well formed, so we set optimal cost to an infeasible value.
	 */
	Term* cur_val = cost_fn->evalute_term(assignments);
	if(cur_val->get_term_type() != CONSTANT_TERM) {
		opt_cost = upper_bound+1;
		return;
	}

	ConstantTerm* ct = static_cast<ConstantTerm*>(cur_val);
	long int cur_estimate =  ct->get_constant();

	/*
	 * Now, do a binary search to figure out optimal cost
	 */
	while(cur_estimate < upper_bound)
	{
		if(num_iterations >=0 && num_solves >= num_iterations) break;
		long int middle = (upper_bound + cur_estimate)/2;
		if(middle == cur_estimate) middle++;

		CNode* geq_middle =
				ILPLeaf::make(cost_fn, ConstantTerm::make(middle), ILP_GEQ);

		geq_middle = Connective::make(AND, c, geq_middle);

		/*
		 * Check if cost_fn >= middle is feasible
		 */
		Solver s(geq_middle, UNSAT_SIMPLIFY, &assignments);
		num_solves++;
		CNode* res = s.get_result();

		/*
		 * cost_fn >= middle is feasible, change cur_estimate to
		 * evaluation of cost function
		 */
		if(res->get_type() != FALSE_NODE) {
			Term* cur_val = cost_fn->evalute_term(assignments);
			if(cur_val->get_term_type() != CONSTANT_TERM) {
				opt_cost = upper_bound+1;
				return;
			}
			ConstantTerm* ct = static_cast<ConstantTerm*>(cur_val);
			cur_estimate = ct->get_constant();

		}

		/*
		 * cost_fn >= middle is not feasible, so change upper_bound to
		 * middle-1
		 */
		else {
			upper_bound = middle -1;
		}
	}

	opt_cost = cur_estimate;

}

const map<Term*, SatValue>& Optimizer::get_assignment()
{
	return assignments;
}

long int Optimizer::get_optimal_cost()
{
	if(min) return -opt_cost;
	return opt_cost;
}

Optimizer::~Optimizer()
{
}

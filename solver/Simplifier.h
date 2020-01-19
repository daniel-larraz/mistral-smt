/*
 * Simplifier.h
 *
 *  Created on: Jul 29, 2009
 *      Author: isil
 */

#ifndef SIMPLIFIER_H_
#define SIMPLIFIER_H_

#include "SkeletonSolver.h"
#include "CNode.h"

class DPLLSolver;



class Simplifier {
private:
	CNode* simplification;
	SkeletonSolver s;
	DPLLSolver* dpll_solver;
	bool switch_to_boolean;

public:

	/*
	 * Constructor for the Simplifier that only simplifies the
	 * boolean structure, taking into account the background.
	 * The background may come e.g., from the conflict clauses/
	 * implications learned while solving the formula.
	 */
	Simplifier(CNode* node, CNode* background);


	/*
	 * Constructor for doing theory-specific simplification.
	 * If switch_to_boolean is true, it will heuristically switch to
	 * boolean simplification if theory-specific clauses take (both in total
	 * and on average) too long to verify.
	 */
	Simplifier(CNode* node, DPLLSolver* dpll_solver, bool switch_to_boolean);

	CNode* get_simplification();
	~Simplifier();

private:
	CNode* simplify(CNode* node);

	/*
	 * Does the current background imply/contradict node?
	 * It is assumed background is already on the stack.
	 */
	inline bool is_implied(CNode* node);
	inline bool is_contradictory(CNode* node);

	inline void push_siblings(cnode_type ct, set<CNode*>& simplified_siblings,
			set<CNode*>::iterator cur_it, set<CNode*>::iterator end_it);

	inline void push(CNode* node);
	inline void pop();
	/*
	 * Queries whether the constraints on the stack are SAT.
	 */
	inline bool sat();




};

#endif /* SIMPLIFIER_H_ */

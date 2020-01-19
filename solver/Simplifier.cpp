/*
 * Simplifier.cpp
 *
 *  Created on: Jul 29, 2009
 *      Author: isil
 */

#include "Simplifier.h"
#include "cnode.h"
#include "DPLLSolver.h"

#define DEBUG false
#define STATS false

#define BOOLEAN_SWITCH_THRESHOLD 3
#define MIN_TOTAL_CLAUSE_SOLVE_TIME 0.01
#define MIN_AVG_CLAUSE_SOLVE_TIME 0.0005

#define FIXED_POINT_SIMPLIFY true

Simplifier::Simplifier(CNode* node, CNode* background) {
	this->dpll_solver = NULL;
	this->switch_to_boolean = true;
	if(background->get_type() != TRUE_NODE) s.push(background);
	this->simplification = simplify(node);
	if(STATS) {
		cout << "Simplification stats: " << endl << s.stats_to_string() << endl;
	}

}

Simplifier::Simplifier(CNode* node, DPLLSolver* dpll_solver, bool
		switch_to_boolean)
{
	this->dpll_solver = dpll_solver;
	this->switch_to_boolean = switch_to_boolean;
	simplification = simplify(node);
	if(STATS)
	{
		cout << "Simplification stats: " << endl << dpll_solver->get_stats() << endl;
		cout << "Skeleton solver stats: " << endl << s.stats_to_string() << endl;
	}

}

CNode* Simplifier::get_simplification()
{
	return this->simplification;
}

CNode* Simplifier::simplify(CNode* node)
{

	switch(node->get_type())
	{
	case TRUE_NODE:
	case FALSE_NODE:
	{
		return node;
	}
	case UNIVERSAL:
	case EQ:
	case ILP:
	case MOD:
	case BOOLEAN_VAR:
	case NOT:
	{
		/*if(!sat()) {
			cout << "ACTIVE FALSE: " << endl;
			return False::make();
		}*/
		bool check_contradiction = true;
		bool check_implication = true;
		if(false && dpll_solver!=NULL)
		{
			CNode* assign = dpll_solver->substitute_partial_assignment(node);

			if(assign->get_type() == TRUE_NODE) {
				check_contradiction = false;
			}
			else if(assign->get_type() == FALSE_NODE)
			{
				check_implication = false;
			}
			else {
				cout << " NO QUERIES MADE!!!" << endl;
				return node;
			}

		}

		if(check_implication && is_implied(node)) return True::make();
		if(check_contradiction && is_contradictory(node)) return False::make();

		return node;


	}
	case AND:
	case OR:
	{
		cnode_type ct = node->get_type();
		Connective* conn_c = (Connective*) node;
		const set<CNode*>& children = conn_c->get_operands();

		bool is_simplified = false;
		set<CNode*> new_children;

		set<CNode*>::iterator end_it = children.end();
		set<CNode*>::iterator it = children.begin();
		for(; it!=children.end(); it++)
		{
			CNode* cur = *it;
			push_siblings(ct, new_children, it, end_it);
			CNode* simplified_cur = simplify(cur);
			pop();
			new_children.insert(simplified_cur);


			/*
			 * The whole and node simplifies to false if any of its
			 * children become false.
			 */
			if(simplified_cur->get_type() == FALSE_NODE && ct == AND) {
				return simplified_cur;
			}

			/*
			 * Or node is a tautology if any of its children is
			 * a tautology.
			 */
			if(simplified_cur->get_type() == TRUE_NODE && ct == OR) {
				return simplified_cur;
			}
			if(simplified_cur != cur) is_simplified = true;

		}

		if(!is_simplified) return node;
		CNode* new_node = Connective::make(ct, new_children);
		if(FIXED_POINT_SIMPLIFY) return simplify(new_node);
		else return new_node;


	}
	default:
		assert(false);



	}
}



inline void Simplifier::push_siblings(cnode_type ct, set<CNode*>& simplified_siblings,
		set<CNode*>::iterator cur_it, set<CNode*>::iterator end_it)
{
	set<CNode*> to_push = simplified_siblings;
	cur_it++;
	to_push.insert(cur_it, end_it);
	CNode* new_bg;
	if(ct == AND) {
		new_bg = Connective::make_and(to_push);
	}
	else {
		new_bg = Connective::make_or(to_push);
		new_bg = Connective::make_not(new_bg);
	}
	CNode* simp = new_bg->get_simplification(UNSAT_SIMPLIFY);
	if(simp != NULL){
		new_bg = simp;
	}
	push(new_bg);

}

/*
 * Does background imply node?
 */
inline bool Simplifier::is_implied(CNode* node)
{
	CNode* not_node = Connective::make_not(node);
	push(not_node);
	bool res = sat();
	pop();

	if(DEBUG && dpll_solver!=NULL)
	{
		cout << "Implication query: " << endl;
		cout << dpll_solver->get_stack()->to_string() << " implies " <<
		node->to_string() << "?" << endl;
		cout << "Result: " << (res ? "no" : "yes") << endl;
   	}



	return !res;

}

/*
 * Does the background contradict the node?
 */
inline bool Simplifier::is_contradictory(CNode* node)
{

	push(node);
	bool res = sat();
	pop();

	if(DEBUG && dpll_solver!=NULL)
	{
		cout << "Contradiction query: " << endl;
		cout << dpll_solver->get_stack()->to_string() << " contradicts " <<
		node->to_string() << "?" << endl;
		cout << "Result: " << (res ? "no" : "yes") << endl;
   	}

	return !res;
}

inline void Simplifier::push(CNode* node)
{
	if(dpll_solver != NULL) dpll_solver->push(node);
	if(switch_to_boolean) s.push(node);
}
inline void Simplifier::pop()
{

	if(dpll_solver != NULL) dpll_solver->pop();
	if(switch_to_boolean) s.pop();
}

inline bool Simplifier::sat()
{


	bool res;
	if(dpll_solver == NULL) {
		res= s.sat();

	}
	else {
		res= dpll_solver->is_sat();
		int num_boolean_correct = dpll_solver->get_num_consecutive_boolean_complete();
		double ratio = dpll_solver->boolean_complete_ratio();
		double time_verifying = dpll_solver->time_verifying_boolean_assignment();
		double time_per_clause =
				time_verifying/(double)dpll_solver->num_clauses_checked_in_theory();
		if(switch_to_boolean && time_verifying> MIN_TOTAL_CLAUSE_SOLVE_TIME &&
				time_per_clause >= MIN_AVG_CLAUSE_SOLVE_TIME)
		{

			//cout << "Avg time per clause: " << time_per_clause << endl;
			//if(num_boolean_correct >= BOOLEAN_SWITCH_THRESHOLD || ratio>=0.3) {
				s.add(dpll_solver->get_background_assumptions());
				dpll_solver = NULL;
			//}
		}

	}



	return res;
}


Simplifier::~Simplifier() {

}

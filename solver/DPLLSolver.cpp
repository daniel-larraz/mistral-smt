/*
 * DPLLSolver.cpp
 *
 *  Created on: Jul 30, 2009
 *      Author: tdillig
 */

#include "DPLLSolver.h"
#include "cnode.h"
#include "SkeletonSolver.h"
#include "BooleanAbstractor.h"
#include "ClauseSolve.h"
#include "UnsatCoreFinder.h"
#include "ConflictDatabase.h"


DPLLSolver::DPLLSolver(set<Term*>& ilp_terms, map<Term*, SatValue>* assignments):
	ilp_terms(ilp_terms)
{
	this->assignments = assignments;
	init();
}

DPLLSolver::DPLLSolver(CNode* theory_tautologies,
		set<Term*>& ilp_terms,
		map<Term*, SatValue>* assignments):ilp_terms(ilp_terms)
{
	this->assignments = assignments;
	init();
	s.add(theory_tautologies);
	assumptions = Connective::make(AND, assumptions,
			theory_tautologies);
}

void DPLLSolver::push(CNode* c)
{
	//c = c->rewrite_ilp_neqs(ilp_terms);
	stack_elem se(c);
	int stack_size = stack.size();
	if(stack_size >=1) {
		stack_elem& top = stack[stack_size-1];
		se.leaves.insert(top.leaves.begin(), top.leaves.end());
		se.cumulative_constraint = Connective::make(AND,
				top.cumulative_constraint, c);
	}
	stack.push_back(se);
	s.push(c);

}

void DPLLSolver::restrict(CNode* background)
{
	//background = background->rewrite_ilp_neqs(ilp_terms);
	assert(stack.size() == 0);
	push(background);
	assumptions = Connective::make(AND, assumptions,
			background);
}

void DPLLSolver::pop()
{
	assert(stack.size() > 0);
	stack.pop_back();
	s.pop();
}

void DPLLSolver::init()
{
	total_ticks = 0;
	num_sat_calls = 0;
	check_prev_ticks = 0;
	num_delta = 0;
	ticks_delta = 0;
	clause_ticks = 0;
	num_clause = 0;
	num_sat_clauses = 0;
	sat_clause_ticks = 0;
	num_consecutive_boolean_complete = 0;
	num_sat_by_prev_assignment = 0;
	num_unknown_by_prev_assignment = 0;
	assumptions = True::make();
	current_assignment = NULL;

}


CNode* DPLLSolver::get_current_assignment()
{
	return current_assignment;
}

CNode* DPLLSolver::get_stack()
{
	set<CNode*> active_constraints;
	for(unsigned int i=0; i< stack.size(); i++)
	{
		active_constraints.insert(stack[i].constraint);
	}
	CNode* node = Connective::make_and(active_constraints);
	return node;
}

inline bool DPLLSolver::satisfied_by_prev_assignment(CNode* formula)
{

	int start = clock();
	bool res = satisfied_by_prev_assignment_internal(formula);
	check_prev_ticks += clock() - start;
	return res;
}

/*
 * Checks if we encountered a constraint with same leaves and whether any
 * of the previous assignments satisfies this formula
 */
inline bool DPLLSolver::satisfied_by_prev_assignment_internal(CNode* formula)
{

	set<CNode*> leaves;
	formula->get_all_leaves(leaves);
	if(leaves_to_assignments.count(leaves) == 0){
		num_unknown_by_prev_assignment++;
		return false;
	}
	vector<map<CNode*, bool> >& assignments = leaves_to_assignments[leaves];
	//cout << "VECTOR SIZE: " << assignments.size() << endl;

	for(int i=assignments.size()-1; i>=0; i--)
	{

		map<CNode*, bool>& cur_assign = assignments[i];
		if(formula->evaluate_assignment(cur_assign)->get_type() == TRUE_NODE)
		{
			num_sat_by_prev_assignment++;
			return true;
		}
	}
	num_unknown_by_prev_assignment++;
	return false;

}

bool DPLLSolver::is_sat()
{

	if(stack.size() == 0){
		return true;
	}

	int start = 0, end = 0;
	start = clock();

	/*
	 * First get the constraint on the stack
	 */
	CNode* node = stack[stack.size()-1].cumulative_constraint;

	/*
	 * Check cache
	 */
	if(node->get_simplification(UNSAT_SIMPLIFY) != NULL && assignments==NULL)
	{
		return node->get_simplification(UNSAT_SIMPLIFY)!= False::make();
	}

	/*
	 * Check if we encountered a constraint with same leaves and whether this
	 * this is a satisfying assignment to the current formula
	 */
	if(satisfied_by_prev_assignment(node)&& assignments==NULL) return true;


	if(node->is_conjunct())
	{

		int cur_pos = stack.size() - 1;
		ClauseSolve cs(node, assignments);
		int end = clock();
		num_clause++;
		clause_ticks+=(end-start);
		total_ticks+=(end-start);
		bool res = cs.is_sat();
		stack[cur_pos].status = (res ? SAT: UNSAT);
		return res;
	}



	set<CNode*>& original_leaves = stack[stack.size()-1].leaves;

	set<CNode*> must_assignments;
	if(node->get_type() == AND)
	{
		Connective* and_c = (Connective*)node;
		set<CNode*>::const_iterator it = and_c->get_operands().begin();
		for(; it != and_c->get_operands().end(); it++)
		{
			CNode* cur = *it;
			if(cur->is_literal()) {
			//	cout << "Must assignment: " << cur->to_string() << endl;
				must_assignments.insert(cur);
			}
		}
	}

	while(true)
	{
		num_sat_calls++;
		if(!s.sat()) {
			sat = false;
			goto end;
		}


		current_assignment = s.make_conjunct_from_sat_assignment(original_leaves);

		if(current_assignment->get_type() == TRUE_NODE) {
			sat = true;
			goto end;
		}

		if(current_assignment->get_type() == FALSE_NODE){
			cout << "Node: " << node->to_string() << endl;
			cout << "Making conjunct from leaves: " << endl;
			set<CNode*>::iterator it = original_leaves.begin();
			for(; it!= original_leaves.end(); it++) {
				cout << "\t " << (*it)->to_string() << endl;
			}
		}

		assert(current_assignment->get_type() != FALSE_NODE);
		bool in_cache = false;
		if(current_assignment->get_simplification(UNSAT_SIMPLIFY)!=NULL)
			in_cache = true;


		ClauseSolve cs(current_assignment, assignments);

		num_clause++;
		clause_ticks += (end-start);
		if(cs.is_sat()) {
			num_sat_clauses++;

			if(!in_cache)
			{

				num_consecutive_boolean_complete++;

				//cout << "sat clause: " << current_assignment->to_string() << endl;
				sat_clause_ticks+=(end-start);

				{
					//delete me
					set<CNode*> leaves;
					current_assignment->get_all_leaves(leaves);


					sat_clauses_with_same_leaves[leaves]++;

					// Only worth doing if it has at least two...
					if(current_assignment->get_type() == AND)
					{
						int start = clock();
						map<CNode*, bool> assignment_map;
						Connective* and_c = (Connective*) current_assignment;
						const set<CNode*>& children = and_c->get_operands();
						set<CNode*>::iterator it = children.begin();
						for(; it!= children.end(); it++)
						{
							CNode* cur = *it;
							if(cur->get_type() == NOT)
							{
								Connective* not_c = (Connective*) cur;
								CNode* leaf = *not_c->get_operands().begin();
								assignment_map[leaf] = false;
							}
							else {
								assignment_map[cur] = true;
							}
						}

						leaves_to_assignments[leaves].push_back(assignment_map);
						check_prev_ticks += clock() - start;
					}

				}


			}
			else num_clause--;
			sat = true;
			goto end;
		}
		num_consecutive_boolean_complete = 0;

		num_delta++;
		start = clock();
		UnsatCoreFinder core_finder(current_assignment, must_assignments);
		//cout << "Minimizing unsat clause: " << current_assignment->to_string() << endl;

		end = clock();
		ticks_delta += end-start;
		CNode* unsat_core = core_finder.get_unsat_core();
		assert(unsat_core->get_type() != FALSE_NODE);


		CNode* learned_implication = Connective::make_not(unsat_core);
		assert(learned_implication->get_type() != TRUE_NODE);

		ConflictDatabase::add_conflict_clause(learned_implication);

	//	cout << "DPLL solver - learned implication: " << learned_implication->to_string() << endl;

		assumptions = Connective::make(AND, assumptions,
				learned_implication);

		s.add(learned_implication);


	}

end:

	end = clock();
	total_ticks += end-start;
	if(sat) node->set_simplification(node, UNSAT_SIMPLIFY);
	else node->set_simplification(False::make(), UNSAT_SIMPLIFY);
	int pos = stack.size() -1;
	stack[pos].status = (sat ? SAT: UNSAT);
	return sat;
}

CNode* DPLLSolver::get_background_assumptions()
{
	return this->assumptions;
}

string DPLLSolver::get_stats()
{
	string res;
	res += "Total time: " +
	float_to_string(((double)total_ticks)/ ((double)CLOCKS_PER_SEC)) + "\n";
	res+= "Num sat calls: " + int_to_string(num_sat_calls) + "\n";

	res+= "Num minimize calls: " + int_to_string(num_delta) + "\n";
	res += "Minimization time: " +
		float_to_string(((double)ticks_delta)/ ((double)CLOCKS_PER_SEC)) + "\n";
	res += "Number of clauses checked in theory: " + int_to_string(num_clause) + "\n";
	res += "Number of satisfiable clauses checked in theory: " +
			int_to_string(num_sat_clauses) + "\n";
	res += "Number of formulas satisfied by previous assignment: " +
			int_to_string(num_sat_by_prev_assignment) + "\n";
	res += "Number of formulas unknown from previous assignments: " +
				int_to_string(num_unknown_by_prev_assignment) + "\n";
	res += "Checked clause solve time for satisfiable clauses: "
			"(excluding minimization)" +
			float_to_string(((double)sat_clause_ticks)/ ((double)CLOCKS_PER_SEC)) + "\n";
	res += "Checked clause solve time for all clauses: (excluding minimization)" +
		float_to_string(((double)clause_ticks)/ ((double)CLOCKS_PER_SEC)) + "\n";

	res += "Checking previous assignment time:" +
		float_to_string(((double)check_prev_ticks)/ ((double)CLOCKS_PER_SEC)) + "\n";

	res += "Clauses sharing leaves: \n";
	map<set<CNode*>, int>::iterator it = sat_clauses_with_same_leaves.begin();
	for(; it!= sat_clauses_with_same_leaves.end(); it++)
	{
		res+= "\t" + int_to_string(it->second) + "\n";
	}

	res += "Learned implications: \n";
	res += assumptions->to_string() + " \n";

	res += "Skeleton stats------------\n";
	res += s.stats_to_string() + "\n";



	return res;



}

CNode* DPLLSolver::substitute_partial_assignment(CNode* constraint)
{
	if(stack.size() == 0) return constraint;
	assert(stack[stack.size()-1].status != UNSAT);
	assert(stack[stack.size()-1].status == SAT);
	map<Term*, SatValue> & cur_assigns = stack[stack.size() -1].assignment;
	CNode* eval = constraint->evaluate_assignment(cur_assigns);
	return eval;


}

DPLLSolver::~DPLLSolver()
{

}

string DPLLSolver::stack_to_string()
{
	string res = "=====BEGIN STACK=====\n";
	for(unsigned int i=0; i< stack.size(); i++)
	{
		res += "  " + stack[i].constraint->to_string() +"\n";
	}
	res += "====END STACK=====\n";
	return res;
}

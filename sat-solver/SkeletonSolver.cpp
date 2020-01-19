/*
 * SkeletonSolver.cpp
 *
 *  Created on: Jul 29, 2009
 *      Author: tdillig
 */

#include "SkeletonSolver.h"
#include "cnode.h"
#include "util.h"

#define DEBUG false

SkeletonSolver::SkeletonSolver()
{
	next_var = 0;
	last_solver = NULL;
	num_false_clauses = 0;
	cnf_time = 0;
	solve_time = 0;
	num_sat_queries = 0;
}

void SkeletonSolver::add(CNode* node)
{
	if(node->get_type() == FALSE_NODE)
	{
		num_false_clauses++;
		return;
	}
	if(node->get_type() == TRUE_NODE) return;

	int start = clock();
    vec<minisat::Lit>* v = new vec<minisat::Lit>();
    cnode_to_clause_set(node,v, false);
    permanent_clauses.push_back(v);
    int end = clock();
    cnf_time += end-start;

}

void SkeletonSolver::push(CNode* node)
{
	vars_stack.push_back(set<int>());
	size_t s = vars_stack.size();
	if(vars_stack.size()>1) {
		set<int> & old_vars = vars_stack[s-2];
		vars_stack[s-1].insert(old_vars.begin(), old_vars.end());
	}

	int start = clock();
	if(DEBUG) cout << "Pushing: " << node->to_string() << endl;
	if(node->get_type() == TRUE_NODE) {
		stack.push_back(STACK_DELIMITER);
		return;
	}
	if(node->get_type() == FALSE_NODE) {
		stack.push_back(FALSE_CLAUSE);
		stack.push_back(STACK_DELIMITER);
		++num_false_clauses;
		return;
	}


	vec<minisat::Lit>* v = new vec<minisat::Lit>();
	cnode_to_clause_set(node, v, true);
    stack.push_back(v);
    stack.push_back(STACK_DELIMITER);
    int end = clock();
    cnf_time += end-start;

    if(DEBUG) {
    	cout << "Size of stack: " << stack.size() << endl;
    	print_stack();
    }


}

void SkeletonSolver::print_stack()
{
	cout << "=====STACK====" << endl;
	int cur = 0;
	string level = "";
	while(cur < (int)stack.size())
	{
		vec<minisat::Lit>* clause = stack[cur++];
		if(clause == NULL) {
			level += "\t";
			continue;
		}
		if(clause == FALSE_CLAUSE) {
			cout << level + "false \n";
			continue;
		}

		cout << level;
		for(int i=0; i<clause->size(); i++)
		{
			minisat::Lit lit = (*clause)[i];
			bool lit_sign = sign(lit);
			minisat::Var v = var(lit);
			CNode* node = var_to_node_map[v];
			cout << (lit_sign ? "!" : "")  << (node!=NULL? node->to_string():
				"v" +int_to_string(v) );
			if(i!= clause->size() -1) cout << " | ";
			else cout << endl;
		}

	}
	cout << "=====END STACK====" << endl;
}



void SkeletonSolver::pop()
{
	assert(stack.size() > 0);
	stack.pop_back();
	vars_stack.pop_back();
	int stack_size = stack.size();
	int end = stack_size-1;

	if(stack[end] == FALSE_CLAUSE) {
		--num_false_clauses;
		stack.pop_back();
		if(DEBUG) {
			cout << "Pop... " << endl;
			print_stack();
		}
		return;
	}

	if(stack[end] == NULL) return;


	while(end >= 0 && stack[end] != NULL)
	{
		vec<minisat::Lit>* to_remove = stack[end];
		stack.pop_back();
		delete to_remove;
		end--;
	}

	if(DEBUG){
		cout << "Pop... " << endl;
		print_stack();
	}
	return;



}


bool SkeletonSolver::sat()
{
	num_sat_queries++;
	if(this->num_false_clauses > 0) return false;

	int start = clock();
	delete last_solver;
	minisat::Solver* solver  = new minisat::Solver();
	solver->reserveVars(var_to_node_map.size());

	/*for(unsigned int i = 0; i < var_to_node_map.size(); i++)
		solver->newVar();*/

	for(unsigned int i=0; i<permanent_clauses.size(); i++)
	{
		solver->addClause(*permanent_clauses[i]);
	}


	for(unsigned int i=0; i<stack.size(); i++)
	{
		if(stack[i] == NULL) continue;
		solver->addClause(*(stack)[i]);
	}

	bool res = solver->solve();
	int end = clock();
	solve_time += end-start;
	last_solver = solver;
	return res;


}

/*
 * Makes a conjunct out of the literals consistent with
 * the model found by the sat solver.
 */
CNode* SkeletonSolver::make_conjunct_from_sat_assignment(set<CNode*>&
		relevant_leaves)
{
	if(last_solver == NULL) return NULL;
	if(!last_solver->ok) return NULL;
	set<CNode*> children;
	set<CNode*>::iterator it = relevant_leaves.begin();
	for(; it!=relevant_leaves.end(); it++)
	{
		CNode* c = *it;
		if(c->get_type() == BOOLEAN_VAR) continue;

		int var_id = node_to_var_map[c];
		int truth_val = last_solver->model[var_id].toInt();
		if(truth_val == 1) {
			children.insert(c);
		}
		else {
			CNode* not_c = Connective::make_not(c);
			children.insert(not_c);
		}

	}


	CNode* res = Connective::make_and(children);
	return res;

}

string SkeletonSolver::model_to_string(minisat::Solver & s)
{
	string res;
	int size = s.model.size();
	for(int i=0; i<size; i++)
	{
		CNode* node = var_to_node_map[i];
		//if(!node->is_leaf()) continue;
		res+= "\t v" + int_to_string(i) +" (" + node->to_string()
				+ "): " + int_to_string(s.model[i].toInt()) + "  ";
	}
	return res;
}

void SkeletonSolver::cnode_to_clause_set(CNode* node, vec<minisat::Lit>*
		antecedent, bool use_stack)
{

	/*
	 * OR node: we don't need a new id for this node.
	 */
	if(node->get_type() == OR)
	{
		Connective* c= (Connective*) node;
		const set<CNode*>& children = c->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* child = *it;
			cnode_to_clause_set(child, antecedent, use_stack);
		}
		return;
	}


	/*
	 * If this is a negation, set node to be the inner leaf.
	 */
	bool is_neg = (node->get_type() == NOT);
	if(is_neg){
		node = *((Connective*) node)->get_operands().begin();
	}

	minisat::Var my_id;
	if(node_to_var_map.count(node) > 0) {
		my_id = node_to_var_map[node];
		size_t var_stack_size = vars_stack.size();
		if(permanent_vars.count(my_id) > 0 || (var_stack_size >0 &&
				vars_stack[var_stack_size-1].count(my_id) > 0))
		{
			antecedent->push(minisat::Lit(my_id, is_neg));
			return;
		}

	}
	else {
		my_id = this->next_var++;
		node_to_var_map[node] = my_id;
		var_to_node_map[my_id] = node;
	}
	if(use_stack)
	{
		vars_stack[vars_stack.size()-1].insert(my_id);
	}
	else
	{
		permanent_vars.insert(my_id);
	}

	/*
	 * If the node is a leaf or negation, insert it into its own clause
	 * and return its id.
	 */

	if(node->is_literal())
	{
		minisat::Lit l(my_id, is_neg);
		antecedent->push(l);
		return;
	}

	// AND case
	minisat::Lit my_lit(my_id, false);
	minisat::Lit my_lit_neg(my_id, true);


	assert(node->get_type() == AND);
	Connective* and_c = (Connective*) node;

	const set<CNode*>& children = and_c->get_operands();
	set<CNode*>::iterator it = children.begin();
	for(; it!= children.end(); it++)
	{
		CNode* child = *it;
		vec<minisat::Lit>* v = new vec<minisat::Lit>();
		v->push(my_lit_neg);
		cnode_to_clause_set(child, v, use_stack);
		if(use_stack) stack.push_back(v);
		else permanent_clauses.push_back(v);

	}
	antecedent->push(my_lit);
}

string SkeletonSolver::stats_to_string()
{
	string res = "Num sat queries: " + int_to_string(num_sat_queries) + "\n";
	res += "Sat solving time: " +
		float_to_string((((double)(solve_time))/((double)CLOCKS_PER_SEC))) + "\n";
	res += "CNF construction time: " +
	float_to_string((((double)(cnf_time))/((double)CLOCKS_PER_SEC))) + "\n";
	return res;
}

SkeletonSolver::~SkeletonSolver()
{

	delete last_solver;

	for(unsigned int i=0; i<permanent_clauses.size(); i++)
	{
		vec<minisat::Lit>* clause = permanent_clauses[i];
		delete clause;
	}

	for(unsigned int i=0; i<stack.size(); i++)
	{
		vec<minisat::Lit>* clause = stack[i];
		if(clause == NULL) continue;
		if(clause == FALSE_CLAUSE) continue;
		delete clause;
	}

}

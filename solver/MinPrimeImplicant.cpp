/*
 * MinPrimeImplicant.cpp
 *
 *  Created on: Nov 18, 2011
 *      Author: isil
 */

#include "MinPrimeImplicant.h"
#include "cnode.h"
#include "Optimizer.h"

#define DEBUG false

MinPrimeImplicant::MinPrimeImplicant(CNode* c, set<CNode*>& background,
		map<VariableTerm*, int>& costs):
	costs(costs), background(background)
{
	this->orig_constraint = c;
	this->constraint = c;
	init_max_cost();
	build_boolean_abstraction();
	add_theory_constraints();
	add_cost_constraints();
	add_background_constraints();
	init_opt_function();

	if(DEBUG) {
		cout << "Optimizing function: " << opt_function->to_string() <<
				" subject to constraint \n: " <<
			constraint->to_string() << endl;
		cout << "Attrib constraints: " <<
				constraint->get_attribute_constraints()->to_string() << endl;
	}


	Optimizer o(constraint, opt_function, true, 0, 1);
	min_cost = o.get_optimal_cost();
	const map<Term*, SatValue>& opt_assign = o.get_assignment();

	if(DEBUG) cout << "====== OPTIMIZER ASSIGNMENTS========" << endl;

		map<Term*, SatValue>::const_iterator it = opt_assign.begin();
		for(; it!= opt_assign.end(); it++)
		{
			Term* t = it->first;
			SatValue var_assign = it->second;

			if(DEBUG)
				cout << t->to_string() << " -> " << var_assign.to_string() << endl;

			if(vars_to_cost_vars.count(t) == 0) continue;
			Term* cost_var = vars_to_cost_vars[t];
			map<Term*, SatValue>::const_iterator it2 = opt_assign.find(cost_var);
			assert(it2 != opt_assign.end());
			SatValue cost_var_assign = it2->second;


			if(cost_var_assign.value != 0) {
				min_assignment[t] = var_assign;
			}
		}
		if(DEBUG)
			cout << "====== OPTIMIZER ASSIGNMENTS DONE========" << endl;



}

void MinPrimeImplicant::init_max_cost()
{

	max_cost = 0;
	set<Term*> orig_vars;
	orig_constraint->get_vars(orig_vars);
	for(set<Term*>::iterator it = orig_vars.begin(); it!= orig_vars.end(); it++)
	{
		Term* t= *it;
		if(t->get_term_type() != VARIABLE_TERM) continue;
		VariableTerm* vt = static_cast<VariableTerm*>(t);
		if(costs.count(vt) > 0) max_cost += costs[vt];
		else max_cost++;
	}


}

void MinPrimeImplicant::add_background_constraints()
{

	string name = "cost_bg_violated";
	bg_violated_cost_var = VariableTerm::make(name);
	bg_violated_cost_var->set_attribute(TERM_ATTRIB_GEQZ);

	Term* high_cost = ConstantTerm::make(max_cost+1);
	CNode* bg_var_eq_high_cost = EqLeaf::make(bg_violated_cost_var, high_cost);


	for(set<CNode*>::iterator it = background.begin();
			it!= background.end(); it++)
	{
		CNode* bg = *it;
		CNode* neg_bg = Connective::make_not(bg);
		CNode* neg_bg_implies_high_cost =
				Connective::make_implies(neg_bg, bg_var_eq_high_cost);
		constraint = Connective::make(AND, constraint, neg_bg_implies_high_cost);
	}
}


int MinPrimeImplicant::get_cost()
{
	return min_cost;
}
const map<Term*, SatValue>& MinPrimeImplicant::get_min_assignment()
{
	return min_assignment;
}


/*
 * Initialize the minimization function called opt_function
 */
void MinPrimeImplicant::init_opt_function()
{
	opt_function = ConstantTerm::make(0);
	if(constraint->contains_term(bg_violated_cost_var))
		opt_function = bg_violated_cost_var;


	map<Term*, Term*>::iterator it = vars_to_cost_vars.begin();
	for(; it!= vars_to_cost_vars.end(); it++)
	{
		Term* cost_var = it->second;
		opt_function = opt_function->add(cost_var);
	}
}

/*
 * If a boolean variable b that stands for literal L with variables x1, .., xk
 * is set to true, variable cxi representing cost of variable xi is set to
 * cost(xi).
 * i.e.,: b -> (cx1 = cost(x1) & ... & cxk = cost(xk))
 */
void MinPrimeImplicant::add_cost_constraints()
{


	CNode* implications = True::make();


	for(map<CNode*, BooleanVar*>::iterator it = literal_to_bool.begin();
		it!= literal_to_bool.end(); it++)
	{
		BooleanVar* cur_bool = it->second;
		CNode* cur_literal = it->first;

		set<Term*> lit_vars;
		cur_literal->get_vars(lit_vars);

		CNode* imp_rhs = True::make(); //rhs of implication
		for(set<Term*>::iterator it = lit_vars.begin();
				it!= lit_vars.end(); it++)
		{
			Term* cur_var = *it;
			Term* cost_var = NULL;
			if(vars_to_cost_vars.count(cur_var) > 0)
			{
				cost_var = vars_to_cost_vars[cur_var];
			}
			else {
				string name = "cost_" + cur_var->to_string();
				cost_var = VariableTerm::make(name);
				cost_var->set_attribute(TERM_ATTRIB_GEQZ);
				vars_to_cost_vars[cur_var] = cost_var;
			}

			int cost = 1;

			if(cur_var->get_term_type() == VARIABLE_TERM &&
					costs.count(static_cast<VariableTerm*>(cur_var)) > 0 )
				cost = costs[static_cast<VariableTerm*>(cur_var)];
			CNode* cost_eq = EqLeaf::make(cost_var, ConstantTerm::make(cost));

			imp_rhs = Connective::make(AND, cost_eq, imp_rhs);
		}

		CNode* implication = Connective::make_implies(cur_bool, imp_rhs);
		implications = Connective::make(AND, implication, implications);

	}

	constraint = Connective::make(AND, constraint, implications);
}


/*
 * Add constraint stipulating that if some boolean var b is set to true,
 * then this implies its actual theory-specific meaning L.
 * Observe that if b1 stands for L1 and b2 stands for L2 such that L1 and L2
 * are contradictory, this encoding prevents b1 and b2 from both being assigned
 * to true.
 */
void MinPrimeImplicant::add_theory_constraints()
{
	for(map<CNode*, BooleanVar*>::iterator it = literal_to_bool.begin();
		it!= literal_to_bool.end(); it++)
	{
		BooleanVar* cur_bool = it->second;
		CNode* cur_literal = it->first;

		CNode* bool_implies_lit =
				Connective::make_implies(cur_bool, cur_literal);

		constraint = Connective::make(AND, constraint, bool_implies_lit);
	}

	/*for(map<CNode*, BooleanVar*>::iterator it = literal_to_bool.begin();
			it!= literal_to_bool.end(); it++)
		{

			CNode* cur_literal = it->first;
			if(cur_literal->get_type() == NOT) continue;

			CNode* cur_neg = Connective::make_not(cur_literal);
			if(literal_to_bool.count(cur_neg) == 0) continue;


			BooleanVar* cur_bool1 = it->second;
			BooleanVar* cur_bool2 = literal_to_bool[cur_neg];



			CNode* bool1_implies_not2 =
					Connective::make_implies(cur_bool1,
							Connective::make_not(cur_bool2));
			CNode* bool2_implies_not1 =
					Connective::make_implies(cur_bool2,
							Connective::make_not(cur_bool1));

			CNode* imp= Connective::make(AND, bool1_implies_not2, bool2_implies_not1);
			constraint = Connective::make(AND, constraint, imp);
		}

*/


}


/*
 * Build boolean abstraction where each literal is replaced with a
 * unique boolean variable. Observe that, after this step, there are
 * no negated boolean variables in the formula. Thus, if the SAT solver
 * does not assign a boolean variable to true, this means it does
 * not need to be part of the assignment.
 */
void MinPrimeImplicant::build_boolean_abstraction()
{
	set<CNode*> literals;
	constraint->get_all_literals(literals);

	set<CNode*> neg_literals;
	set<CNode*> pos_literals;

	/*
	 * Separate negative and positive literals because we need to substitute the
	 * negative ones first.
	 */
	for(set<CNode*>::iterator it = literals.begin(); it!= literals.end(); it++)
	{
		CNode* cur = *it;
		if(cur->get_type() == NOT) {
			neg_literals.insert(cur);
		}
		else pos_literals.insert(cur);
	}

	/*
	 * Replace negative literals with fresh boolean variable and add to map
	 */
	for(set<CNode*>::iterator it = neg_literals.begin();
			it!= neg_literals.end();  it++)
	{
		CNode* cur = *it;
		BooleanVar* bv = BooleanVar::make();
		literal_to_bool[cur] = bv;
		constraint = constraint->replace(cur, bv);
	}

	/*
	 * Replace positive literals with fresh boolean variable and add to map
	 */
	for(set<CNode*>::iterator it = pos_literals.begin();
			it!= pos_literals.end();  it++)
	{
		CNode* cur = *it;
		BooleanVar* bv = BooleanVar::make();
		literal_to_bool[cur] = bv;
		constraint = constraint->replace(cur, bv);
	}

}

MinPrimeImplicant::~MinPrimeImplicant() {

}

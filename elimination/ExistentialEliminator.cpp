/*
 * ExistentialEliminator.cpp
 *
 *  Created on: Nov 26, 2011
 *      Author: isil
 */

#include "ExistentialEliminator.h"
#include "cnode.h"
#include "term.h"
#include "Cooper.h"
#include "Solver.h"

#define DEBUG false

ExistentialEliminator::ExistentialEliminator(CNode* _c, Term* _t,
		 bool overapproximation)
{

	this->c= _c;
	this->elim_t = _t;
	this->overapprox = overapproximation;
	this->simplify = true;
	if(DEBUG) {
		cout << "elim from " << c->to_string() << " term: " << elim_t->to_string()
			<< endl;
	}
	this->result = eliminate_existential(c);
	if(DEBUG) cout << "Result: " << result->to_string() << endl;


	set<Term*>::iterator it = new_elim_terms.begin();
	for(; it!= new_elim_terms.end(); it++)
	{
		Term* new_elim = *it;
		if(DEBUG) {
			cout << "NEW ELIM TERM: " << new_elim->to_string() << endl;
		}
		if(overapprox) {
			if(DEBUG) {
				cout << "Eliminating from: " << result->to_string() << endl;
			}
			ExistentialEliminator ee(result, new_elim, true);
			this->result = ee.get_result();
			if(DEBUG) {
				cout << "RESULT: " << result->to_string() << endl;
			}

		}
		else {
			CNode* neg_res = Connective::make_not(result);
			if(DEBUG) {
				cout << "Eliminating from: " << neg_res->to_string() << endl;
			}
			ExistentialEliminator ee(neg_res, new_elim, true);
			this->result = Connective::make_not(ee.get_result());
			if(DEBUG) {
				cout << "RESULT: " << result->to_string() << endl;
			}
		}
	}

	if(simplify) {
		Solver s2(result, THEORY_SIMPLIFY);
		result= s2.get_result();
	}


	if(result->contains_term(elim_t)){
		cout << "FAILED TO ELIMINATE " << elim_t->to_string() << " from " <<
				c->to_string() << endl;
		assert(false);
	}
	if(DEBUG)
		cout << "Result simplified: " << result->to_string() << endl;




}

CNode* ExistentialEliminator::get_result()
{
	return result;
}




CNode* ExistentialEliminator::find_disjunctive_equalities(CNode* c,
		Term* elim_t, bool parent_conjunct)
{
	set<Term*> nested_terms;
	c->get_nested_terms(nested_terms, false, false);
	if(nested_terms.count(elim_t) == 0)
	{
		if(parent_conjunct) return True::make();
		else return False::make();
	}


	/*
	 * We know c must contain elim_t because of check above
	 */
	if(c->is_leaf())
	{
		if(c->get_type() == ILP) {
			ILPLeaf* ilp = static_cast<ILPLeaf*>(c);
			if(ilp->get_operator() != ILP_EQ) {
				return True::make();
			}
		}
		if(c->get_type() == MOD) {
			return True::make();
		}
		set<Term*> nested_terms;
		c->get_nested_terms(nested_terms, true, false);
		set<Term*>::iterator it = nested_terms.begin();
		for(; it!= nested_terms.end(); it++) {
			Term* t = *it;
			if(t->get_term_type() == FUNCTION_TERM) {
				if(t->contains_term(elim_t)) {
					if(parent_conjunct) return True::make();
					else return False::make();
				}
			}
		}
		return c;
	}

	if(c->get_type() == AND || c->get_type() == OR){
		bool is_and = (c->get_type() == AND);
		Connective* con = static_cast<Connective*>(c);
		set<CNode*> new_children;
		const set<CNode*>& old_children = con->get_operands();
		set<CNode*>::const_iterator it = old_children.begin();
		for(;it!=old_children.end(); it++){
			CNode* old_child = *it;
			CNode* new_child = find_disjunctive_equalities(old_child, elim_t,
					is_and);
			if(new_child->get_type() == FALSE_NODE && !overapprox)
				return True::make();
			new_children.insert(new_child);
		}
		if(is_and) return Connective::make_and(new_children);
		else return Connective::make_or(new_children);

	}

	if(parent_conjunct) return True::make();
	else return False::make();


}

CNode* ExistentialEliminator::replace_elim_t_in_function(CNode* c, Term* elim_t)
{

	//cout << "Find disjunctive eqs for " << elim_t->to_string()
	//		<< " in " << c->to_string() <<endl;
	CNode* res = find_disjunctive_equalities(c, elim_t, true);
//	cout << "Result: " << res->to_string() << endl;



	CNode* cnf = res->to_cnf();
	CNode* disj_eq;
	if(cnf->get_type() == AND){
		Connective* con = static_cast<Connective*>(cnf);
		disj_eq = *con->get_operands().begin();
	}
	else disj_eq = cnf;

	/*
	 * eq_terms is the set of all things elim_t can be equal to.
	 */
	set<Term*> eq_terms;

	if(disj_eq->get_type() == OR) {
		Connective* con = static_cast<Connective*>(disj_eq);
		const set<CNode*>& ops = con->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++){
			CNode* cur = *it;
			cur->collect_term_equalities(elim_t, eq_terms);
		}
	}
	else {
		disj_eq->collect_term_equalities(elim_t, eq_terms);
	}

	/*
	 * Find all leaves that contain f(t) where t is term to be
	 * eliminated
	 */
	set<CNode*> leaves;
	c->get_all_leaves(leaves);
	set<CNode*> leaves_with_fun;
	set<CNode*>::iterator it = leaves.begin();
	for(; it!=leaves.end(); it++)
	{
		CNode* leaf = *it;
		set<Term*> nested_terms;
		leaf->get_nested_terms(nested_terms,true, false);
		set<Term*>::iterator it =nested_terms.begin();
		for(;it!=nested_terms.end(); it++) {
			Term* cur = *it;
			if(cur->get_term_type() == FUNCTION_TERM &&
					cur->contains_term(elim_t)) {
				leaves_with_fun.insert(leaf);
				break;
			}
		}
	}


	/*
	 * Construct replacement map
	 */
	map<CNode*, CNode*> to_replace;


	for(set<CNode*>::iterator it = leaves_with_fun.begin();
			it!= leaves_with_fun.end(); it++)
	{
		CNode* cur_leaf = *it;
		set<Term*>::iterator it2= eq_terms.begin();
		for(;it2!= eq_terms.end(); it2++) {
			Term* eq_term = *it2;
			CNode* new_c = cur_leaf->substitute(elim_t, eq_term);
			CNode* if_eq = EqLeaf::make(elim_t, eq_term);
			CNode* repl = Connective::make_implies(if_eq, new_c);
			if(to_replace.count(cur_leaf) == 0) {
				to_replace[cur_leaf] = repl;
			}
			else {
				CNode* old_repl = to_replace[cur_leaf];
				CNode* new_repl = Connective::make(AND, repl, old_repl);
				to_replace[cur_leaf] = new_repl;
			}

		}
	}

	CNode* new_c = c->substitute(to_replace);
	return new_c;

}

CNode* ExistentialEliminator::eliminate_existential(CNode* c)
{


	/*
	 * If c doesn't contain this term, nothing to do.
	 */
	if(!c->contains_term(elim_t)) {
		simplify = false;
		if(DEBUG) cout << "c does not contain term " << endl;
		return c;
	}




	/*
	 * If there is an equality involving this term, we just do a substitution.
	 */
	Term* eq_term = c->contains_term_equality(elim_t);
	if(eq_term != NULL) {



		simplify = false;
		/*
		 * Add attributes
		 */
		set<Term*> which_term;
		which_term.insert(elim_t);
		c = c->add_attributes(&which_term);
		CNode* res = c->substitute(elim_t, eq_term);
		if(DEBUG)
		{
			cout << "c before sub: " << c->to_string() << endl;
			cout << "sub: " << elim_t->to_string() << " -> " << eq_term->to_string()
					<< endl;
			cout << "result: " << res->to_string() << endl;
		}
		return res;
	}


	/*
	 * If c is UNSAT, we are done too.
	 */
	Solver s(c, THEORY_SIMPLIFY);
	c = s.get_result();

	if(c->get_type()==FALSE_NODE)
	{
		if(DEBUG) cout << "C is unsat " << endl;
		return c;
	}




	/*
	 * Existential quantifier distributes over disjuncts, so if the outer
	 * level connective is an OR, break it up into simpler subproblems.
	 */
	if(c->get_type() == OR) {
		Connective* conn = static_cast<Connective*>(c);
		set<CNode*> new_ops;
		const set<CNode*>& ops = conn->get_operands();
		for(set<CNode*>::const_iterator it = ops.begin(); it != ops.end(); it++)
		{
			CNode* cur_op = *it;
			ExistentialEliminator ee(cur_op, elim_t, overapprox);
			CNode* new_op = ee.get_result();
			new_ops.insert(new_op);
		}
		return Connective::make_or(new_ops);

	}

	/*
	 * Add attributes
	 */
	set<Term*> which_term;
	which_term.insert(elim_t);
	c = c->add_attributes(&which_term);


	/*
	 * If a variable is contained in function term, figure out all terms it can
	 * be equal to.
	 */
	if(contained_in_function_term(c, elim_t)) {
		//cout << "TERM CONTAINED IN FUNCTION!" << endl;
		//cout << "Before replacement: " << c->to_string() << endl;
		c = replace_elim_t_in_function(c, elim_t);
	//	cout << "After replacement:" << c->to_string() << endl;
	}


	/*
	 * Introduce relevant Ackermannization axioms
	 */
	CNode* new_c = collect_function_terms_containing_elim_t(c);
	if(contained_in_function_term(new_c, elim_t)) {
		assert(false);
	}
	if(c != new_c)
	{
		c = new_c;
		build_map_from_fun_id_to_terms(c);
		CNode* fc_axioms = get_functional_consistency_axioms();

		CNode* c_with_axioms;
		if(overapprox) {
			c_with_axioms = Connective::make(AND, c, fc_axioms);
		}
		else {
			c_with_axioms = Connective::make_implies(fc_axioms, c);
		}

		c = c_with_axioms;
	}


	Cooper cooper(c, elim_t);
	CNode* res = cooper.get_result();
	return res;



}

bool ExistentialEliminator::contained_in_function_term(CNode* c, Term* elim_term)
{
	set<Term*> nested_terms;
	c->get_nested_terms(nested_terms, true, false);
	for(set<Term*>::iterator it = nested_terms.begin(); it!= nested_terms.end(); it++)
	{
		Term* t = *it;
		if(t->get_term_type() != FUNCTION_TERM) continue;
		FunctionTerm* ft = static_cast<FunctionTerm*>(t);
		const vector<Term*>& args = ft->get_args();
		for(vector<Term*>::const_iterator it = args.begin(); it!= args.end(); it++)
		{
			Term* cur = *it;
			if(cur->contains_term(elim_term)) return true;
		}
	}

	return false;
}

CNode* ExistentialEliminator::get_functional_consistency_axioms()
{
	if(DEBUG) {
		cout << "INTRODUCING FC AXIOMS" << endl;
	}
	CNode* fc_axioms = True::make();
	map<int, map<Term*, Term*> >::iterator it = function_terms_to_vars.begin();
	for(; it!= function_terms_to_vars.end(); it++)
	{
		int fun_id = it->first;
		if(function_ids_to_terms.count(fun_id) == 0) continue;
		map<Term*, Term*>& funs_with_elim = it->second;
		set<Term*>& funs_without_elim = function_ids_to_terms[fun_id];

		for(map<Term*, Term*>::iterator it2 = funs_with_elim.begin();
				it2 != funs_with_elim.end(); it2++)
		{
			FunctionTerm* fun_with_elim = static_cast<FunctionTerm*>(it2->first);
			Term* new_term = it2->second;

			if(DEBUG) {
				cout << "FUN 1: " << fun_with_elim->to_string() << " " <<fun_with_elim << endl;
			}

			for(set<Term*>::iterator it3 = funs_without_elim.begin();
					it3 != funs_without_elim.end(); it3++)
			{
				FunctionTerm* fun2 = static_cast<FunctionTerm*>(*it3);
				if(DEBUG) {
					cout << "FUN 2: " << fun2->to_string()<< " " << fun2<< endl;
				}
				if(fun2 == fun_with_elim) continue;


				CNode* args_equal_c = args_equal(fun_with_elim, fun2);
				if(DEBUG) {
					cout << "Args equal: " <<args_equal_c->to_string() << endl;
				}
				CNode* new_var_eq_fun;
				if(funs_with_elim.count(fun2) == 0) {
					new_var_eq_fun = EqLeaf::make(fun2, new_term);
				}
				else {
					Term* new_var2 = funs_with_elim[fun2];
					if(DEBUG) {
						cout << "NEW VAR 2: " << new_var2->to_string() << endl;
					}
					new_var_eq_fun = EqLeaf::make(new_term, new_var2);
				}
				if(DEBUG) {
					cout << "NEW VAR EQ FUN: " << new_var_eq_fun->to_string() << endl;
				}
				CNode* imp = Connective::make_implies(args_equal_c, new_var_eq_fun);
				fc_axioms = Connective::make(AND, fc_axioms, imp);
			}
		}


	}

	return fc_axioms;
}

CNode* ExistentialEliminator::args_equal(FunctionTerm* ft1, FunctionTerm* ft2)
{
	CNode* c = True::make();
	const vector<Term*>& args1 = ft1->get_args();
	const vector<Term*>& args2 = ft2->get_args();
	assert(args1.size() == args2.size());

	for(unsigned int i=0; i<args1.size(); i++)
	{
		Term* t1 = args1[i];
		Term* t2 = args2[i];
		CNode* eq = EqLeaf::make(t1,t2);
		c = Connective::make(AND, c, eq);
	}
	return c;


}

void ExistentialEliminator::build_map_from_fun_id_to_terms(CNode* c)
{
	set<Term*> nested_terms;
	c->get_nested_terms(nested_terms, true, false);
	for(set<Term*>::iterator it = nested_terms.begin();
			it!= nested_terms.end(); it++)
	{
		Term* cur = *it;
		if(cur->get_term_type() != FUNCTION_TERM) continue;

		FunctionTerm* ft = static_cast<FunctionTerm*>(cur);
		int fun_id = ft->get_id();
		if(function_terms_to_vars.count(fun_id) == 0) continue;
		function_ids_to_terms[fun_id].insert(cur);
	}
}

class CompareFunctionTerm:public binary_function<FunctionTerm*, FunctionTerm*,
bool> {

public:
   bool operator()(const FunctionTerm* _b1, const FunctionTerm* _b2) const
   {
	   FunctionTerm* b1 = (FunctionTerm*)_b1;
	   FunctionTerm* b2 = (FunctionTerm*)_b2;
	   if(b1->contains_term(b2)) return false;
	   if(b2->contains_term(b1)) return true;
	   return b1 < b2;
   }
};

CNode* ExistentialEliminator::collect_function_terms_containing_elim_t(CNode* c)
{
	CNode* new_c = c;
	set<Term*> nested_terms;
	c->get_nested_terms(nested_terms,true, false);

	map<Term*, Term*> subs;

	set<FunctionTerm*, CompareFunctionTerm> ordered_terms;

	for(set<Term*>::iterator it = nested_terms.begin();
			it!= nested_terms.end(); it++)
	{
		Term* cur = *it;
		if(cur->get_term_type() != FUNCTION_TERM) continue;

		FunctionTerm* ft = static_cast<FunctionTerm*>(cur);
		ordered_terms.insert(ft);
	}

	for(set<FunctionTerm*, CompareFunctionTerm> ::iterator it = ordered_terms.begin();
			it!= ordered_terms.end(); it++)
	{
		FunctionTerm* ft = *it;
		Term* sub_t= ft->substitute(subs);
		if(sub_t->get_term_type() != FUNCTION_TERM) continue;
		ft = static_cast<FunctionTerm*>(sub_t);
		int fun_id = ft->get_id();

		/*
		 * Check if this function term contain elim_t directly as an argument
		 */
		const vector<Term*>& args = ft->get_args();
		for(vector<Term*>::const_iterator it2 = args.begin(); it2 != args.end(); it2++)
		{
			Term* arg = *it2;
			set<Term*> nested_arg_terms;
			arg->get_nested_terms(nested_arg_terms,false, false);
			if(nested_arg_terms.count(elim_t) == 0) continue;
			if(function_terms_to_vars[fun_id].count(ft) == 0)
			{
				Term* new_var =
						VariableTerm::make("elim{"+ft->to_string() + "}");
				function_terms_to_vars[fun_id][ft] = new_var;
				new_elim_terms.insert(new_var);
				subs[ft]= new_var;
				function_ids_to_terms[fun_id].insert(ft);
				new_c = new_c->substitute(ft, new_var);
			}
			break;

		}
	}
	return new_c;
}

ExistentialEliminator::~ExistentialEliminator()
{

}

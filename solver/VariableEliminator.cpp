/*
 * VariableEliminator.cpp
 *
 *  Created on: Feb 8, 2009
 *      Author: tdillig
 */

#include "VariableEliminator.h"
#include "cnode.h"
#include "term.h"
#include "Solver.h"
#include "Clause.h"
#include "ClauseSolve.h"
#include <algorithm>

#include "Cooper.h"
#include "ExistentialEliminator.h"

#define DEBUG false
#define ELIMINATE_PREFIX "$u"

/*
 * WARNING: Verifying elimination can be very expensive --
 * disable in production runs.
 */
#define VERIFY_ELIMINATION false
#define LCM_LIMIT 6

VariableEliminator::VariableEliminator(CNode *n, vector<VariableTerm*> &
		to_eliminate,
		simplification_level level, bool over_approximate,
		bool track_new_inequalities)
{
	//assert(track_new_inequalities);

	//delete me
	/*
	res = n;
	for(vector<VariableTerm*>::iterator it = to_eliminate.begin();
			it!= to_eliminate.end(); it++)
	{
		VariableTerm* vt = *it;
		ExistentialEliminator ee(res, vt, over_approximate);
		res = ee.get_result();
	}
	return;
	*/

	//delete me end


	this->res = n;
	this->orig_c = n;
	this->large_lcm = false;
	this->track_new_inequalities = track_new_inequalities;
	fresh_var_counter = 0;
	this->over_approximate = over_approximate;
	this->simplify = false;

	for(unsigned int i=0; i < to_eliminate.size(); i++) {
		if(DEBUG) {
			cout << "## Eliminating var: " <<
			to_eliminate[i]->to_string() << endl;
		}

		res = eliminate_var(res, to_eliminate[i]);
		res = res->make_canonical();
		if(DEBUG) {
			cout << "Result of elimination: " << res->to_string() << endl;
		}
		if(large_lcm) {
			cerr << "LARGE LCM!!!! " << n->to_string() << " " <<
				to_eliminate[i]->to_string() << " -> " <<
			res->to_string() << endl;

			large_lcm = false;
		}
	}

	if(simplify && level > UNSAT_SIMPLIFY){
		Solver s(res, level);
		res = s.get_result();
	}



	if(VERIFY_ELIMINATION) {
		if(over_approximate){
			if(!Solver::implies(n, res)){
				cout << "Constraint does not imply necessary cond: " <<
				n->to_string() << " NC: " << res->to_string() << endl;
				assert(false);

			}
		}
	}






}

VariableEliminator::VariableEliminator(CNode *n, VariableTerm* to_eliminate,
		simplification_level level, bool over_approximate,
		bool track_new_inequalities)
{
	//assert(track_new_inequalities);

	//delete me
	/*
	ExistentialEliminator ee(n, to_eliminate, over_approximate);
	res = ee.get_result();
	return;
	*/
	//delete me end


	this->res = n;
	this->orig_c = n;
	this->large_lcm = false;
	this->track_new_inequalities = track_new_inequalities;
	fresh_var_counter = 0;
	this->over_approximate = over_approximate;
	this->simplify = false;

	res = eliminate_var(res, to_eliminate);
	res = res->make_canonical();


	if(simplify && level > UNSAT_SIMPLIFY){
		Solver s(res, level);
		res = s.get_result();
	}

	if(large_lcm) {
		cerr << "LARGE LCM!!!! " << n->to_string() << " " <<
		to_eliminate->to_string() << " -> " <<
		res->to_string() << endl;
	}

	if(VERIFY_ELIMINATION) {
		if(over_approximate) {
			if(!Solver::implies(n, res)){
				cout << "Constraint does not imply necessary cond: " <<
				n->to_string() << " NC: " << res->to_string() << endl;
				assert(false);

			}
		}
	}




}




const map<VariableTerm*, set<pair<Term*, Term*> > > &
VariableEliminator::get_new_inequalities()
{
	return new_inequality_terms;
}


VariableEliminator::~VariableEliminator()
{

}

//-------------------------------------

CNode* VariableEliminator::eliminate_var(CNode* node, VariableTerm* vt)
{
	if(!node->contains_term(vt)) return node;
	set<Term*> which_term;
	which_term.insert(vt);
	node = node->add_attributes(&which_term);
//	cout << "Constraint after attributes: " << node->to_string() << endl;
	CNode* res = eliminate_var_rec(node, vt, True::make());
	//cout << "Res: " << res->to_string() << endl;
	return res;
}

CNode* VariableEliminator::eliminate_var_rec(CNode* node,
		VariableTerm* evar, CNode* active_constraint)
{


	CNode* and_c = Connective::make(AND, node, active_constraint);

	/*CNode* canonical = and_c->make_canonical();
	Solver s(canonical, UNSAT_SIMPLIFY);
	CNode* res_c = s.get_result();
	if(res_c->get_type() == FALSE_NODE) return False::make(); */

	if(DEBUG) {
		cout << "CUR CONSTRAINT: " << node->to_string() << endl;
		cout << "Active constraint: " << active_constraint->to_string() << endl;
	}

	if(!and_c->contains_term(evar)){
		if(DEBUG) {
			cout << "Does not contain var to eliminate " << endl;
			cout << "Result: " << and_c->to_string() << endl;
		}
		return and_c;
	}


	/*
	 * If we can find an equality like t=T', then substitute
	 * every occurence of t in the subtree with T'.
	 */


	Term* sub = and_c->contains_term_equality(evar);
	if(sub != NULL) {
		if(DEBUG){
			cout << "Simple substitution found! " << evar->to_string()
			<< "-> " << sub->to_string() << " in constraint: " <<
			and_c->to_string() << endl;
		}
		map<Term*, Term*> sub_map;
		sub_map[evar] = sub;
		CNode* res = and_c->substitute(sub_map);
		if(DEBUG) {
			cout << "Result: " << res->to_string() << endl;
		}
		return res;

	}


	if(and_c->is_conjunct())
	{
		simplify = true;
		CNode* res = eliminate_var_conjunct(and_c, evar);
		CNode* simp_res = res;
		if(DEBUG) {
			cout << "Base case (conjunct)  " << endl;
			//cout << "Result: " << res->to_string() << endl;
		}
		return simp_res;
	}

	if(node->is_conjunct())
	{
		CNode* res = eliminate_var_rec(and_c, evar, True::make());
		if(DEBUG) {
			cout << "Pseudo base-case: " << endl;
			cout << "Result: " << res->to_string() << endl;
		}
		return res;
	}

	assert(node->is_connective());
	Connective* parent = (Connective*) node;

	bool changed = false;
	set<CNode*> new_children;
	set<CNode*>::const_iterator it = parent->get_operands().begin();

	if(parent->get_type() == OR)
	{
		bool and_active_constraint = false;
		it = parent->get_operands().begin();
		for(; it!= parent->get_operands().end() ;it++)
		{
			CNode* child = *it;
			if(!child->contains_term(evar)) {
				and_active_constraint = true;
				new_children.insert(child);
				continue;
			}
			CNode* new_child = eliminate_var_rec(child, evar,
					active_constraint);
			if(new_child->get_type() == TRUE_NODE) {
				return True::make();
			}
			if(new_child != child) {
				changed = true;
			}
			new_children.insert(new_child);

		}
		if(!changed){
			if(DEBUG)
			{
				cout << "OR not changed: " << endl;
				cout << "Result: " << node->to_string() << endl;
			}
			return node;
		}
		CNode* res = Connective::make_or(new_children);
		if(and_active_constraint) {
			CNode* new_active = eliminate_var_rec(active_constraint, evar, True::make());
			res = Connective::make(AND, res, new_active);
		}

		if(DEBUG) {
			cout << "Or case: " << endl;
			cout << "Result: " << res->to_string() << endl;
		}

		return res;
	}

	if(parent->get_type() == AND) {



		/*
		 * Find a disjunct (one must exist because this is not a conjunct)
		 */
		Connective* c = (Connective*) parent;
		const set<CNode*>& ops = c->get_operands();
		CNode* or_child = NULL;
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* cur = *it;
			if(cur->get_type() == OR && cur->contains_term(evar)) {
				or_child = cur;
				break;
			}
		}

		if(or_child == NULL) {
			set<CNode*> to_and;
			set<CNode*> new_ops;
			const set<CNode*>& ops = c->get_operands();
			it = ops.begin();
			for(; it!= ops.end(); it++) {
				CNode* op = *it;
				if(op->contains_term(evar)) {
					new_ops.insert(op);
				}
				else {
					to_and.insert(op);
				}
			}
			CNode* conjunct = Connective::make_and(new_ops);
			CNode* rec_res = eliminate_var_rec(conjunct, evar, active_constraint);
			to_and.insert(rec_res);

			CNode* res = Connective::make_and(to_and);
			return res;
		}


		/*
		 * Find active constraints containing the var to be eliminated.
		 */
		set<CNode*> containing_evar;
		set<CNode*> no_evar;
		it = ops.begin();
		for(; it!= ops.end(); it++){
			CNode* cur = *it;
			if(cur == or_child) continue;
			if(cur->contains_term(evar)) {
				containing_evar.insert(cur);
			}
			else no_evar.insert(cur);
		}

		//cout << "Current node: " << c->to_string() << endl;
		//cout << "Or child: " << or_child->to_string() << endl;

		CNode* sibling_constraints = Connective::make_and(containing_evar);
		CNode* new_active = Connective::make(AND, active_constraint,
				sibling_constraints);
		CNode* inactive_constraint = Connective::make_and(no_evar);

		assert(or_child != c);
		CNode* rec_res = eliminate_var_rec(or_child, evar, new_active);
		CNode* res = Connective::make(AND, rec_res, inactive_constraint);
		CNode* final_res = res;

		if(DEBUG) {
			cout << "AND case: " << endl;
			cout << "Result: " << final_res->to_string() << endl;
		}


		return final_res;
	}
	assert(false);
}


CNode* VariableEliminator::remove_eq_var_with_no_parents(Clause& cl,
		VariableTerm* evar)
{
	set<EqLeaf*> to_delete;
	set<EqLeaf*>::iterator it = cl.neg_eq.begin();
	for(; it!= cl.neg_eq.end(); it++)
	{
		EqLeaf* eq = *it;
		Term* lhs = eq->get_lhs();
		Term* rhs = eq->get_rhs();
		if(lhs->contains_term(evar) || rhs->contains_term(evar))
			to_delete.insert(eq);
	}

	for(it=to_delete.begin(); it!= to_delete.end(); it++)
	{
		cl.neg_eq.erase(*it);
	}
	CNode* new_node = cl.to_cnode();
	return new_node;

}


CNode* VariableEliminator::eliminate_var_conjunct(CNode* node, VariableTerm* evar)
{

	if(DEBUG) {
		cout << "IN ELIMINATE VAR FROM CONJUNCT " << node->to_string()<< endl;
		cout << "Trying to eliminate: " << evar->to_string() <<endl;
	}

	int initial_count = fresh_var_counter;
	assert(node->is_conjunct());


	Clause cl(node);
	map<Term*, Term*> denestings;
	cl.denest( &denestings);



	if(DEBUG) {
		cout << "DENESTINGS: " << endl;
		map<Term*, Term*>::iterator it = denestings.begin();
		for(; it!= denestings.end(); it++)
		{
			cout << "\t " << it->first->to_string() <<
			"-> " << it->second->to_string() << endl;
		}
	}


	ClauseSolve cs(&cl, NULL);
	bool res = cs.is_sat();



	/*
	 * If the clause is UNSAT, the SNC is false.
	 * We call sat to ensure that all relevant interactions
	 * are propagated between the ILP and EQ domains. After calling
	 * sat, eq_members, var_to_cols etc are properly initialized.
	 */
	if(!res){
		return False::make();
	}

	Term* rep = cs.find_representative(evar);



	Term* valid_rep = NULL;
	if(rep!=NULL && !rep->contains_term(evar) && denestings.count(rep)==0) {
		valid_rep = rep;
	}
	else {
		set<Term*>& eq_class = cs.eq_members[rep];
		set<Term*>::iterator it = eq_class.begin();
		for(; it!= eq_class.end(); it++) {
			Term* cur_t = *it;
			if(!cur_t->contains_term(evar)&&denestings.count(cur_t)==0){
				valid_rep = cur_t;
				break;
			}
		}
	}


	/*
	 * We found one member in the equivalence class of this variable
	 * that does not contain that variable.
	 */
	if(valid_rep != NULL) {
		map<Term*, Term*> subs;
		subs[evar] = valid_rep;
		CNode* res = node->substitute(subs);
		node = node->substitute(denestings);
		return res;
	}


	set<FunctionTerm*> direct_parents;
	get_direct_parents(evar, direct_parents, cs.eq_members);

	if(!over_approximate) {
			if(direct_parents.size() > 0) return False::make();
		}


	/*
	 * Base case: If this term does not contain any parent terms,
	 * eliminate it from the ILP domain
	 */
	if(direct_parents.size() == 0 && cs.ilp_vars.count(evar->get_var_id()) > 0 ){
		set<CNode*> mod_constraints;
		if(DEBUG) {
			cout << "ELIMINATING FROM ILP: " << cl.to_string("&") << endl;
		}
		CNode* res= eliminate_var_from_ilp_domain(cl, evar, mod_constraints);
		if(DEBUG) {
			cout << "AFTER ELIMINATING FROM ILP: " << res->to_string() << endl;
		}
		res = eliminate_denestings(res, denestings, evar, initial_count, false);
		return res;
	}
	else if(direct_parents.size() == 0)
	{
		CNode* res = remove_eq_var_with_no_parents(cl, evar);
		return eliminate_denestings(res, denestings, evar, initial_count,
				false);
	}




	/*
	 * We want to replace each function term in which the variable appears with
	 * a fresh term u, u' etc. and then introduce conditional equality
	 * constraints.
	 * For example, if we have f(x, a) = f(x, b), introduce a=b->u1=u2
	 * where u1 and u2 are the replacements for f(x,a) and f(x,b) respectively.
	 */
	map<VariableTerm*, FunctionTerm*> fresh_vars_to_functions;
	map<FunctionTerm*, VariableTerm*> functions_to_fresh_vars;




	/*
	 * A map from function id's (e.g. f) to all the function terms containing x
	 * as an argument to this function id.
	 */
	map<int, set<FunctionTerm*> > function_id_to_functions;

	{
		introduce_fresh_vars_for_function_terms(cl, evar, direct_parents,
				fresh_vars_to_functions, functions_to_fresh_vars,
				function_id_to_functions);


		if(DEBUG) {
			cout << "FUNCTION ID TO FUNCTIONS: " << endl;
			map<int, set<FunctionTerm*> >::iterator it2 = function_id_to_functions.begin();
			for(; it2 != function_id_to_functions.end(); it2++){
				cout << "Function: " << CNode::get_varmap().get_name(it2->first);
				set<FunctionTerm*>::iterator it3 = it2->second.begin();
				for(; it3!= it2->second.end(); it3++) {
					cout << "\t " << (*it3)->to_string() << endl;
				}
			}
		}
	}



	/*
	 * Introduce conditional equalities
	 * First, introduce conditional equalities between u terms
	 */
	map<CNode*, CNode*> conditional_equalities;
	map<int, set<FunctionTerm*> >::iterator it = function_id_to_functions.begin();
	for(; it!= function_id_to_functions.end(); it++) {
		set<FunctionTerm*>& s1 = it->second;
		set<FunctionTerm*>::iterator it2 = s1.begin();


		for(; it2!= s1.end(); it2++) {
			FunctionTerm* ft1 = *it2;
			set<FunctionTerm*>::iterator it3 = it2;
			it3++;
			for(; it3 != s1.end(); it3++) {
				set<CNode*> ops;
				FunctionTerm* ft2 = *it3;
				assert(ft1->get_args().size()  == ft2->get_args().size());
				for(unsigned int i=0; i< ft1->get_args().size(); i++)
				{
					Term* cur_arg1 = ft1->get_args()[i];
					Term* cur_arg2 = ft2->get_args()[i];
					if(cur_arg1 == evar && cur_arg2 == evar) continue;
					if(cur_arg1 == evar || cur_arg2 == evar) {
						if(cs.ilp_vars.count(evar->get_var_id()) == 0) continue;
					}


					CNode* eq = EqLeaf::make(cur_arg1, cur_arg2);
					ops.insert(eq);
				}
				if(ops.size() == 0) continue;
				CNode* precedent = Connective::make_and(ops);
				assert(functions_to_fresh_vars.count(ft1) > 0);
				assert(functions_to_fresh_vars.count(ft2) > 0);
				VariableTerm* fresh1 = functions_to_fresh_vars[ft1];
				VariableTerm* fresh2 = functions_to_fresh_vars[ft2];
				CNode* antecedent = EqLeaf::make(fresh1, fresh2);
				conditional_equalities[precedent] = antecedent;

			}
		}
	}


	/*
	 * If the variable to be eliminated is a shared variable, also need to
	 * add conditional equalities with non-u terms.
	 */
	 if(cs.ilp_vars.count(evar->get_var_id()) > 0) {
		 map<int, set<FunctionTerm*> > functions_in_clause;
		 get_function_terms_in_clause(cl, functions_in_clause);
		 it = function_id_to_functions.begin();
		 for(; it!= function_id_to_functions.end(); it++) {
			 set<FunctionTerm*>& evar_terms = it->second;
			 if(functions_in_clause.count(it->first)==0) continue;
			 set<FunctionTerm*>& clause_terms = functions_in_clause[it->first];
			 set<FunctionTerm*>::iterator it2 = evar_terms.begin();
			 for(; it2 != evar_terms.end(); it2++) {
				 FunctionTerm* ft1 = *it2;
				 set<FunctionTerm*>::iterator it3 = clause_terms.begin();
				 for(; it3 != clause_terms.end(); it3++) {
					set<CNode*> ops;
					FunctionTerm* ft2 = *it3;
					assert(ft1->get_args().size()  == ft2->get_args().size());
					for(unsigned int i=0; i< ft1->get_args().size(); i++)
					{
						Term* cur_arg1 = ft1->get_args()[i];
						Term* cur_arg2 = ft2->get_args()[i];
						CNode* eq = EqLeaf::make(cur_arg1, cur_arg2);
						ops.insert(eq);
					}
					if(ops.size() == 0) continue;
					CNode* precedent = Connective::make_and(ops);
					assert(functions_to_fresh_vars.count(ft1) > 0);
					VariableTerm* fresh1 = functions_to_fresh_vars[ft1];
					CNode* antecedent = EqLeaf::make(fresh1, ft2);
					conditional_equalities[precedent] = antecedent;

				}

			 }

		 }
	 }


	if(DEBUG)
	{
		cout << "CONDITIONAL EQUALITIES: " << endl;
		map<CNode*, CNode*>::iterator it = conditional_equalities.begin();
		for(; it!= conditional_equalities.end(); it++) {
			CNode* precedent = it->first;
			CNode* antecedent = it->second;
			cout << precedent->to_string() << " => " << antecedent->to_string()
				<< endl;
		}
	}


	/*
	 * Make the new formula anded with the conditional constraints
	 */
	set<CNode*> new_ops;
	CNode* original = cl.to_cnode();
	new_ops.insert(original);
	map<CNode*, CNode*>::iterator cond_it = conditional_equalities.begin();
	for(; cond_it != conditional_equalities.end(); cond_it++)
	{
		CNode* cur_cond = Connective::make_implies(cond_it->first,
				cond_it->second);
		new_ops.insert(cur_cond);
	}
	CNode* new_node = Connective::make_and(new_ops);


	new_node = eliminate_denestings(new_node, denestings, evar, initial_count,
			true);
	return new_node;
}

void VariableEliminator::update_denestings(map<Term*, Term*>& denestings,
		map<Term*, Term*>& substitutions)
{
	map<Term*, Term*> new_denestings;
	map<Term*, Term*>::iterator it = denestings.begin();
	for(; it!= denestings.end(); it++)
	{
		Term* denest_t = it->first;
		if(substitutions.count(denest_t) > 0) continue;
		Term* new_val = it->second->substitute(substitutions);
		new_denestings[denest_t] = new_val;
	}
	denestings = new_denestings;

}

CNode* VariableEliminator::eliminate_denestings(CNode* node,
		map<Term*, Term*>& denestings, VariableTerm* evar, int initial_count,
		bool include_evar)
{
	vector<VariableTerm*> new_evars;
	if(include_evar) new_evars.push_back(evar);


	map<Term*, Term*> subs;
	map<Term*, Term*>::iterator denest_it = denestings.begin();
	for(; denest_it!= denestings.end(); denest_it++) {
		Term* denest_t = denest_it->first;
		Term* actual_t = denest_it->second;
		if(!actual_t->contains_term(evar)) continue;
		assert(denest_t->get_term_type() == VARIABLE_TERM);
		int denest_id = ((VariableTerm*)denest_t)->get_var_id();
		string fresh_name = ELIMINATE_PREFIX + int_to_string(fresh_var_counter++);
		int id = CNode::get_varmap().get_id(fresh_name);
		Term* new_t = VariableTerm::make(id);
		node = node->rename_variable(denest_id, id);
		subs[denest_t] = new_t;

	}

	update_denestings(denestings, subs);
	node = node->substitute(denestings);


	for(int i= initial_count; i<fresh_var_counter; i++) {
		string name = ELIMINATE_PREFIX + int_to_string(i);
		new_evars.push_back((VariableTerm*)VariableTerm::make(name));
	}

	if(DEBUG) {
		cout << "Original node: " << node->to_string() << endl;
		cout << "After introducing u-terms: " << node->to_string() << endl;
	}

	for(unsigned int i=0; i<new_evars.size(); i++)
	{
		node = eliminate_var(node, new_evars[i]);
		if(DEBUG){
			cout << "After eliminating term: " <<
			new_evars[i]->to_string() << "=====> " <<
			node->to_string() << endl;
		}

	}
	return node;

}



void VariableEliminator::get_direct_parents(Term* t, set<FunctionTerm*>& parents,
		map<Term*, set<Term*> >& eq_members)
{
	map<Term*, set<Term*> >::iterator it = eq_members.begin();
	for(; it!= eq_members.end(); it++)
	{
		set<Term*>& eq_class = it->second;
		set<Term*>::iterator it = eq_class.begin();
		for(; it!= eq_class.end(); it++){
			Term* cur_t = *it;
			if(cur_t->get_term_type() != FUNCTION_TERM) continue;
			FunctionTerm* ft = (FunctionTerm*) cur_t;
			const vector<Term*>& args = ft->get_args();
			for(unsigned int i=0; i< args.size(); i++) {
				if(args[i] == t) parents.insert(ft);
			}
		}

	}
}

void VariableEliminator::introduce_fresh_vars_for_function_terms(Clause& cl,
		VariableTerm* elim_term,
		set<FunctionTerm*>& direct_parents,
		map<VariableTerm*, FunctionTerm*>& fresh_vars_to_functions,
		map<FunctionTerm*, VariableTerm*>& functions_to_fresh_vars,
		map<int, set<FunctionTerm*> >& function_id_to_functions)
{
	set<FunctionTerm*>::iterator it = direct_parents.begin();
	for(; it!= direct_parents.end(); it++) {
		introduce_fresh_var_for_function_term(cl, elim_term, *it,
				fresh_vars_to_functions, functions_to_fresh_vars,
				function_id_to_functions);
	}
}
VariableTerm* VariableEliminator::introduce_fresh_var_for_function_term(
		Clause& cl,VariableTerm* elim_term, FunctionTerm* parent,
		map<VariableTerm*, FunctionTerm*>& fresh_vars_to_functions,
		map<FunctionTerm*, VariableTerm*>& functions_to_fresh_vars,
		map<int, set<FunctionTerm*> >& function_id_to_functions)
{
	if(functions_to_fresh_vars.count(parent) > 0)
		return functions_to_fresh_vars[parent];
	const vector<Term*>& args = parent->get_args();
	bool changed = false;
	vector<Term*> new_args;

	for(unsigned int i=0; i< args.size(); i++) {
		Term* cur_arg = args[i];
		if(cur_arg->get_term_type() != FUNCTION_TERM) {
			new_args.push_back(cur_arg);
			continue;
		}
		FunctionTerm* ft_arg = (FunctionTerm*) cur_arg;
		if(!ft_arg->contains_term(elim_term)) {
			new_args.push_back(ft_arg);
			continue;
		}

		VariableTerm* new_arg =
			introduce_fresh_var_for_function_term(cl, elim_term, ft_arg,
				fresh_vars_to_functions, functions_to_fresh_vars,
				function_id_to_functions);

		new_args.push_back(new_arg);
		changed = true;
	}

	FunctionTerm* ft_insert = NULL;
	if(!changed) {
		ft_insert = parent;
	}
	else {
		ft_insert = (FunctionTerm*)
					FunctionTerm::make(parent->get_id(), new_args,
							parent->is_invertible());
	}

	string fresh_name = ELIMINATE_PREFIX + int_to_string(fresh_var_counter++);
	Term* fresh_t = VariableTerm::make(fresh_name);
	assert(fresh_t->get_term_type() == VARIABLE_TERM);
	VariableTerm* fresh_vt = (VariableTerm*) fresh_t;
	fresh_vars_to_functions[fresh_vt] = ft_insert;
	functions_to_fresh_vars[ft_insert] = fresh_vt;
	function_id_to_functions[ft_insert->get_id()].insert(ft_insert);
	replace_function_with_freshvar_in_clause(cl, ft_insert, fresh_vt);
	return fresh_vt;

}

void VariableEliminator::replace_function_with_freshvar_in_clause(Clause& cl,
		FunctionTerm* ft, VariableTerm* fresh_var)
{
	map<EqLeaf*, CNode*> new_to_old;
	set<EqLeaf*>::iterator it = cl.pos_eq.begin();
	for(; it!= cl.pos_eq.end(); it++) {
		EqLeaf* eq = *it;
		CNode* new_eq =
			replace_function_with_freshvar_in_leaf(eq, ft, fresh_var);
		if(eq == new_eq) continue;
		new_to_old[eq] = new_eq;
	}

	map<EqLeaf*, CNode*>::iterator it2 = new_to_old.begin();
	for(; it2!= new_to_old.end(); it2++){
		cl.pos_eq.erase(it2->first);

		if(it2->second->get_type() == EQ)
			cl.pos_eq.insert((EqLeaf*)it2->second);
	}

	new_to_old.clear();

	it = cl.neg_eq.begin();
	for(; it!= cl.neg_eq.end(); it++) {
		EqLeaf* eq = *it;
		CNode* new_eq =
			replace_function_with_freshvar_in_leaf(eq, ft, fresh_var);
		if(eq == new_eq) continue;
		new_to_old[eq] = new_eq;
	}

	it2 = new_to_old.begin();
	for(; it2!= new_to_old.end(); it2++){
		cl.neg_eq.erase(it2->first);
		if(it2->second->get_type() == EQ)
			cl.neg_eq.insert((EqLeaf*)it2->second);
	}
}

CNode* VariableEliminator::replace_function_with_freshvar_in_leaf(
		EqLeaf* eq, FunctionTerm* ft, VariableTerm* fresh_var)
{
	Term* lhs = eq->get_lhs();
	Term* new_lhs = lhs->replace_term(ft, fresh_var);

	Term* rhs = eq->get_rhs();
	Term* new_rhs = rhs->replace_term(ft, fresh_var);

	if(lhs == new_lhs && rhs == new_rhs) return eq;
	return EqLeaf::make(new_lhs, new_rhs);

}

void VariableEliminator::get_function_terms_in_clause(Clause& cl,
		map<int, set<FunctionTerm*> >& functions_in_clause)
{

	set<EqLeaf*>::iterator it = cl.pos_eq.begin();
	for(; it!= cl.pos_eq.end(); it++) {
		set<Term*> terms;
		EqLeaf* eq = *it;
		eq->get_lhs()->get_nested_terms(terms);
		eq->get_rhs()->get_nested_terms(terms);
		set<Term*>::iterator it2 = terms.begin();
		for(; it2 != terms.end(); it2++) {
			Term* t = *it2;
			if(t->get_term_type() != FUNCTION_TERM) continue;
			FunctionTerm* ft = (FunctionTerm*) t;
			functions_in_clause[ft->get_id()].insert(ft);
		}

	}

	 it = cl.neg_eq.begin();
	for(; it!= cl.neg_eq.end(); it++) {
		set<Term*> terms;
		EqLeaf* eq = *it;
		if(eq->get_lhs() == NULL) {
			cout << eq->get_type() << endl;
			cout << "EQ: " << eq->to_string() << endl;
		}

		eq->get_lhs()->get_nested_terms(terms);
		eq->get_rhs()->get_nested_terms(terms);
		set<Term*>::iterator it2 = terms.begin();
		for(; it2 != terms.end(); it2++) {
			Term* t = *it2;
			if(t->get_term_type() != FUNCTION_TERM) continue;
			FunctionTerm* ft = (FunctionTerm*) t;
			functions_in_clause[ft->get_id()].insert(ft);
		}
	}

	if(DEBUG)
	{
		cout << " --- FUNCTIONS IN CLAUSE ---- " << endl;
		map<int, set<FunctionTerm*> >::iterator it = functions_in_clause.begin();
		for(; it != functions_in_clause.end(); it++) {
			cout << "Function: " << CNode::get_varmap().get_name(it->first) << endl;
			set<FunctionTerm*>::iterator it2 = it->second.begin();
			for(; it2!= it->second.end(); it2++) {
				cout << "\t " << (*it2)->to_string() << endl;
			}
		}
	}
}

ILPLeaf* VariableEliminator::find_ilp_equality_with_evar(Clause& cl,
		VariableTerm* evar)
{
	ILPLeaf* eq_ilp = NULL;
	set<ILPLeaf*>::iterator it = cl.pos_ilp.begin();
	for(; it!= cl.pos_ilp.end(); it++) {
		ILPLeaf* ilp = *it;
		if(ilp->get_operator() != ILP_EQ) continue;
		if(!ilp->contains_var(evar->get_var_id())) continue;
		const map<Term*, long int>& elems = ilp->get_elems();
		if(elems.count(evar) == 0) continue;
		long int coef = elems.find(evar)->second;

		assert(coef != 0);
		// If we can find an equality with coefficient 1 or -1,
		// so if there are any such eqalities, favor those.
		if(coef == 1 || coef == -1) {
			return  ilp;
		}

		eq_ilp = ilp;

	}
	return eq_ilp;
}

Term* VariableEliminator::get_ilp_substitution(ILPLeaf* eq_ilp, Term* evar)
{
	map<Term*, long int> term_elems;
	const map<Term*, long int>& elems = eq_ilp->get_elems();
	map<Term*, long int>::const_iterator it = elems.begin();
	for(; it!= elems.end(); it++)
	{
		Term* t = it->first;
		if(t == evar) continue;
		int cur_coef = it->second;
		cur_coef = -cur_coef;
		term_elems[t] = cur_coef;
	}
	long int constant = eq_ilp->get_constant();
	Term* t = ArithmeticTerm::make(term_elems, constant);
	return t;

}

CNode* VariableEliminator::apply_ilp_substitution(ILPLeaf* ilp, Term* evar,
		Term* sub, long int coef)
{
	long int other_coef = ilp->get_coefficient(evar);
	long int m = lcm(coef, other_coef);
	long int sub_factor = labs(m/coef);
	long int other_factor = labs(m/other_coef);

	if(!have_same_sign(coef, other_coef)) {
		sub_factor = -sub_factor;
	}
	Term* new_sub = sub->multiply(sub_factor);


	CNode* _other_ilp = ilp->multiply(other_factor);
	_other_ilp = _other_ilp->fold_negated_ilps();
	assert(_other_ilp->get_type() == ILP);
	ILPLeaf* other_ilp = (ILPLeaf*) _other_ilp;
	map<Term*, long int> new_elems = other_ilp->get_elems();
	new_elems.erase(evar);
	if(new_elems.count(new_sub) == 0){
		new_elems[new_sub] = 1;
	}
	else {
		new_elems[new_sub]+=1;
	}

	CNode* new_ilp = ILPLeaf::make(other_ilp->get_operator(), new_elems,
			other_ilp->get_constant());
	new_ilp = new_ilp->fold_negated_ilps();

	return new_ilp;

}

void VariableEliminator::apply_ilp_substitution(Clause& cl, Term* evar,
		Term* sub, long int coef)
{

	set<ILPLeaf*> old_pos = cl.pos_ilp;
	cl.pos_ilp.clear();
	set<ILPLeaf*>::iterator it = old_pos.begin();
	for(; it!= old_pos.end(); it++){
		ILPLeaf* cur = *it;
		if(!cur->contains_elem(evar)) {
			cl.pos_ilp.insert(cur);
			continue;
		}
		CNode* new_ilp = apply_ilp_substitution(cur, evar, sub, coef);

		// Assert node is not false because we should have already detected
		// this contradiction while solving.
		assert(new_ilp->get_type() != FALSE_NODE);


		if(new_ilp->get_type() == TRUE_NODE) continue;
		else if(new_ilp->get_type() == ILP) {
			cl.pos_ilp.insert((ILPLeaf*)new_ilp);
		}
		else if(new_ilp->get_type()== EQ) {
			cl.pos_eq.insert((EqLeaf*)new_ilp);
		}
		else assert(false);

	}

	set<ILPLeaf*> old_neg = cl.neg_ilp;
	cl.neg_ilp.clear();
	it = old_neg.begin();
	for(; it!= old_neg.end(); it++){
		ILPLeaf* cur = *it;
		if(!cur->contains_elem(evar)) {
			cl.neg_ilp.insert(cur);
			continue;
		}
		CNode* new_ilp = apply_ilp_substitution(cur, evar, sub, coef);

		// Assert node is not true because this would mean
		// we have a contradiction that we did not detect earlier
		assert(new_ilp->get_type() != TRUE_NODE);


		if(new_ilp->get_type() == FALSE_NODE) continue;
		else if(new_ilp->get_type() == ILP) {
			cl.neg_ilp.insert((ILPLeaf*)new_ilp);
		}
		else if(new_ilp->get_type()== EQ) {
			cl.neg_eq.insert((EqLeaf*)new_ilp);
		}
		else assert(false);

	}
}

void VariableEliminator::separate_equations_by_sign(Clause& cl,
		Term* evar, set<ILPLeaf*>&
		positive, set<ILPLeaf*>& negative)
{
	set<ILPLeaf*>::iterator it = cl.pos_ilp.begin();
	for(; it!= cl.pos_ilp.end(); it++)
	{
		ILPLeaf* ilp = *it;
 		if(!ilp->contains_elem(evar)){
 			continue;
 		}
		long int coef = ilp->get_coefficient(evar);
		if(coef > 0)
			positive.insert(ilp);
		else
			negative.insert(ilp);
	}
}

void VariableEliminator::get_neq_equations_with_evar(Clause& cl,
		Term* evar, set<Leaf*> & neqs)
{
	set<ILPLeaf*>::iterator it = cl.neg_ilp.begin();
	for(; it!= cl.neg_ilp.end(); it++)
	{
		ILPLeaf* ilp = *it;
		if(ilp->contains_elem(evar)) {
			neqs.insert(ilp);
		}
	}

	assert(evar->get_term_type() == VARIABLE_TERM);
	VariableTerm* vt = (VariableTerm*) evar;
	set<EqLeaf*>::iterator it2 = cl.neg_eq.begin();
	for(; it2!= cl.neg_eq.end(); it2++)
	{
		EqLeaf* eq = *it2;
		if(eq->contains_var(vt->get_var_id()))
			neqs.insert(eq);

	}
}

CNode* VariableEliminator::expand_neq_constraints(Clause& cl, set<Leaf*>& neqs)
{
	set<Leaf*>::iterator it = neqs.begin();
	for(; it!= neqs.end(); it++)
	{
		Leaf* l = *it;
		if(l->get_type() == ILP)
			cl.neg_ilp.erase((ILPLeaf*)l);
		else
			cl.neg_eq.erase((EqLeaf*)l);
	}

	CNode* node = cl.to_cnode();
	set<CNode*> to_and;
	to_and.insert(node);
	for(it=neqs.begin(); it!=neqs.end(); it++)
	{
		Leaf* l = *it;
		CNode* lt  = NULL;
		CNode* gt = NULL;
		if(l->get_type() == ILP) {
			ILPLeaf* ilp = (ILPLeaf*) l;
			lt = ILPLeaf::make(ILP_LT, ilp->get_elems(), ilp->get_constant());
			lt = lt->fold_negated_ilps();
			gt = ILPLeaf::make(ILP_GT, ilp->get_elems(), ilp->get_constant());
			gt = gt->fold_negated_ilps();
		}
		else {
			EqLeaf* eq = (EqLeaf*) l;
			map<Term*, long int> elems;
			elems[eq->get_lhs()] = 1;
			elems[eq->get_rhs()] = -1;
			lt = ILPLeaf::make(ILP_LT, elems, 0);
			lt = lt->fold_negated_ilps();
			gt = ILPLeaf::make(ILP_GT, elems, 0);
			gt = gt->fold_negated_ilps();
		}
		CNode* disjunct = Connective::make(OR, lt, gt);
		to_and.insert(disjunct);
	}
	return Connective::make_and(to_and);


}

bool VariableEliminator::expand_neq_constraints_with_bound(Clause& cl,
		set<Leaf*>& neqs, set<ILPLeaf*>& result, Term* evar, bool lt)
{
	set<Leaf*>::iterator it = neqs.begin();
	for(; it!= neqs.end(); it++)
	{
		Leaf* l = *it;
		if(l->get_type() == ILP){
			cl.neg_ilp.erase((ILPLeaf*)l);
			long int coef = ((ILPLeaf*)l)->get_coefficient(evar);
			if(coef < 0){
				CNode* n =((ILPLeaf*)l)->multiply(-1);
				n = n->fold_negated_ilps();
				assert(n->is_leaf());
				l = (Leaf*) n;
			}
		}
		else cl.neg_eq.erase((EqLeaf*)l);


		ILPLeaf* to_insert = NULL;
		if(lt) {
			CNode* _ilp_lt = NULL;
			if(l->get_type() == ILP) {
				ILPLeaf* ilp = (ILPLeaf*) l;
				_ilp_lt = ILPLeaf::make(ILP_LT, ilp->get_elems(),
						ilp->get_constant());
				_ilp_lt = _ilp_lt->fold_negated_ilps();

			}
			else {
				EqLeaf* eq = (EqLeaf*) l;
				map<Term*, long int> elems;
				elems[eq->get_lhs()] = 1;
				elems[eq->get_rhs()] = -1;
				_ilp_lt = ILPLeaf::make(ILP_LT, elems, 0);
				_ilp_lt = _ilp_lt->fold_negated_ilps();
			}
			cnode_type ct = _ilp_lt->get_type();
			if(ct == FALSE_NODE) return false;
			if(ct == TRUE_NODE) continue;
			assert(ct == ILP);
			to_insert = (ILPLeaf*) _ilp_lt;

		}
		else {
			CNode* _ilp_gt = NULL;
			if(l->get_type() == ILP) {
				ILPLeaf* ilp = (ILPLeaf*) l;
				_ilp_gt = ILPLeaf::make(ILP_GT, ilp->get_elems(),
						ilp->get_constant());
				_ilp_gt = _ilp_gt->fold_negated_ilps();
			}
			else {
				EqLeaf* eq = (EqLeaf*) l;
				map<Term*, long int> elems;
				elems[eq->get_lhs()] = 1;
				elems[eq->get_rhs()] = -1;
				_ilp_gt = ILPLeaf::make(ILP_GT, elems, 0);
				_ilp_gt = _ilp_gt->fold_negated_ilps();
			}
			cnode_type ct = _ilp_gt->get_type();
			if(ct == FALSE_NODE) return false;
			if(ct == TRUE_NODE) continue;
			assert(ct == ILP);
			to_insert = (ILPLeaf*) _ilp_gt;
		}

		cl.pos_ilp.insert(to_insert);
		result.insert(to_insert);


	}
	return true;
}

bool VariableEliminator::contains_related_var(set<Leaf*> neq,
		VariableTerm* evar)
{
	set<int> ids;
	int evar_id = evar->get_var_id();
	set<Leaf*>::iterator it = neq.begin();
	for(; it!= neq.end(); it++) {
		set<int> cur_ids;
		Leaf* l = *it;
		l->get_vars(cur_ids);
		cur_ids.erase(evar_id);
		set<int> res;
		set_intersection(ids.begin(), ids.end(), cur_ids.begin(),
				cur_ids.end(), insert_iterator<set<int> >
				(res, res.begin()) );
		if(res.size() > 0) return true;
		ids.insert(cur_ids.begin(), cur_ids.end());
	}
	return false;
}

/*
 * Checks if the evar is only contained in a single
 * mod leaf. If this is the case, returns this mod constraint,
 * otherwise null.
 */
ModLeaf* VariableEliminator::find_single_mod_constraint(Clause& cl,
		VariableTerm* evar)
{
	set<ILPLeaf*>::iterator it = cl.pos_ilp.begin();
	for(; it!= cl.pos_ilp.end(); it++)
	{
		ILPLeaf* ilp = *it;
		if(ilp->contains_term(evar)) return NULL;
	}
	for(it= cl.neg_ilp.begin(); it!=cl.neg_ilp.end(); it++)
	{
		ILPLeaf* ilp = *it;
		if(ilp->contains_term(evar)) return NULL;
	}

	set<EqLeaf*>::iterator it2 = cl.neg_eq.begin();
	for(; it2!= cl.neg_eq.end(); it2++)
	{
		EqLeaf* eq = *it2;
		if(eq->contains_term(evar)) return NULL;
	}

	ModLeaf* only_mod = NULL;
	set<ModLeaf*>::iterator it3 = cl.pos_mod.begin();
	for(; it3!= cl.pos_mod.end(); it3++)
	{
		ModLeaf* mod = *it3;
		if(mod->contains_term(evar)){
			if(only_mod!=NULL) return NULL;
			only_mod = mod;
		}

	}

	it3 = cl.neg_mod.begin();
	for(; it3!= cl.neg_mod.end(); it3++)
	{
		ModLeaf* mod = *it3;
		if(mod->contains_term(evar)){
			if(only_mod!=NULL) return NULL;
			only_mod = mod;
		}

	}

	return only_mod;

}

CNode* VariableEliminator::eliminate_var_from_ilp_domain(Clause& cl,
		VariableTerm* evar, set<CNode*>& mod_constraints)
{

	if( DEBUG) {
		cout << "Eliminating " << evar->to_string()<< " from: "
			<< cl.to_string(" & ") << endl;
	}

	/*
	 * First check if there is an equality term this variable is involved in
	 */
	ILPLeaf* eq_ilp = find_ilp_equality_with_evar(cl, evar);
	if(eq_ilp != NULL) {
		long int coef = eq_ilp->get_coefficient(evar);
		Term* sub = get_ilp_substitution(eq_ilp, evar);
		cl.pos_ilp.erase(eq_ilp);
		long int abs_coef = (coef > 0) ? coef: -coef;
		if(coef != 1) {
			int zero = 0;
			CNode* ml = ModLeaf::make(sub, abs_coef, zero);
			mod_constraints.insert(ml);
		}

		apply_ilp_substitution(cl, evar, sub, coef);
		CNode* c1 = cl.to_cnode();
		CNode* c2 = Connective::make_and(mod_constraints);
		CNode* res = Connective::make(AND, c1, c2);
		return res;

	}

	/*
	 * Edge case: Check if this variable is only involved in a single
	 * mod constraint. If this is the case, drop the constraint
	 */
	ModLeaf* single_mod = find_single_mod_constraint(cl, evar);
	if(single_mod != NULL) {
		cl.pos_mod.erase(single_mod);
		cl.neg_mod.erase(single_mod);
		return cl.to_cnode();
	}


	/*
	 * Convert all mod constraints containing variables to be eliminated as ilp
	 * leaves, then also eliminate the temporaries
	 */
	set<VariableTerm*> to_eliminate;
	set<ModLeaf*> to_delete;
	set<ModLeaf*>::iterator it = cl.pos_mod.begin();
	for(; it!= cl.pos_mod.end(); it++)
	{
		ModLeaf* ml = *it;
		if(!ml->contains_term(evar)) continue;
		to_delete.insert(ml);
		set<ILPLeaf*> ilps;
		int id = fresh_var_counter++;
		ml->to_ilp(ilps, true, id);
		cl.pos_ilp.insert(ilps.begin(), ilps.end());
		to_eliminate.insert(ml->get_ilp_temp(id));
	}
	set<ModLeaf*>::iterator delete_it = to_delete.begin();
	for(; delete_it != to_delete.end(); delete_it++)
	{
		assert(cl.pos_mod.count(*delete_it) > 0);
		cl.pos_mod.erase(*delete_it);
	}
	to_delete.clear();

	it = cl.neg_mod.begin();
	for(; it!= cl.neg_mod.end(); it++)
	{
		ModLeaf* ml = *it;
		if(!ml->contains_term(evar)) continue;
		to_delete.insert(ml);
		set<ILPLeaf*> ilps;
		int id = fresh_var_counter++;
		ml->to_ilp(ilps, true, id);
		cl.pos_ilp.insert(ilps.begin(), ilps.end());
		to_eliminate.insert(ml->get_ilp_temp(id));
	}
	delete_it = to_delete.begin();
	for(; delete_it != to_delete.end(); delete_it++)
	{
		cl.neg_mod.erase(*delete_it);
	}


	/*
	 * Recheck if there is an equality term this variable is involved in
	 */
	eq_ilp = find_ilp_equality_with_evar(cl, evar);
	if(eq_ilp != NULL) {
		long int coef = eq_ilp->get_coefficient(evar);
		Term* sub = get_ilp_substitution(eq_ilp, evar);
		cl.pos_ilp.erase(eq_ilp);
		long int abs_coef = (coef > 0) ? coef: -coef;
		if(coef != 1) {
			int zero = 0;
			CNode* ml = ModLeaf::make(sub, abs_coef, zero);
			mod_constraints.insert(ml);
		}

		apply_ilp_substitution(cl, evar, sub, coef);
		CNode* c1 = cl.to_cnode();
		CNode* c2 = Connective::make_and(mod_constraints);
		CNode* res = Connective::make(AND, c1, c2);
		/*
		 * Finally eliminate the temporaries
		 */
		return eliminate_mod_temps(res, to_eliminate);


	}


	set<ILPLeaf*> positive;
	set<ILPLeaf*> negative;
	set<Leaf*> neqs;
	separate_equations_by_sign(cl, evar, positive, negative);
	get_neq_equations_with_evar(cl, evar, neqs);

	/*
	 * We will need to introduce disjunct for negative ilp leaves
	 * and make a recursive call if:
	 * (i) neq's is non-empty and (ii) both positive and negative
	 * are not empty.
	 */
	if((neqs.size() > 0 && positive.size()>0 && negative.size()>0) ||
			contains_related_var(neqs, evar))
	{
		CNode* new_problem = expand_neq_constraints(cl, neqs);
		return eliminate_var_rec(new_problem, evar, True::make());
	}

	if(neqs.size() >0 && positive.size() > 0)
	{
		bool res =expand_neq_constraints_with_bound(cl, neqs, positive, evar,
				true);
		if(!res) return False::make();
	}

	else if(neqs.size() > 0 && negative.size() > 0)
	{
		bool res = expand_neq_constraints_with_bound(cl, neqs, negative, evar,
				false);
		if(!res) return False::make();
	}
	else
	{
		set<Leaf*>::iterator it = neqs.begin();
		for(; it!= neqs.end(); it++){
			Leaf* l = *it;
			if(l->get_type() == ILP)
				cl.neg_ilp.erase((ILPLeaf*)l);
			else {
				cl.neg_eq.erase((EqLeaf*)l);
			}

		}
	}



	/*
	 * At this point, we've gotten rid of all negative ilp leaves
	 * containing the evar.
	 */
	CNode* res_cooper = apply_cooper(cl, evar, positive, negative);

	/*
	 * Finally eliminate the temporaries
	 */
	return eliminate_mod_temps(res_cooper, to_eliminate);





}

inline void VariableEliminator::add_new_inequality(Term* evar, ILPLeaf* pos,
		ILPLeaf* neg)
{

	long int rhs_constant = pos->get_constant();
	map<Term*, long int> new_elems;
	const map<Term*, long int>&pos_elems = pos->get_elems();
	map<Term*, long int>::const_iterator it = pos_elems.begin();
	for(; it!= pos_elems.end(); it++)
	{
		if(it->first == evar) continue;
		new_elems[it->first] = -it->second;
	}
	Term* rhs_t = ArithmeticTerm::make(new_elems, rhs_constant);


	long int lhs_constant = -neg->get_constant();
	map<Term*, long int> neg_elems = neg->get_elems();
	neg_elems.erase(evar);

	Term* lhs_t = ArithmeticTerm::make(neg_elems, lhs_constant);

	assert(evar->get_term_type() == VARIABLE_TERM);
	VariableTerm* vt = (VariableTerm*)evar;

	this->new_inequality_terms[vt].insert(
			pair<Term*, Term*>(lhs_t, rhs_t));

}


CNode* VariableEliminator::apply_cooper(Clause& cl, Term* evar,
		set<ILPLeaf*>& positive, set<ILPLeaf*>& negative)
{
	if(DEBUG){
		cout << "Applying Cooper's method..." << cl.to_string("&") <<
		"to eliminate " << evar->to_string() << endl;
	}
	set<CNode*> new_constraints;
	set<ILPLeaf*>::iterator pos_it = positive.begin();
	for(; pos_it!= positive.end(); pos_it++)
	{
		ILPLeaf* pos_ilp = *pos_it;
		long int pos_coef = pos_ilp->get_coefficient(evar);
		set<ILPLeaf*>::iterator neg_it = negative.begin();
		for(; neg_it != negative.end(); neg_it++)
		{
			ILPLeaf* neg_ilp = *neg_it;
			long int neg_coef = neg_ilp->get_coefficient(evar);
			long int pos_neg_lcm = lcm(pos_coef, neg_coef);
			long int pos_factor = labs(pos_neg_lcm/pos_coef);
			long int neg_factor = labs(pos_neg_lcm/neg_coef);


			CNode* _pos_ilp = pos_ilp->multiply(pos_factor);
			_pos_ilp = _pos_ilp->fold_negated_ilps();
			assert(_pos_ilp->get_type() == ILP);
			ILPLeaf* pos_ilp = (ILPLeaf*) _pos_ilp;


			CNode* _neg_ilp = neg_ilp->multiply(neg_factor);
			_neg_ilp = _neg_ilp->fold_negated_ilps();
			assert(_neg_ilp->get_type() == ILP);
			neg_ilp = (ILPLeaf*) _neg_ilp;
			CNode* new_node = pos_ilp->add(neg_ilp);
			new_node = new_node->fold_negated_ilps();

			if(new_node->get_type() == FALSE_NODE){
				return False::make();
			}

			if(track_new_inequalities) {
				add_new_inequality(evar, pos_ilp, neg_ilp);
			}


			if(pos_neg_lcm > LCM_LIMIT){
				large_lcm = true;
				cerr << "Large LCM in existential quantifier elimination --"
						"INTRODUCINGS *LOTS OF* DISJUNCTS" << endl;
				cerr << "Original constraint: " << orig_c->to_string() << endl;
				cerr << "Var to eliminate: " << evar->to_string() << endl;
				cerr << "Current clause: " << cl.to_string("&") << endl;
				//assert(false);
				return True::make();
			}
			set<CNode*> to_or;
			vector<CNode*> divisibility_vec;
			set<CNode*> divisibility_set;
			map<Term*, long int> new_elems = neg_ilp->get_elems();
			new_elems.erase(evar);
			long int new_constant = -neg_ilp->get_constant();

			Term* t=ArithmeticTerm::make(new_elems,new_constant);


			for(int i=0; i<pos_neg_lcm; i++){
				Term* cur_t = t->add(i);
				CNode* ml = ModLeaf::make(cur_t,pos_neg_lcm,(long int)0);
				divisibility_set.insert(ml);
				divisibility_vec.push_back(ml);
			}

			if(new_node->get_type() == TRUE_NODE)
			{
				CNode* divisibility_node = Connective::make_or(divisibility_set);
				new_constraints.insert(divisibility_node);
				continue;
			}

			assert(new_node->get_type() == ILP);
			ILPLeaf* ilp = (ILPLeaf*) new_node;
			assert(ilp->get_operator() == ILP_LEQ);
			const map<Term*, long int>& elems = ilp->get_elems();
			long int ilp_constant = ilp->get_constant();
			for(int i=0;i<pos_neg_lcm;i++){
				CNode* cur_ilp = ILPLeaf::make(ILP_LEQ, elems, ilp_constant-i);
				CNode* mod_c = divisibility_vec[i];
				CNode* and_c = Connective::make(AND, cur_ilp, mod_c);
				to_or.insert(and_c);
			}
			CNode* or_c = Connective::make_or(to_or);
			new_constraints.insert(or_c);

		}
	}

	set<ILPLeaf*>::iterator it = positive.begin();
	for(; it!= positive.end(); it++){
		cl.pos_ilp.erase(*it);
	}
	it = negative.begin();
	for(; it!= negative.end(); it++){
		cl.pos_ilp.erase(*it); //this is not a mistake --negative refers to sign
	}
	CNode* orig = cl.to_cnode();
	new_constraints.insert(orig);
	CNode* res = Connective::make_and(new_constraints);
	return res;
}

CNode* VariableEliminator::eliminate_mod_temps(CNode* node, set<VariableTerm*>&
		to_eliminate)
{
	set<VariableTerm*> new_vars;
	set<VariableTerm*>::iterator it = to_eliminate.begin();
	for(; it!= to_eliminate.end(); it++)
	{
		VariableTerm* old_t = *it;
		string fresh_name = ELIMINATE_PREFIX + int_to_string(fresh_var_counter++);
		VariableTerm* new_t = (VariableTerm*)VariableTerm::make(fresh_name);
		map<Term*, Term*> subs;
		subs[old_t] = new_t;
		node = node->substitute(subs);
		new_vars.insert(new_t);
	}

	set<VariableTerm*>::iterator it2 = new_vars.begin();
	for(; it2!= new_vars.end(); it2++) {
		node = eliminate_var(node, *it2);
	}
	return node;
}






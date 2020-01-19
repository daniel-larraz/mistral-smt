/*
 * UniversalInstantiator.cpp
 *
 *  Created on: Sep 12, 2008
 *      Author: tdillig
 */

#include "CNode.h"
#include "UniversalInstantiator.h"
#include "assert.h"
#include "Connective.h"
#include "EqLeaf.h"
#include "ILPLeaf.h"
#include "QuantifiedLeaf.h"
#include "VarMap.h"
#include "util.h"
#include "VariableTerm.h"
#include "ConstantTerm.h"
#include "FunctionTerm.h"
#include "ArithmeticTerm.h"
#include "util.h"
#include "True.h"
#include "False.h"

#define DEBUG false

UniversalInstantiator::UniversalInstantiator(CNode* node, bool * success)
{
	cur_varindex = 0;
	new_conn = process_clause(node);
	if(new_conn == NULL)
	{
		error();
		return;
	}

	this->success = success;
	if(this->success != NULL)
		*this->success = true;




	/*assert(node->get_type() == OR);
	cur_varindex = 0;
	Connective *outer = (Connective*) node;
	const set<CNode*> & elems = outer->get_operands();

	set<CNode*> operands;
	set<CNode*>::iterator it = elems.begin();
	for(; it!= elems.end(); it++){
		CNode* cur = process_clause(*it);
		if(cur == NULL)
		{
			error();
			new_conn = NULL;
			return;
		}
		operands.insert(cur);
	}
	new_conn = Connective::make_or(operands);
	this->success = success;
	if(this->success != NULL)
		*this->success = true;*/

	if(DEBUG)
	{
		cout << "***Final instantiated constraint****" << endl;
		cout << new_conn->to_string() << endl;
	}
}

/*
 * Returns the resulting constraint after instantiating the quantified
 * variables. The return value must be deleted by whoever calls this method.
 */
CNode* UniversalInstantiator::get_constraint()
{
	return new_conn;
}

/*
 * Checks whether the given node contains any quantifiers; if so,
 * we have nothing to do here.
 */
bool UniversalInstantiator::contains_quantifier(CNode* _c)
{
	assert(_c->get_type() != OR);
	if(_c->get_type() == AND || _c->get_type() == NOT ) {
		Connective* c = (Connective*) _c;
		set<CNode*>::iterator it = c->get_operands().begin();
		for(; it!= c->get_operands().end(); it++)
		{
			CNode* cur = *it;
			if(cur->get_type() == UNIVERSAL)
				return true;
			if(cur->get_type() == NOT){
				Connective *cnot = (Connective*)cur;
				if((*cnot->get_operands().begin())->get_type() == UNIVERSAL)
					return true;
			}
		}
		return false;
	}



	return _c->get_type() == UNIVERSAL;
}


/*
 * Substitutes variables if there are any
 * active subtituitons (this is the case if an existentially
 * quantified variable appears in a leaf.)
 */
CNode* UniversalInstantiator::process_eq_leaf(EqLeaf* l,map<int,int>& var_subs,
			QuantifiedLeaf* ql)
{

	Term* lhs = l->get_lhs();
	Term *new_lhs = process_term(lhs, var_subs , -1, -1, ql);
	if(new_lhs == NULL)
		return NULL;
	Term *rhs = l->get_rhs();
	Term* new_rhs = process_term(rhs, var_subs, -1, -1, ql);
	if(new_rhs == NULL)
		return NULL;

	return EqLeaf::make(new_lhs, new_rhs);

}
/*
 * Substitutes variables if there are any
 * active subtituitons & byuilds the fun_arg_universal
 * and reverse_fun_arg universal maps. This is
 * recursive since we need to cdr down
 * nested function terms.
 */
Term* UniversalInstantiator::process_term(Term* t, map<int,int> & var_subs,
		int fun_id, int arg_num, QuantifiedLeaf* ql)
{
	if(t->get_term_type() == CONSTANT_TERM) return t;

	if(t->get_term_type() == VARIABLE_TERM){
		VariableTerm* vt = (VariableTerm*)t;
		int var_id = vt->get_var_id();
		if(var_subs.count(var_id)>0){
			Term* new_vt = VariableTerm::make(var_subs[var_id]);
			return new_vt;
		}
		else if(fun_id != -1 && ql!= NULL &&
				ql->get_quantified_vars().count(var_id) >0)
		{
			assert(arg_num != -1);
			qvar qv;

			//qv.orig_id = ql->get_orig_id();
			qv.id = (long int) ql;
			qv.var_id = var_id;

			map<int, int> *fun_map = NULL;
			if(fun_arg_universal.count(qv)>0) {
				fun_map = fun_arg_universal[qv];
			}
			else
			{
				fun_map = new map<int, int>();
				fun_arg_universal[qv] = fun_map;
			}
			if(fun_map->count(fun_id) == 0){
				(*fun_map)[fun_id] = arg_num;
				pair<int, int> key(fun_id, arg_num);
				set<qvar>* val = reverse_fun_arg_universal[key];
				if(val == NULL){
					val = new set<qvar>();
					reverse_fun_arg_universal[key] = val;

				}
				val->insert(qv);
			}
			else {
				if((*fun_map)[fun_id] != arg_num)
					return NULL;
			}
		}
		return t;
	}
	if(t->get_term_type() == FUNCTION_TERM)
	{
		FunctionTerm* ft = (FunctionTerm*)t;
		vector<Term*> new_args;
		for(unsigned int i=0; i < ft->get_args().size(); i++)
		{
			Term* cur_arg = process_term(ft->get_args()[i], var_subs,
					ft->get_id(), i, ql);
			if(cur_arg == NULL){
				return NULL;
			}
			new_args.push_back(cur_arg);
		}
		Term* new_ft = FunctionTerm::make(ft->get_id(), new_args,
				ft->is_invertible());
		return new_ft;
	}
	else {
		assert(t->get_term_type() == ARITHMETIC_TERM);
		ArithmeticTerm* at = (ArithmeticTerm*) t;
		bool changed = false;
		map<Term*, long int> new_elems;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for(; it!= at->get_elems().end(); it++){
			Term* new_t = process_term(it->first, var_subs, -1, -1, ql);
			if(new_t == NULL) return NULL;
			new_elems[new_t] = it->second;
		}
		if(!changed) return at;
		Term* new_at = ArithmeticTerm::make(new_elems, at->get_constant());
		return new_at;
	}


}

/*
 * Applies existential substitutions if any are active.
 */
CNode* UniversalInstantiator::process_ilp_leaf(ILPLeaf*l,
		map<int,int> & var_subs, QuantifiedLeaf* ql)
{
	if(var_subs.size() == 0) return l;
	map<Term*, long int >::const_iterator it = l->get_elems().begin();
	map<Term*, long int > elems;
	bool changed = false;
	for(; it != l->get_elems().end(); it++)
	{
		Term* t = it->first;
		long int c = it->second;
		Term* new_t = process_term(t, var_subs, -1, -1, ql);
		if(new_t == NULL) return NULL;

		if(new_t != t) {
			changed = true;
		}
		elems[new_t]= c;
	}
	if(!changed) return l;
	return ILPLeaf::make(l->get_operator(), elems, l->get_constant());
}

/*
 * Preprocessing constitutes pushing negations in,
 * eliminating existential quantifiers, and building
 * the fun_arg_universal map which we later use to
 * compute the index set.
 */
bool UniversalInstantiator::preprocess_constraint(CNode* c)
{
	map<int, int> var_subs;
	return rec_preprocess_constraint(c,	true, var_subs, NULL)!=NULL;
}


CNode* UniversalInstantiator::rec_preprocess_constraint(CNode* c,
		bool phase, map<int,int> & var_subs, QuantifiedLeaf* outer_ql)
{
	assert(c!=NULL);
	if(c->get_type() == TRUE_NODE) {
		if(phase) return c;
		return False::make();
	}

	if(c->get_type() == FALSE_NODE) {
		if(phase) return c;
		return True::make();
	}

	if(c->get_type() == EQ) {
		CNode* cur = process_eq_leaf((EqLeaf*)c, var_subs, outer_ql);
		if(cur == NULL) return NULL;
		if(phase) return cur;
		return Connective::make_not(cur);
	}
	if(c->get_type() == ILP) {
		CNode* cur = process_ilp_leaf((ILPLeaf*)c, var_subs, outer_ql);
		if(cur == NULL)
			return NULL;
		if(phase) return cur;
		return Connective::make_not(cur);
	}
	if(c->get_type() == UNIVERSAL)
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*)c;
		if(phase == true)
		{
			if(var_subs.size()>0 || outer_ql != NULL)
				return NULL;
			CNode* index_guard = NULL;
			if(ql->get_index_guard()!= NULL){
				index_guard =
					rec_preprocess_constraint(ql->get_index_guard(),
							!phase, var_subs, ql);
				if(index_guard == NULL){
					return NULL;
				}
			}
			CNode* value_guard = NULL;
			if(ql->get_value_guard() != NULL){
				value_guard = rec_preprocess_constraint(
						ql->get_value_guard(), phase, var_subs, ql);
				if(value_guard == NULL){
					return NULL;
				}
			}
			CNode* new_ql = QuantifiedLeaf::make(ql->get_quantified_vars(),
					index_guard, value_guard);
			return new_ql;
		} else {
			if(var_subs.size()>0 || outer_ql != NULL)
				return NULL;
			map<int, int> subs = var_subs;
			set<int>::iterator it = ql->get_quantified_vars().begin();
			for(; it != ql->get_quantified_vars().end(); it++)
			{
				subs[*it] = CNode::get_varmap().get_id(
						"$e"+int_to_string(cur_varindex++));
			}
			CNode* index_guard =rec_preprocess_constraint(ql->get_index_guard(),
					true, subs, NULL);
			if(index_guard == NULL)
				return NULL;
			CNode* value_guard =rec_preprocess_constraint(ql->get_value_guard(),
					false, subs, NULL);
			if(value_guard == NULL)
				return NULL;
			CNode *c_and = Connective::make(AND, index_guard, value_guard);
			return c_and;
		}
	}
	if(c->get_type() == NOT)
	{
		Connective *con = (Connective*)c;
		CNode* inner = *con->get_operands().begin();
		return rec_preprocess_constraint(inner, !phase, var_subs,
				outer_ql);
	}


	assert(c->get_type() == OR || c->get_type() == AND);
	Connective* con = (Connective*)c;

	set<CNode*> to_add;
	set<CNode*>::const_iterator it = con->get_operands().begin();
	for(; it != con->get_operands().end(); it++)
	{
		CNode *res = rec_preprocess_constraint(*it, phase, var_subs,
				outer_ql);
		if(res == NULL)
			return NULL;
		to_add.insert(res);
	}

	CNode* res = NULL;
	if(!phase)
	{
		if(con->get_type() == AND){
			res = Connective::make_or(to_add);
		}
		else if(con->get_type() == OR)
			res = Connective::make_or(to_add);
	}
	else
	{

		res = Connective::make(con->get_type(), to_add);

	}

	return res;

}


CNode* UniversalInstantiator::process_clause(CNode* c)
{
	if(!contains_quantifier(c)){
		return c;
	}

	if(!preprocess_constraint(c)){
		error();
		return NULL;
	}

	set<int> empty;
	if(!build_index_set(c, empty))
	{
		delete_fun_arg_universal();
		error();
		return NULL;
	}

	if(DEBUG) {
		cout << "+++++++Index set: +++++++" << endl;
		map<qvar, set<Term*>* >::iterator it = index_set.begin();
		for(; it!= index_set.end(); it++) {
			cout << "For qvar " << CNode::get_varmap().get_name(
					it->first.var_id) << endl;
			set<Term*>::iterator it2 = it->second->begin();
			for(; it2!= it->second->end(); it2++) {
				cout << "\t" << (*it2)->to_string() << endl;
			}
		}

	}

	map<int,Term*> init_map;
	CNode * res = instantiate_universals(c, init_map);
	sub_exp_to_var_id.clear();
	delete_fun_arg_universal();

	if(DEBUG){
		cout << "***** instantiated universals *******" << endl;
		cout << res->to_string() << endl;
	}

	return res;



}
/*
 * Cdr's down terms to build the index set.
 * This can only be called if the term is not in index guard.
 */
bool  UniversalInstantiator::build_index_set_term(Term* t, set<int> &qvars,
		int fun_id, int arg_num)
{
	if(t->get_term_type() == FUNCTION_TERM)
	{
		FunctionTerm* ft = (FunctionTerm*)t;
		bool contains_uvar = false;
		for(unsigned int i=0; i < ft->get_args().size(); i++) {
			bool res =
				build_index_set_term(ft->get_args()[i], qvars, ft->get_id(), i);
			if(res) contains_uvar = true;
		}
		if(contains_uvar) return true;
	}
	if(t->get_term_type() == ARITHMETIC_TERM)
	{
		bool contains_uvar = false;
		ArithmeticTerm* at = (ArithmeticTerm*) t;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for(; it!=at->get_elems().end(); it++){
			bool res = build_index_set_term(it->first, qvars, -1, -1);
			if(res) contains_uvar = true;
		}
		if(contains_uvar) return true;
	}


	pair<int, int> key(fun_id, arg_num);
	if(reverse_fun_arg_universal.count(key) ==0) return false;
	if(t->get_term_type() == VARIABLE_TERM){
		VariableTerm* vt = (VariableTerm*) t;
		if(qvars.count(vt->get_var_id()) != 0){
			return true;
		}
	}

	Term* se = t;
	set<qvar>* val = reverse_fun_arg_universal[key];
	if(val->size() == 0) {
		return false;
	}
	bool added = false;
	set<qvar>::iterator it = val->begin();
	for(; it!= val->end(); it++){
		set<Term*>* s = index_set[*it];
		if(s == NULL){
			s= new set<Term*>();
			index_set[*it] =s;
		}
		unsigned int old_size = s->size();
		s->insert(se);
		if(s->size() > old_size) added = true;
	}
	return false;
}


bool UniversalInstantiator::build_index_set(CNode* clause, set<int> &qvars)
{
	if(clause->get_type() == AND || clause->get_type() == OR ||
		clause->get_type() == NOT)
	{
		Connective* c = (Connective*) clause;
		set<CNode*>::iterator it = c->get_operands().begin();
		for(; it != c->get_operands().end(); it++)
		{
			if(!build_index_set(*it, qvars))
				return false;
		}
		return true;
	}
	if(clause->get_type() == EQ)
	{
		EqLeaf* l = (EqLeaf*)clause;
		build_index_set_term(l->get_lhs(), qvars, -1, -1);
		build_index_set_term(l->get_rhs(), qvars, -1, -1);
		return true;
	}


	if(clause->get_type() == UNIVERSAL)
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*) clause;
		if(!build_index_set_index_guard(ql->get_index_guard(),
				ql->get_quantified_vars(), ql))
			return false;
		return build_index_set(ql->get_value_guard(), ql->get_quantified_vars());
	}
	return true;
}

void UniversalInstantiator::add_to_index_set(qvar qv,
		Term* se)
{
	set<qvar> eq_class;
	get_equivalence_class(qv, eq_class);

	set<qvar>::iterator it = eq_class.begin();
	bool added = false;
	for(; it!=eq_class.end(); it++){
		set<Term*>* val = index_set[*it];
		if(val == NULL){
			val = new set<Term*>();
			index_set[*it] = val;
		}
		unsigned int old_size = val->size();
		val->insert(se);
		if(val->size() > old_size) added = true;
	}

}

bool UniversalInstantiator::process_eq_leaf_in_index_guard(EqLeaf* eq,
		set<int> &qvars, QuantifiedLeaf* ql)
{
	Term* lhs = eq->get_lhs();
	Term* rhs = eq->get_rhs();
	if(lhs->get_term_type() == FUNCTION_TERM ||
			rhs->get_term_type() == FUNCTION_TERM) return false;

	if(lhs->get_term_type() == CONSTANT_TERM && rhs->get_term_type()
			== CONSTANT_TERM) return true;
	if(lhs->get_term_type() != VARIABLE_TERM ||
			qvars.count(((VariableTerm*)lhs)->get_var_id())==0) {
		Term* temp = rhs;
		rhs = lhs;
		lhs = temp;
	}


	assert(lhs->get_term_type() == VARIABLE_TERM);
	VariableTerm* vt = (VariableTerm*) lhs;
	if(qvars.count(vt->get_var_id()) == 0){
		return true;
	}
	qvar qv;
	//qv.orig_id = ql->get_orig_id();
	qv.id = (long int) ql;
	qv.var_id = vt->get_var_id();
	if(rhs->get_term_type() == CONSTANT_TERM){
		add_to_index_set(qv, rhs);
		{
			return true;
		}

	}

	assert(rhs->get_term_type() == VARIABLE_TERM);
	VariableTerm* vt_rhs = (VariableTerm*) rhs;
	if(qvars.count(vt_rhs->get_var_id()) > 0){
		return true;
	}
	add_to_index_set(qv, vt_rhs);
	return true;
}

/*
 * Two universally quantified variables are in the
 * same "equivalence class" if they appear in the same function
 * term and must be instantiated with the same values.
 */
void UniversalInstantiator::get_equivalence_class(qvar qv, set<qvar>& eq_class)
{
	eq_class.insert(qv);
	if(fun_arg_universal.count(qv) == 0) return;
	map<int, int>::iterator it = fun_arg_universal[qv]->begin();
	for(; it!=fun_arg_universal[qv]->end(); it++){
		int key = it->first;
		int val = it->second;
		eq_class.insert(
				reverse_fun_arg_universal[pair<int, int>(key, val)]->begin(),
				reverse_fun_arg_universal[pair<int, int>(key, val)]->end()
				);
	}
}

bool UniversalInstantiator::process_ilp_leaf_in_index_guard(ILPLeaf* ilp,
		set<int> &qvars, QuantifiedLeaf* ql)
{
	int qvar_id = -1;
	int qvar_coef = 1;
	bool seen_non_zero_coef = false;
	bool seen_two_uvars = false;
	long int running_gcd = 0;
	map<Term*, long int> new_elems;

	//ArithmeticTerm* se = new ArithmeticTerm();
	map<Term*, long int >::const_iterator it = ilp->get_elems().begin();
	for(; it!=ilp->get_elems().end(); it++)
	{
		Term* t= it->first;
		int coef = it->second;

		if(t->get_term_type() == FUNCTION_TERM) return false;
		if(t->get_term_type() == CONSTANT_TERM) continue;
		VariableTerm* vt = (VariableTerm*) t;
		int var_id = vt->get_var_id();

		// Universally quantified variable
		if(qvars.count(var_id) > 0){
			if(qvar_id!=-1){
				if(coef == 0) continue;
				// not legal
				if(ilp->get_constant() != 0 ){
					return false;
				}
			}
			else {
				qvar_id = var_id;
				qvar_coef = coef;
				continue;
			}
		}

		// Non-univerally quantified variable
		if(coef != 0) seen_non_zero_coef = true;
		new_elems[vt] = -coef;
		running_gcd = gcd(running_gcd, coef);

	}

	if(seen_two_uvars && seen_non_zero_coef){
		return false;
	}
	if(qvar_id == -1){
		return true;
	}
	if(running_gcd % qvar_coef != 0){
		return false;
	}

	Term* se = NULL;
	if(qvar_coef != 1){
		map<Term*, long int>  new_set;
		map<Term*, long int>::iterator it2 = new_elems.begin();
		for(; it2!=new_elems.end(); it2++){
			new_set[it2->first] = it2->second/qvar_coef;
		}
		se = ArithmeticTerm::make(new_set, ilp->get_constant()/qvar_coef);
	}
	else {
		se = ArithmeticTerm::make(new_elems, ilp->get_constant());
	}
	qvar qv;
	//qv.orig_id = ql->get_orig_id();
	qv.id = (long int) ql;
	qv.var_id = qvar_id;

	add_to_index_set(qv, se);
	return true;
}

bool UniversalInstantiator::build_index_set_index_guard(CNode* c,
		set<int> &qvars, QuantifiedLeaf* ql)
{
	if(c == NULL) return true;
	if(c->is_constant() ) return true;

	if(c->get_type() == EQ)
	{
		EqLeaf* eq = (EqLeaf*) c;
		return process_eq_leaf_in_index_guard(eq, qvars, ql);
	}
	if(c->get_type() == ILP)
	{
		ILPLeaf* ilp = (ILPLeaf*) c;
		return process_ilp_leaf_in_index_guard(ilp, qvars, ql);

	}
	if(c->get_type() == UNIVERSAL) return false;
	assert(c->is_connective());
	Connective* connect = (Connective*) c;
	set<CNode*>::iterator it = connect->get_operands().begin();
	for(; it!=connect->get_operands().end(); it++){
		if(!build_index_set_index_guard(*it, qvars, ql)) return false;
	}
	return true;
}


Term* UniversalInstantiator::instantiate_term(Term* t,
			map<int, Term*> &sub_map)
{
	if(t->get_term_type() == CONSTANT_TERM)
		return t;
	if(t->get_term_type() == VARIABLE_TERM){
		VariableTerm *vt = (VariableTerm*)t;
		if(sub_map.count(vt->get_var_id()) == 0)
			return vt;
		return sub_map[vt->get_var_id()];
	}
	if(t->get_term_type() == ARITHMETIC_TERM) {
		ArithmeticTerm* at = (ArithmeticTerm*)t;
		bool changed = false;
		map<Term*, long int> new_elems;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for(; it!= at->get_elems().end(); it++) {
			Term* new_t = instantiate_term(it->first, sub_map);
			if(new_t != t) changed = true;
			new_elems[new_t] = it->second;
		}
		if(!changed) return at;
		return ArithmeticTerm::make(new_elems, at->get_constant());
	}
	FunctionTerm *ft = (FunctionTerm*)t;
	vector<Term*> new_args;
	for(unsigned int i=0; i < ft->get_args().size(); i++)
	{
		Term* cur = instantiate_term(ft->get_args()[i], sub_map);
		new_args.push_back(cur);
	}
	return FunctionTerm::make(ft->get_id(), new_args, ft->is_invertible());
}


/*
 * Once we've preprocessed and built the index set,
 * we can finally instantiate universals.
 */
CNode* UniversalInstantiator::instantiate_universals(CNode *c,
		map<int, Term*> & sub_map)

{
	if(c->is_constant()) return c;

	if(c->get_type() == EQ)
	{
		EqLeaf* l = (EqLeaf*)c;
		Term* new_rhs = instantiate_term(l->get_rhs(), sub_map);
		Term* new_lhs = instantiate_term(l->get_lhs(), sub_map);
		if(*new_rhs == *l->get_rhs() && *new_lhs == *l->get_lhs())
			return l;
		if(new_rhs->get_term_type() == ARITHMETIC_TERM ||
				new_lhs->get_term_type() == ARITHMETIC_TERM)
		{
			map<Term*, long int> new_elems;
			new_elems[new_rhs] = 1;
			new_elems[new_lhs] = -1;
			return ILPLeaf::make(ILP_EQ, new_elems, 0);
		}

		return EqLeaf::make(new_lhs, new_rhs);
	}
	if(c->get_type() == ILP)
	{
		ILPLeaf* ilp = (ILPLeaf*)c;
		map<Term*, long int >::const_iterator it = ilp->get_elems().begin();
		bool changed = false;
		map<Term*, long int > new_elems;
		for(;it!= ilp->get_elems().end(); it++)
		{
			Term* t = instantiate_term(it->first, sub_map);
			if(t!= it->first)changed = true;
			new_elems[t] = it->second;
		}
		if(!changed) return ilp;
		return ILPLeaf::make(ilp->get_operator(), new_elems, ilp->get_constant());
	}
	if(c->get_type() == UNIVERSAL)
	{

		QuantifiedLeaf* ql = (QuantifiedLeaf*)c;
		set<int> & qvars = ql->get_quantified_vars();
		set<int>::iterator it = qvars.begin();
		set<CNode*> result_set;
		CNode* c_or = Connective::make(OR,
				Connective::make_not(ql->get_index_guard()),
				ql->get_value_guard());
		result_set.insert(c_or);
		for(; it!=qvars.end(); it++)
		{
			int qvar_id = *it;
			qvar qv;

			//qv.orig_id = ql->get_orig_id();
			qv.id = (long int) ql;
			qv.var_id = qvar_id;
			set<Term*>* sub_exps =
					index_set[qv];
			if(sub_exps == NULL){
				sub_exps = new set<Term*>();
				index_set[qv] = sub_exps;
				Term* se = ConstantTerm::make(0);
				sub_exps->insert(se);
			}
			set<Term*>::iterator it2 = sub_exps->begin();
			set<CNode*> new_res;
			for(; it2!=sub_exps->end(); it2++){
				map<int, Term*> cur_sub_map;
				cur_sub_map[qvar_id] = *it2;
				set<CNode*>::iterator it3 = result_set.begin();
				for(; it3 != result_set.end(); it3++)
				{
					CNode* cur = instantiate_universals(*it3, cur_sub_map);
					new_res.insert(cur);
				}
			}
			result_set = new_res;
		}
		CNode* res = Connective::make_and(result_set);
		return res;

	}
	assert(c->is_connective());
	Connective* conn = (Connective*)c;
	set<CNode*> new_operands;


	set<CNode*>::iterator it = conn->get_operands().begin();
	for(;it != conn->get_operands().end(); it++)
	{
		CNode *cur = instantiate_universals(*it, sub_map);
		new_operands.insert(cur);
	}

	return Connective::make(conn->get_type(), new_operands);
}



void UniversalInstantiator::delete_fun_arg_universal()
{
	map<qvar, map<int, int>* >::iterator it = fun_arg_universal.begin();
	for(; it != fun_arg_universal.end(); it++)
	{
		delete it->second;
	}
	fun_arg_universal.clear();

	map<pair<int, int>,set<qvar>* >::iterator it2 =
		reverse_fun_arg_universal.begin();
	for(; it2!= reverse_fun_arg_universal.end(); it2++)
	{
		delete it2->second;
	}
	reverse_fun_arg_universal.clear();
}



void UniversalInstantiator::error()
{
	if(success != NULL) *success = false;
}


UniversalInstantiator::~UniversalInstantiator() {
	delete_fun_arg_universal();
}

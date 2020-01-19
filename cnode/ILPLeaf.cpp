/*
 * ILPLeaf.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include "ILPLeaf.h"
#include "VarMap.h"
#include "EqLeaf.h"
#include "ConstantTerm.h"
#include "ArithmeticTerm.h"
#include "util.h"
#include "Term.h"
#include <assert.h>
#include <iostream>
#include "True.h"
#include "False.h"
#include "Connective.h"
#include "util.h"


#define PRETTY_PRINT true

/*
 * The ILP constructor writes all ILP constraints
 * in terms of LEQ and EQ to allow better simplifications.
 */
ILPLeaf::ILPLeaf(ilp_leaf_type kind, const map<Term*, long int> & _elems,
		long int constant)
{
	node_type = ILP;
	this->constant = constant;
	int factor = 1;

	switch(kind)
	{
	case ILP_EQ:
	case ILP_LEQ:
	{
		this->kind = kind;
		break;
	}
	case ILP_LT:
	{
		this->kind = ILP_LEQ;
		this->constant -= 1;
		break;
	}
	case ILP_GT:
	{
		this->kind = ILP_LEQ;
		this->constant = -constant-1;
		factor = -1;
		break;
	}
	case ILP_GEQ:
	{
		this->kind = ILP_LEQ;
		this->constant = -constant;
		factor = -1;
		break;
	}
	default:
		assert(false);

	}



	map<Term*, long int>::const_iterator it = _elems.begin();
	for(; it!= _elems.end(); it++) {
		Term* t = it->first;
		long int coef = it->second *factor;
		add_term(t, coef);
	}

	it = elems.begin();
	set<Term*> to_delete;
	for(; it!= elems.end(); it++) {
		if(it->second == 0) {
			to_delete.insert(it->first);
		}
	}
	set<Term*>::iterator it2 = to_delete.begin();
	for(; it2 != to_delete.end(); it2++) {
		elems.erase(*it2);
	}


	negations_folded = this;

	compute_hash_code();

}

CNode* ILPLeaf::remove_elem(Term* t)
{
	map<Term*, long int> new_terms = elems;
	new_terms.erase(t);
	return ILPLeaf::make(kind, new_terms, constant);

}

void ILPLeaf::add_term(Term* t, long int coef)
{
	if(coef == 0) return;
	switch(t->get_term_type())
	{
	case CONSTANT_TERM:
	{
		ConstantTerm* ct = (ConstantTerm*) t;
		constant -= (ct->get_constant() * coef);
		break;
	}
	case VARIABLE_TERM:
	case FUNCTION_TERM:
	{
		if(this->elems.count(t) == 0) elems[t] = coef;
		else {
			this->elems[t] += coef;
			if(elems[t] == 0) elems.erase(t);
		}
		break;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) t;
		map<Term*, long int>::const_iterator it =
			at->get_elems().begin();
		for(; it!=at->get_elems().end(); it++) {

			add_term(it->first, it->second*coef);
		}
		constant -= at->get_constant() * coef;
		break;
	}
	default:
		assert(false);
	}
}

void ILPLeaf::compute_hash_code()
{
	map<Term*, long int>::iterator it = elems.begin();
	hash_c = (constant+3)*7;
	for(; it!= elems.end(); it++) {
		hash_c += ((((size_t)it->first<<27) >>27) + it->second)*17;
	}
	if(kind==ILP_EQ) {
		hash_c |= 1<<31;
	}
	else {
		hash_c &= ~(1<<31);
	}

}

CNode* ILPLeaf::make(ilp_leaf_type kind, const map<Term*, long int>& elems,
			long int constant)
{
	return _make(kind, elems, constant, true);
}

CNode* ILPLeaf::make(Term* t1, Term* t2, ilp_leaf_type kind)
{
	map<Term*, long int> elems;
	elems[t1] += 1;
	elems[t2] += -1;
	return make(kind, elems, 0);
}

CNode* ILPLeaf::_make(ilp_leaf_type kind, const map<Term*, long int>& _elems,
			long int constant, bool force_canonical)
{

	ILPLeaf* l = new ILPLeaf(kind, _elems, constant);
	const map<Term*, long int>& elems = l->get_elems();
	kind = l->get_operator();
	constant = l->get_constant();
	assert(kind == ILP_EQ || kind == ILP_LEQ);
	if(l->get_elems().size() == 0) {
		if(l->get_constant() == 0) {
			delete l;
			return True::make();
		}
		delete l;
		if(constant < 0) return False::make();
		if(kind == ILP_EQ) return False::make();
		return True::make();
	}

	// check if this is actually an EqLeaf
	if(kind == ILP_EQ && l->get_elems().size() == 2 && l->get_constant() == 0) {
		map<Term*, long int>::const_iterator it = l->get_elems().begin();
		long int coef1 = it->second;
		Term* t1 = it->first;
		it++;
		long int coef2 = it->second;
		Term* t2 = it->first;
		if((coef1 == 1 && coef2 == -1) || (coef1==-1 && coef2==1)) {
			delete l;
			return EqLeaf::make(t1, t2);
		}
	}
	else if(kind == ILP_EQ && l->get_elems().size() == 1)
	{
		map<Term*, long int>::const_iterator it = l->get_elems().begin();
		long int coef = it->second;
		Term* t = it->first;
		long int constant = l->get_constant();
		if(constant%coef == 0){
			constant/=labs(coef);
			if(coef<0) coef = -1;
			else coef = 1;
		}
		if(coef == 1 || coef == -1)
		{
			delete l;
			if(coef < 0) {
				constant = -constant;
			}
			return EqLeaf::make(t, ConstantTerm::make(constant));
		}
	}

	//check if it has any integer solutions
	if(l->kind == ILP_EQ) {
		assert(l->elems.size()>=1);
		map<Term*, long int>::const_iterator it = elems.begin();
		long int cur_gcd = it->second;
		it++;
		for(; it!= elems.end(); it++) {
			cur_gcd = gcd(cur_gcd, it->second);
		}
		if(l->constant%cur_gcd != 0) {
			delete l;
			return False::make();
		}
	}






	// check if true or false
	if(l->get_elems().size() == 0) {
		if(l->get_constant() == 0){
			delete l;
			return True::make();
		}
		if(l->get_operator() == ILP_EQ) {
			delete l;
			return False::make();
		}
		else {
			if(l->get_constant() >=0) {
				delete l;
				return True::make();
			}
			else {
				delete l;
				return False::make();
			}
		}
	}

	//compute gcd
	long int cur_gcd = constant;
	for(map<Term*, long int>::iterator it = l->elems.begin();
			it != l->elems.end(); it++) {
		cur_gcd = gcd(cur_gcd, it->second);
	}
	if(cur_gcd < 0) cur_gcd = -cur_gcd;
	if(cur_gcd > 1) {
		for(map<Term*, long int>::iterator it = l->elems.begin();
				it != l->elems.end(); it++) {
			it->second/=cur_gcd;
		}
		l->constant/=cur_gcd;
		l->compute_hash_code();

	}

	if(force_canonical && l->get_operator() == ILP_LEQ &&
			l->get_elems().begin()->second < 0)
	{
		CNode* not_l = l->negate(true);
		CNode* node = Connective::make_not(not_l);
		CNode* res = CNode::get_node(node);
		return res;
	}

	return CNode::get_node(l);
}



bool ILPLeaf::operator==(const CNode& __other)
{
	CNode& _other = (CNode&) __other;
	if(_other.get_type()!= ILP) return false;
	ILPLeaf& other = (ILPLeaf&) _other;
	return(kind == other.kind && constant == other.constant &&
			elems == other.elems);
}





string ILPLeaf::pretty_print_ilp(bool neg)
{
	map<string, long int> lhs;
	map<string, long int> rhs;


	map<Term*, long int>::iterator it = elems.begin();
	for(; it!= elems.end(); it++)
	{
		Term* t = it->first;
		long int coef = it->second;
		if(coef < 0) rhs[t->to_string()] = -coef;
		else lhs[t->to_string()] = coef;
	}

	ilp_leaf_type t = kind;
	long int new_constant = constant;
	if(neg)
	{
		if(kind == ILP_LEQ) {
			neg = false;
			t = ILP_GT;
		}

	}

	if(constant == -1) {
		if(t == ILP_GT) {
			t = ILP_GEQ;
			new_constant = 0;
		}
		else if(t == ILP_LEQ) {
			t = ILP_LT;
			new_constant = 0;
		}
	}
	else if(constant == 1) {
		if(t == ILP_GEQ) {
			t = ILP_GT;
			new_constant = 0;
		}
		else if(t == ILP_LT) {
			t = ILP_EQ;
			new_constant = 0;
		}
	}

	bool constant_left = false;
	if(new_constant < 0 && rhs.size()>0) constant_left = true;
	if(new_constant >= 0 && lhs.size() == 0) constant_left = true;

	if(constant_left)
		new_constant*=-1;

	string op= (neg ? "!" : "") + ilp_leaf_type_to_string(t);

	string res;

	map<string, long int>::iterator it2 = lhs.begin();
	bool first = true;
	for(; it2 != lhs.end(); it2++)
	{
		string cur = it2->first;
		long int coef = it2->second;
		if(!first) res+= "+";
		first = false;
		if(coef != 1)
			res+=int_to_string(coef);
		res +=cur;
	}
	if(constant_left) {
		bool print_constant = true;
		if(new_constant > 0 && lhs.size() > 0 ) res += "+";
		if(new_constant == 0 && lhs.size() > 0) print_constant = false;
		if(print_constant) res += int_to_string(new_constant);
 	}

	res += op;

	it2 = rhs.begin();
	first = true;
	for(; it2 != rhs.end(); it2++)
	{
		string cur = it2->first;
		long int coef = it2->second;
		if(!first) res+= "+";
		first = false;
		if(coef != 1)
			res+=int_to_string(coef);
		res +=cur;
	}

	if(!constant_left) {
		bool print_constant = true;
		if(new_constant > 0 && rhs.size() > 0 ) res += "+";
		if(new_constant == 0 && rhs.size() > 0) print_constant = false;
		if(print_constant) res += int_to_string(new_constant);
 	}




	return res;







}


string ILPLeaf::to_string()
{



	if(PRETTY_PRINT)
	{
		return pretty_print_ilp(false);
	}

	string res;
	map<Term*, long int>::iterator it = elems.begin();
	int i=0;
	for(; it!= elems.end(); it++, i++)
	{
		Term* t = it->first;
		long int coef = it->second;
		if(coef != 1) res += int_to_string(coef);
		res += t->to_string();
		if(i!= (int)elems.size() - 1) res += "+";
	}
	res += ilp_leaf_type_to_string(kind);
	res += int_to_string(this->constant);
	return res;

}

string ILPLeaf::ilp_leaf_type_to_string(ilp_leaf_type t)
{
	switch(t)
	{
	case ILP_EQ:
		return "=";
	case ILP_LEQ:
		return "<=";
	case ILP_LT:
		return "<";
	case ILP_GEQ:
		return ">=";
	case ILP_GT:
		return ">";
	default:
		assert(false);
	}
}






ILPLeaf::~ILPLeaf() {

}

CNode* ILPLeaf::negate(bool remove_all_negations)
{

	switch(kind)
	{
		case ILP_EQ:
		{
			Connective* c = new Connective(this);
			return CNode::get_node(c);
		}
		case ILP_LEQ:
		{
			if(!remove_all_negations && elems.begin()->second >= 0)
			{
				Connective* c = new Connective(this);
				return CNode::get_node(c);
			}
			map<Term*, long int> new_elems;
			map<Term*, long int>::iterator it = elems.begin();
			for(; it!= elems.end(); it++)
			{
				new_elems[it->first] = -it->second;
			}
			long int new_constant = -constant-1;
			CNode* res = ILPLeaf::_make(ILP_LEQ, new_elems, new_constant,
					!remove_all_negations);
			return res;

		}
		default:
			assert(false);

	}
}
CNode* ILPLeaf::substitute(map<Term*, Term*>& subs)
{
	map<Term*, long int> new_elems;
	bool changed = false;
	map<Term*, long int> ::const_iterator it = elems.begin();
	for (; it != elems.end(); it++) {
		Term* v = it->first->substitute(subs);
		if(new_elems.count(v) == 0)
				new_elems[v] = it->second;
		else new_elems[v] += it->second;
		if (v != it->first)
			changed = true;

	}
	if (!changed)
		return this;

	CNode* res = ILPLeaf::make(kind, new_elems, constant);
	return res;
}

CNode* ILPLeaf::multiply(long int factor)
{
	if(factor == 1) return this;
	if(factor == 0) {
		return True::make();
	}
	ilp_leaf_type new_kind = kind;
	assert(kind == ILP_EQ || kind == ILP_LEQ);
	if(factor < 0 && kind == ILP_LEQ)
	{
		kind = ILP_GEQ;
	}

	map<Term*, long int> new_elems;
	map<Term*, long int>::const_iterator it = elems.begin();
	for(; it!= elems.end(); it++)
	{
		Term* t = it->first;
		long int coef = it->second;
		new_elems[t] = coef*factor;
	}
	CNode* new_ilp = ILPLeaf::make(new_kind, new_elems, constant*factor);
	return new_ilp;

}

long ILPLeaf::get_coefficient(Term* t)
{
	assert(elems.count(t) > 0);
	return elems[t];
}
bool ILPLeaf::contains_elem(Term* t)
{
	return (elems.count(t) > 0);
}

CNode* ILPLeaf::add(ILPLeaf* other)
{
	assert(kind == other->kind);
	map<Term*, long int> new_elems;
	new_elems = elems;
	map<Term*, long int>::const_iterator it = other->elems.begin();
	for(; it!=other->elems.end(); it++)
	{
		Term* t = it->first;
		long int coef = it->second;
		if(new_elems.count(t) > 0) {
			new_elems[t]+= coef;
		}
		else new_elems[t] = coef;
	}
	long int new_constant = constant + other->constant;
	CNode* res = ILPLeaf::make(kind, new_elems, new_constant);
	return res;

}

CNode* ILPLeaf::divide(long int c, Term* desired_term)
{
	map<Term*, long int> new_elems;
	map<Term*, long int>::const_iterator it = elems.begin();
	bool changed = false;
	for(; it!= elems.end(); it++)
	{
		Term* t = it->first;
		long int coef = it->second;
		if(t == desired_term) {
			coef/=c;
			changed = true;
		}
		new_elems[t] = coef;
	}
	if(!changed) return this;
	CNode* new_ilp = ILPLeaf::make(kind, new_elems, constant);
	return new_ilp;
}

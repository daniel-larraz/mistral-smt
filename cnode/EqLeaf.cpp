/*
 * EqLeaf.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include "EqLeaf.h"
#include "Term.h"
#include <iostream>
#include "util.h"
#include "ConstantTerm.h"
#include <assert.h>
#include "True.h"
#include "False.h"
#include "ILPLeaf.h"
#include "VariableTerm.h"


CNode* EqLeaf::make(Term* lhs, Term* rhs)
{
	if(lhs == rhs){
		return True::make();
	}

	term_type lhs_t= lhs->get_term_type();
	term_type rhs_t = rhs->get_term_type();

	if(lhs_t == CONSTANT_TERM && rhs_t == CONSTANT_TERM)
	{
		// they can't be the same, otherwise their addresses would be same
		return False::make();
	}

	if(lhs_t == CONSTANT_TERM) {
		Term* t = lhs;
		lhs = rhs;
		rhs = t;
	}

	lhs_t = lhs->get_term_type();
	rhs_t = rhs->get_term_type();


	if(lhs_t == ARITHMETIC_TERM ||
			rhs_t == ARITHMETIC_TERM)
	{
		map<Term*, long int> elems;
		elems[lhs] =1;
		elems[rhs] = -1;
		return ILPLeaf::make(ILP_EQ, elems, 0);
	}

	EqLeaf* eq = new EqLeaf(lhs, rhs);
	return CNode::get_node(eq);
}

EqLeaf::EqLeaf(Term* lhs, Term* rhs) {
	node_type = EQ;
	/*
	 * EqLeaves should not contain arithmetic terms -- should make
	 * ILPLeaf instead.
	 */
	assert(lhs->get_term_type() != ARITHMETIC_TERM);
	assert(rhs->get_term_type() != ARITHMETIC_TERM);


	// This is to ensure a canonical ordering of lhs and rhs's
	if(lhs< rhs)
	{
		this->lhs = lhs;
		this->rhs = rhs;
	}
	else
	{
		this->lhs = rhs;
		this->rhs = lhs;
	}
	negations_folded = this;
	compute_hash_code();

}

void EqLeaf::compute_hash_code()
{
	hash_c = ((size_t) lhs)*7 + ((size_t) rhs)*13;
}


bool EqLeaf::operator==(const CNode& __other)
{
	CNode& _other = (CNode&) __other;
	if(_other.get_type() != EQ) return false;
	EqLeaf& other = (EqLeaf&) _other;
	return (lhs==other.lhs && rhs == other.rhs);
}



string EqLeaf::to_string()
{
	string res;
	if(rhs->get_term_type() == VARIABLE_TERM){
		res += rhs->to_string();
		res += " = ";
		res += lhs->to_string();
		return res;
	}

	res += lhs->to_string();
	res += " = ";
	res += rhs->to_string();
	return res;
}


Term* EqLeaf::get_lhs()
{
	return lhs;
}
Term* EqLeaf::get_rhs()
{
	return rhs;
}


CNode* EqLeaf::substitute(map<Term*, Term*>& subs)
{
	Term* new_lhs = lhs->substitute(subs);
	Term* new_rhs = rhs->substitute(subs);
	if(new_lhs == lhs && new_rhs == rhs) return this;
	CNode* res = make(new_lhs, new_rhs);
	return res;
}


EqLeaf::~EqLeaf() {
}

/*
 * Connective.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include "Connective.h"
#include <assert.h>
#include "Leaf.h"
#include "util.h"
#include "True.h"
#include "False.h"
#include "ILPLeaf.h"
#include "EqLeaf.h"
#include "QuantifiedLeaf.h"

#define PRETTY_PRINT true


Connective::Connective(cnode_type connective_type, const set<CNode*>& ops) {
	assert(connective_type != IMPLIES);
	this->node_type = connective_type;
	operands = ops;
	negations_folded = this;
	compute_hash_code();
	size = -1;
}

Connective::Connective(CNode* op)
{
	this->node_type = NOT;
	operands.insert(op);
	negations_folded = this;
	compute_hash_code();
	size = -1;
}

void Connective::compute_hash_code()
{
	set<CNode*>::iterator it = operands.begin();
	hash_c = 0;
	for(; it!= operands.end(); it++) {
		hash_c += (((size_t)*it<<27) >>27)*13;
	}
	if(node_type==AND) {
		hash_c |= 1<<31;
	}
	else if(node_type==NOT){
		hash_c &= ~(1<<31);
		hash_c |= 1 << 30;
	}
	else {
		hash_c |= 1<<31;
		hash_c |= 1 <<30;
	}

}

bool Connective::operator==(const CNode& _other)
{
	if(!_other.is_connective()) return false;
	Connective& other = (Connective&) _other;
	if(other.node_type != node_type) return false;
	return other.operands == operands;
}




string Connective::to_string()
{
	string res;
	if(!PRETTY_PRINT && node_type == NOT) res += "!";
	if(PRETTY_PRINT && node_type == NOT)
	{
		CNode* inner = *operands.begin();
		if(inner->get_type() != ILP) res +="!";
		else
		{
			ILPLeaf* ilp = (ILPLeaf*) inner;
			return ilp->pretty_print_ilp(true);
		}
	}
	if(operands.size() >1) res += "(";
	set<CNode*>::iterator it = operands.begin();
	unsigned int i=0;
	for(; it != operands.end(); it++, i++)
	{
		CNode* arg = *it;
		res += arg->to_string();
		if(i!=operands.size()-1) res += connective_to_string() + " ";
	}
	if(operands.size() >1) res += ")";

	return res;
}

// p=> a
CNode* Connective::make_implies(CNode* p, CNode* a)
{
	CNode* not_node = make_not(p);
	return make(OR, not_node, a);
}




CNode* Connective::_make_and(const set<CNode*>& ops, bool simplify)
{
	if(!simplify)
	{
		Connective* c = new Connective(AND, ops);
		return CNode::get_node(c);
	}

	set<CNode*> new_ops;
	set<CNode*>::const_iterator it = ops.begin();
	for(; it!= ops.end(); it++)
	{
		CNode* cur = *it;
		if(cur->get_type() == TRUE_NODE) continue;
		if(cur->get_type() == FALSE_NODE) return False::make();
		if(cur->get_type() == AND) {
			Connective* child = (Connective*) cur;
			new_ops.insert(child->get_operands().begin(),
							child->get_operands().end());
			continue;
		}
		new_ops.insert(cur);
	}
	if(new_ops.size() == 0) {
		return True::make();
	}
	if(new_ops.size() == 1) {
		return *new_ops.begin();
	}

	/*
	 * Check if we have children that are negations of one another,
	 * this is not automatically detected because things are in NNF, e.g.,
	 * (a | b) & !(a | b) is (a |b) & !a & !b
	 */
	it = new_ops.begin();
	for(; it!= new_ops.end(); it++)
	{
		CNode* cur = *it;
		CNode* not_cur = Connective::make_not(cur);
		if(not_cur->get_type() == AND)
		{
			Connective* and_c = (Connective*) not_cur;
			bool all_present = true;
			set<CNode*>::iterator it = and_c->get_operands().begin();
			for(; it != and_c->get_operands().end(); it++)
			{
				if(new_ops.count(*it) == 0){
					all_present = false;
					break;
				}

			}
			if(all_present) return False::make();

		}
		else if(new_ops.count(not_cur) > 0) {
			return False::make();
		}
	}


	Connective* c = new Connective(AND, new_ops);
	return CNode::get_node(c);

}
CNode* Connective::make_or(const set<CNode*>& ops, bool simplify)
{
	if(!simplify)
	{
		Connective* c = new Connective(OR, ops);
		return CNode::get_node(c);
	}
	set<CNode*> new_ops;
	set<CNode*>::const_iterator it = ops.begin();
	bool sat = false;
	for(; it!= ops.end(); it++)
	{
		CNode* cur = *it;
		if(cur->get_type() == FALSE_NODE) continue;
		if(cur->get_type() == TRUE_NODE) return True::make();
		if(cur->get_simplification(UNSAT_SIMPLIFY)!=NULL) sat = true;
		if(cur->get_type() == OR) {
			Connective* child = (Connective*) cur;
			new_ops.insert(child->get_operands().begin(),
							child->get_operands().end());
			continue;
		}
		new_ops.insert(cur);
	}

	if(new_ops.size() == 0) {
		return False::make();
	}
	if(new_ops.size() == 1) {
		return *new_ops.begin();
	}
	it = new_ops.begin();
	for(; it!= new_ops.end(); it++)
	{
		CNode* cur = *it;
		CNode* not_cur = Connective::make_not(cur);
		if(not_cur->get_type() == OR)
		{
			Connective* or_c = (Connective*) not_cur;
			bool all_present = true;
			set<CNode*>::iterator it = or_c->get_operands().begin();
			for(; it != or_c->get_operands().end(); it++)
			{
				if(new_ops.count(*it) == 0) {
					all_present = false;
					break;
				}

			}
			if(all_present) return True::make();

		}
		else if(new_ops.count(not_cur) > 0) {
			return True::make();
		}

	}


	Connective* c = new Connective(OR, new_ops);
	CNode* res = CNode::get_node(c);
	if(sat) res->set_simplification(res, UNSAT_SIMPLIFY);
	return res;



}
CNode* Connective::make_not(CNode* op)
{
	if(op->negation != NULL){
		return op->negation;
	}
	CNode* res;
	switch(op->get_type())
	{
	case TRUE_NODE:
	{
		res =  False::make();
		break;
	}
	case FALSE_NODE:
	{
		res = True::make();
		break;
	}
	case EQ:
	case UNIVERSAL:
	case MOD:
	case BOOLEAN_VAR:
	{
		Connective* c = new Connective(op);
		res = CNode::get_node(c);
		break;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) op;
		res = ilp->negate();
		if(res->get_type() == NOT)
		{
			res->negations_folded = ilp->negate(true);
		}
		break;
	}
	case NOT:
	{
		Connective* inner = (Connective*) op;
		res= *inner->get_operands().begin();
		break;
	}
	case AND:
	case OR:
	{
		Connective* con  = (Connective*) op;
		set<CNode*> negated_ops;
		set<CNode*>::const_iterator it = con->get_operands().begin();
		for(; it!= con->get_operands().end(); it++)
		{
			negated_ops.insert(make_not(*it));
		}
		if(con->get_type() == AND){
			res= Connective::make_or(negated_ops);
		}
		else {
			res = Connective::make_and(negated_ops);
		}
		break;
	}
	default:
		assert(false);

	}
	op->negation = res;
	//res->negation =  op->make_canonical();
	return res;

}



CNode* Connective::make(cnode_type connective_type, const set<CNode*>& ops)
{
	switch(connective_type)
	{
	case AND:
		return make_and(ops);
	case OR:
		return make_or(ops);
	case NOT:
		assert(ops.size() == 1);
		return make_not(*ops.begin());
	default:
		assert(false);
	}


}
CNode* Connective::make(cnode_type connective_type, CNode* op1, CNode* op2)
{
	assert(connective_type == AND || connective_type == OR);
	set<CNode*> ops;
	ops.insert(op1);
	ops.insert(op2);
	return make(connective_type, ops);
}

const set<CNode*>& Connective::get_operands()
{
	return operands;
}



string Connective::connective_to_string()
{
	switch(this->node_type)
	{
	case AND:
		return "&";
	case OR:
		return "|";
	case NOT:
		return "!";
	default:
		assert(false);
	}
}

Connective::~Connective()
{

}

CNode* Connective::substitute(map<Term*, Term*>& subs)
{
	bool changed;
	set<CNode*> new_ops;
	set<CNode*>::const_iterator it = operands.begin();
	for (; it != operands.end(); it++) {
		CNode* new_arg = (*it)->substitute(subs);
		new_ops.insert(new_arg);
		if(new_arg != *it) changed = true;
	}
	if(!changed) return this;
	return make(node_type, new_ops);
}



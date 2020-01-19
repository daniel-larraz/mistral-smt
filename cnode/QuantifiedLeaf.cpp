/*
 * QuantifiedLeaf.cpp
 *
 *  Created on: Sep 12, 2008
 *      Author: isil
 */

#include "QuantifiedLeaf.h"
#include "VarMap.h"
#include "util.h"
#include "assert.h"
#include "True.h"
#include "False.h"

QuantifiedLeaf::QuantifiedLeaf(set<int>& quantified_vars, CNode* index_guard,
		CNode* value_guard)
{
	node_type = UNIVERSAL;
	this->quantified_vars = quantified_vars;
	this->index_guard = index_guard;
	this->value_guard = value_guard;
	negations_folded = this;
	hash_c = index_guard->hash_code()*47 + value_guard->hash_code()*7;

}

CNode* QuantifiedLeaf::make(set<int>& quantified_vars, CNode* index_guard,
		CNode* value_guard)
{
	if(index_guard->get_type() == FALSE_NODE) return True::make();
	if(value_guard->get_type() == TRUE_NODE) return True::make();
	if(index_guard->get_type() == TRUE_NODE && value_guard->get_type() == FALSE_NODE)
		return False::make();
	QuantifiedLeaf* ql = new QuantifiedLeaf(quantified_vars, index_guard,
			value_guard);
	return CNode::get_node(ql);
}





set<int>& QuantifiedLeaf::get_quantified_vars()
{
	return quantified_vars;
}
CNode* QuantifiedLeaf::get_index_guard()
{
	return index_guard;
}
CNode* QuantifiedLeaf::get_value_guard()
{
	return value_guard;
}

bool QuantifiedLeaf::operator==(const CNode& _other)
{
	if(((QuantifiedLeaf&)_other).get_type()!=UNIVERSAL) return false;
	QuantifiedLeaf& other = (QuantifiedLeaf&) _other;
	return(quantified_vars == other.quantified_vars &&
			index_guard == other.index_guard &&
			value_guard == other.value_guard);
}
string QuantifiedLeaf::to_string()
{
	string res = "A";
	set<int>::iterator it = this->quantified_vars.begin();
	unsigned int i =0;
	for(;it != quantified_vars.end(); it++, i++)
	{
		res+=vm.get_name(*it);
		if(i!=quantified_vars.size()-1) res+=", ";
	}
	res+=".(";
	res+=(index_guard == NULL ? " ": index_guard->to_string());
	res+="->";
	res+=(value_guard == NULL ? " ": value_guard->to_string());
	res+=")";
	return res;
}




QuantifiedLeaf::~QuantifiedLeaf() {

}

CNode* QuantifiedLeaf::substitute(map<Term*, Term*>& subs)
{

	CNode* new_index = index_guard->substitute(subs);
	CNode* new_val = value_guard->substitute(subs);

	if (index_guard == new_index && new_val == value_guard)
		return this;
	return make(quantified_vars, new_index, new_val);

}

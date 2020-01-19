/*
 * BooleanVar.cpp
 *
 *  Created on: Jul 25, 2009
 *      Author: tdillig
 */

#include "BooleanVar.h"
#include "util.h"
#include "cnode.h"
#include "term.h"

unsigned int BooleanVar::next_id = 0;
map<unsigned int, string> BooleanVar::names;
map<string, unsigned int> BooleanVar::names_rev;
void BooleanVar::clear()
{
	next_id = 0;
	names.clear();
	names_rev.clear();
}

BooleanVar::BooleanVar() {
	id = next_id++;
	this->node_type = BOOLEAN_VAR;
	this->hash_c = 30673 + 7*id;
	this->negations_folded = this;

}

BooleanVar::BooleanVar(const string & name)
{

	if(names_rev.count(name) > 0)
		id = names_rev[name];
	else
	{
		id = next_id++;
		names[id] = name;
		names_rev[name] = id;
	}
	this->node_type = BOOLEAN_VAR;
	this->hash_c = 30673 + 7*id;
	this->negations_folded = this;

}

BooleanVar* BooleanVar::make()
{
	BooleanVar* bv = new BooleanVar();
	return (BooleanVar*) CNode::get_node(bv);
}

BooleanVar* BooleanVar::make(const string & name)
{
	BooleanVar* bv = new BooleanVar(name);
	return (BooleanVar*) CNode::get_node(bv);
}

unsigned int BooleanVar::get_id() const
{
	return id;
}
bool BooleanVar::operator==(const CNode& other)
{
	if(other.get_type() != BOOLEAN_VAR) return false;
	BooleanVar& other_bv = (BooleanVar&) other;
	return other_bv.id == id;
}
string BooleanVar::to_string()
{
	if(names.count(id) == 0) return "p" + int_to_string(id);
	return names[id];
}

string BooleanVar::get_name()
{
	if(names.count(id) == 0) return "p" + int_to_string(id);
	return names[id];
}

CNode* BooleanVar::substitute(map<Term*, Term*>& subs)
{
	return this;
}

EqLeaf* BooleanVar::to_eqleaf() const
{
	Term* ct = ConstantTerm::make(1);
	Term* var = VariableTerm::make("bool`" + int_to_string(id) );
	EqLeaf* eq = (EqLeaf*) EqLeaf::make(var, ct);
	return eq;
}

BooleanVar::~BooleanVar() {}

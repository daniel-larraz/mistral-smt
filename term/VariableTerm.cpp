/*
 * VariableTerm.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include "VariableTerm.h"
#include "ArithmeticTerm.h"
#include "ConstantTerm.h"
#include "util.h"



#ifndef COMPASS
Term* VariableTerm::make(int id)
{
	VariableTerm* vt = new VariableTerm(id);
	return Term::get_term(vt);
}

Term* VariableTerm::make(string name)
{
	return make(CNode::get_varmap().get_id(name));
}
#endif

#ifdef COMPASS
#include "Variable.h"

Term* VariableTerm::make(int id)
{
	Term* t = _make_ap(CNode::get_varmap().get_name(id));
	return Term::get_term(t);
}

Term* VariableTerm::make(string name)
{
	Term* t = _make_ap(name);
	return Term::get_term(t);
}
#endif

VariableTerm::VariableTerm(int var_id, int attribute) {
	this->var_id = var_id | attribute;
	this->type = VARIABLE_TERM;
	hash_c = (this->var_id+2)* 65537;

}

bool VariableTerm::operator==(const Term& __other)
{
	Term& _other = (Term&) __other;
	if(_other.get_term_type() != VARIABLE_TERM)
		return false;
	VariableTerm& other = (VariableTerm&) _other;
	return var_id == other.var_id;
}

string VariableTerm::to_string()
{
	string res = CNode::get_varmap().get_name(var_id);
	return res;
}

Term* VariableTerm::substitute(map<Term*, Term*>& subs)
{
	if(subs.count(this) !=0 ) return subs[this];
	return this;
}


string VariableTerm::get_name()
{
	return CNode::get_varmap().get_name(var_id);
}

VariableTerm::~VariableTerm()
{

}

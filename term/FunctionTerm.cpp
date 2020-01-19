/*
 * FunctionTerm.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include "FunctionTerm.h"
#include "util.h"
#include "ArithmeticTerm.h"

#define INVERTIBLE_FN_TOKEN "#"

#ifndef COMPASS

Term* FunctionTerm::make(int id, vector<Term*>& args, bool invertible)
{
	FunctionTerm* ft = new FunctionTerm(id, args, invertible);
	return Term::get_term(ft);
}

Term* FunctionTerm::make(string name, vector<Term*>& args, bool invertible)
{
	int id = CNode::get_varmap().get_id(name, invertible);
	FunctionTerm* ft = new FunctionTerm(id, args, invertible);
	return Term::get_term(ft);
}
#endif

#ifdef COMPASS
#include "ArithmeticValue.h"

Term* FunctionTerm::make(int id, vector<Term*>& args, bool invertible)
{

	Term* t = _make_ap(CNode::get_varmap().get_name(id), args, invertible);
	return Term::get_term(t);
}

Term* FunctionTerm::make(string name, vector<Term*>& args, bool invertible)
{

	Term* t = _make_ap(name, args, invertible);
	return Term::get_term(t);
}
#endif

FunctionTerm::FunctionTerm(int id, const vector<Term*>& args, bool invertible,
		int attribute) {
	this->fun_id = id | attribute;
	this->args = args;
	this->type = FUNCTION_TERM;
	this->invertible = invertible;
	compute_hash_code();
}

FunctionTerm::FunctionTerm(int id, Term* arg, bool invertible, int attribute)
{
	this->fun_id = id | attribute;
	this->args.push_back(arg);
	this->type = FUNCTION_TERM;
	this->invertible = invertible;
	compute_hash_code();
}

FunctionTerm::FunctionTerm(int id, Term* arg1, Term* arg2, bool invertible,
		int attribute)
{
	this->fun_id = id | attribute;
	this->args.push_back(arg1);
	this->args.push_back(arg2);
	this->type = FUNCTION_TERM;
	this->invertible = invertible;
	compute_hash_code();

}

void FunctionTerm::compute_hash_code()
{
	hash_c = 0;
	for(unsigned int i=0; i<args.size(); i++)
	{
		Term * cur = args[i];
		hash_c*=21;
		hash_c+=(((size_t)cur<<26) >>26);
	}
	hash_c*=(fun_id+1);
	if(invertible) hash_c+=1;
}



bool FunctionTerm::operator==(const Term& __other)
{


	Term& _other = (Term&) __other;

	if(_other.get_term_type() != FUNCTION_TERM){
		return false;
	}
	FunctionTerm& other = (FunctionTerm&) _other;
	bool res = (this->fun_id == other.fun_id && args == other.args &&
			invertible == other.invertible);

	return res;
}

string FunctionTerm::to_string()
{

	int attrib = this->get_id_attribute();
	char begin = 'A';
	begin+=attrib;


	string fun_name;
	if(attrib != 0) fun_name+= begin;
	fun_name += CNode::get_varmap().get_name(fun_id);
	if(invertible) fun_name += INVERTIBLE_FN_TOKEN;
	string res = fun_name +  "(";
	for(unsigned int i=0; i<args.size(); i++){
		res += args[i]->to_string();
		//res += int_to_string((long int) args[i]);
		if(i!=args.size()-1) res += ", ";
	}
	res += ")";
	//res += int_to_string((long int)this);
	//res += " hc: " + int_to_string(hash_c);
	//res += " fun id: " + int_to_string(fun_id);
	return res;
}




string FunctionTerm::get_name()
{
	return CNode::get_varmap().get_name(fun_id);
}



Term* FunctionTerm::substitute(map<Term*, Term*>& subs)
{


	if(subs.count(this) > 0) return subs[this];
	bool changed = false;
	vector<Term*> new_args;
	for (unsigned int i = 0; i < args.size(); i++) {
		Term * ot = args[i];
		Term * nt = ot->substitute(subs);
		if (ot != nt)
			changed = true;
		new_args.push_back(nt);
	}
	if (!changed)
		return this;
	Term* res=  FunctionTerm::make(fun_id, new_args, invertible);
	return res;

}


FunctionTerm::~FunctionTerm() {

}

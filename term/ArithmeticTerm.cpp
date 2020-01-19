/*
 * ArithmeticTerm.cpp
 *
 *  Created on: Oct 5, 2008
 *      Author: isil
 */

#include "ArithmeticTerm.h"
#include "VariableTerm.h"
#include "FunctionTerm.h"
#include "util.h"
#include "ConstantTerm.h"
#include <iostream>
#include "assert.h"

ArithmeticTerm* ArithmeticTerm::_make(const map<Term*, long int>& elems, long int constant)
{


	ArithmeticTerm* at = new ArithmeticTerm(elems, constant);
	return at;

}

ArithmeticTerm::ArithmeticTerm(const map<Term*, long int>& elems,
		long int constant)
{
	this->type = ARITHMETIC_TERM;
	this->constant = constant;
	this->elem_gcd = -1;
	map<Term*, long int>::const_iterator it = elems.begin();
	for(; it!= elems.end(); it++)
	{
		add_elem(it->first, it->second);
	}

	compute_hash_code();
}


/*
 * c1*t1 + c2*t2
 */
ArithmeticTerm::ArithmeticTerm(Term* t1, long int c1, Term* t2, long int c2)
{
	this->type = ARITHMETIC_TERM;
	this->constant = 0;
	this->elem_gcd = -1;
	add_elem(t1, c1);
	add_elem(t2, c2);
	compute_hash_code();
}

/*
 * t * c
 */
ArithmeticTerm::ArithmeticTerm(Term* t, long int c)
{
	this->type = ARITHMETIC_TERM;
	this->constant = 0;
	this->elem_gcd = -1;
	add_elem(t, c);
	compute_hash_code();
}

Term* ArithmeticTerm::canonicalize(ArithmeticTerm* at)
{
	if(at->get_elems().size() == 0) {
		long int constant = at->get_constant();
		delete at;
		return ConstantTerm::make(constant);
	}
	if(at->get_constant() == 0 && at->get_elems().size() == 1 &&
			(at->get_elems().begin())->second ==1)
	{
		Term* t = at->get_elems().begin()->first;
		switch(t->get_term_type())
		{
		case VARIABLE_TERM:
		case FUNCTION_TERM:
		{
			delete at;
			return t;
		}
		default:
			assert(false);
		}
	}

	return Term::get_term(at);
}


long int ArithmeticTerm::get_gcd(bool include_constant)
{
	if(!include_constant && elem_gcd != -1){
		return elem_gcd;
	}
	if(include_constant && elem_gcd != -1) return gcd(elem_gcd, constant);

	elem_gcd = 0;
	assert(elems.size() > 0);
	map<Term*, long int>::const_iterator it  = elems.begin();
	for(; it!= elems.end(); it++) {
		int c = it->second;
		elem_gcd = gcd(c, elem_gcd);
	}
	if(!include_constant) return elem_gcd;
	return gcd(elem_gcd, constant);

}

void ArithmeticTerm::add_elem(Term* t, long int coef)
{

	if(coef == 0) return;
	switch(t->get_term_type())
	{
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) t;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for(; it!= at->get_elems().end(); it++) {
			add_elem(it->first, coef*it->second);
		}
		constant += coef*at->get_constant();
		break;
	}
	case CONSTANT_TERM:
	{
		ConstantTerm* ct = (ConstantTerm*) t;
		constant += coef*ct->get_constant();
		break;
	}
	case VARIABLE_TERM:
	case FUNCTION_TERM:
	{
		if(elems.count(t) == 0) {
			elems[t] = coef;
		}
		else {
			elems[t] += coef;
			if(elems[t] == 0) {
				elems.erase(t);
			}
		}
		break;
	}
	default: {
		cerr << "Unexpected term: " << t->get_term_type() << endl;
		//cerr << t->to_string() << endl;
		assert(false);
	}

	}
}

void ArithmeticTerm::compute_hash_code()
{
	map<Term*, long int>::iterator it = elems.begin();
	hash_c = constant;
	for(; it!= elems.end(); it++) {
		hash_c += ((((size_t)it->first<<27) >>27) + it->second)*13;
	}
}




bool ArithmeticTerm::operator==(const Term& __other)
{
	Term& _other = (Term&) __other;
	if(_other.get_term_type() != ARITHMETIC_TERM) return false;
	ArithmeticTerm& at = (ArithmeticTerm&) _other;
	return constant == at.constant && elems == at.elems;

}
string ArithmeticTerm::to_string()
{
	string res = "";
	map<Term*, long int>::iterator it = elems.begin();
	unsigned int i;
	for(i=0; it!= elems.end(); it++, i++)
	{
		Term* t = it->first;
		int c = it->second;
		if(i != 0 && c>=0) res += "+";
		if(c!= 1 && c!= -1) res += int_to_string(c);
		if(c == -1) res += "-";
		res += t->to_string();
	}
	if(constant != 0){
		if(constant > 0) res += "+";
		res += int_to_string(constant);
	}
	return res;
}

Term* ArithmeticTerm::get_base()
{
	return ArithmeticTerm::make(elems, 0);
}

ArithmeticTerm::~ArithmeticTerm()
{
}

Term* ArithmeticTerm::substitute(map<Term*, Term*>& subs)
{


	if(subs.count(this) > 0) return subs[this];
	bool changed = false;
	map<Term*, long int> new_elems;
	map<Term*, long int>::const_iterator it = elems.begin();
	for (; it != elems.end(); it++) {
		Term* nt = it->first->substitute(subs);
		if (nt != it->first)
			changed = true;
		new_elems[nt] += it->second;
	}
	if (!changed)
		return this;


	Term* res = make(new_elems, constant);

	return res;

}

bool ArithmeticTerm::has_only_negative_coefficients()
{
	map<Term*, long int>::const_iterator it = elems.begin();
	for(; it!= elems.end(); it++) {
		if(it->second > 0) return false;
	}
	return true;
}

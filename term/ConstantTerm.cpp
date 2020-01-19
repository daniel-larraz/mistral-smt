/*
 * ConstantTerm.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include "ConstantTerm.h"
#include "util.h"



#ifdef COMPASS
#include "ConstantValue.h"
#endif




Term* ConstantTerm::_make_term(long int c)
{
	ConstantTerm* ct;
	ct = new ConstantTerm(c);
	return Term::get_term(ct);
}

ConstantTerm::ConstantTerm(long int c) {
	this->c = c;
	this->type = CONSTANT_TERM;
	hash_c = c*47;

}

string ConstantTerm::to_string()
{
	string res = int_to_string(c);
	return res;
}
bool ConstantTerm::operator==(const Term& _other)
{
	Term& other = (Term&) _other;
	if(other.get_term_type()!=CONSTANT_TERM) return false;
	ConstantTerm& ct = (ConstantTerm&) other;
	return c == ct.get_constant();
}


Term* ConstantTerm::substitute(map<Term*, Term*>& subs)
{
	if(subs.count(this) > 0) return subs[this];
	return this;
}

ConstantTerm::~ConstantTerm() {

}

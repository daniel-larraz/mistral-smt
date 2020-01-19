/*
 * Term.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include "Term.h"
#include "FunctionTerm.h"
#include "VariableTerm.h"
#include "ConstantTerm.h"
#include "ArithmeticTerm.h"
#include <algorithm>
#include <assert.h>
#include "Constraint.h"
#include "ILPLeaf.h"

unordered_set<Term*, hash<Term*>, term_eq> Term::terms;
set<Term*> Term::to_delete;


#define DEBUG_TERM_UNIQUIFY false

static set<string> term_strings;

Term* Term::get_term(Term* t)
{
	if(t->get_term_type() == FUNCTION_TERM) {
		FunctionTerm* ft = (FunctionTerm*) t;
	}

	unordered_set<Term*, hash<Term*>, term_eq>::iterator it = terms.find(t);
	if(it == terms.end()){

		if(DEBUG_TERM_UNIQUIFY && t!= NULL) {
			if(term_strings.count(t->to_string()) > 0) {
				cout << " Fount term in term_strings, but not in term: " <<
						t->to_string() << endl;
				cout << "Hash code of term inserted: " << t->hash_c << endl;
				unordered_set<Term*, hash<Term*>, term_eq>::iterator it = terms.begin();
				for(; it!= terms.end(); it++) {
					Term* cur_t = *it;
					if(cur_t->to_string() == t->to_string()) {
						cout << "Hash code of existing term: " << cur_t->hash_c << endl;
						cout << "Result of ==: " << ((*cur_t == *t) ? " equal " :
								" not equal ") << endl;
					}
				}

				assert(false);

			}
			term_strings.insert(t->to_string());
		}

		terms.insert(t);
		//register_children(t);
		return t;
	}
	if(*it!=t){
		 delete t;
	}
	return *it;
}

Term* Term::get_term_nodelete(Term* t)
{


	unordered_set<Term*, hash<Term*>, term_eq>::iterator it = terms.find(t);
	if(it == terms.end()){


		if(DEBUG_TERM_UNIQUIFY && t!= NULL) {
			if(term_strings.count(t->to_string()) > 0) {
				cout << " Fount term in term_strings, but not in term: " <<
						t->to_string() << endl;
				cout << "Hash code of term inserted: " << t->hash_c << endl;
				unordered_set<Term*, hash<Term*>, term_eq>::iterator it = terms.begin();
				for(; it!= terms.end(); it++) {
					Term* cur_t = *it;
					if(cur_t->to_string() == t->to_string()) {
						cout << "Hash code of existing term: " << cur_t->hash_c << endl;
						cout << "Result of ==: " << ((*cur_t == *t) ? " equal " :
								" not equal ") << endl;
					}
				}

				assert(false);

			}
			term_strings.insert(t->to_string());
		}
		terms.insert(t);
		//register_children(t);
		return t;
	}
	if(*it!=t){
		 to_delete.insert(t);
	}
	return *it;
}

void Term::delete_loaded_terms()
{
	set<Term*>::iterator it = to_delete.begin();
	for(; it!= to_delete.end(); it++) {
		delete *it;
	}
	to_delete.clear();
}

void Term::clear()
{
	vector<Term*> t1;
	unordered_set<Term*, hash<Term*>, term_eq>::iterator it2 = terms.begin();
	for(; it2!=terms.end(); it2++){
		t1.push_back((*it2));
	}
	for(unsigned int i=0; i<t1.size(); i++)
	{
		delete t1[i];
	}
	terms.clear();
//	parent_terms.clear();
}

void Term::clear_representatives()
{
	this->representative = NULL;
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
	case VARIABLE_TERM:
		return;
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*) this;
		const vector<Term*>& args = ft->get_args();
		for(unsigned int i=0; i< args.size(); i++) {
			Term* t = args[i];
			t->clear_representatives();
		}
		return;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			t->clear_representatives();
		}
		return;
	}
	default:
		assert(false);
	}
}


void Term::get_nested_vars(set<int>& vars)
{
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
	{
		return;
	}
	case VARIABLE_TERM:
	{
		VariableTerm* vt = (VariableTerm*) this;
		vars.insert(vt->get_var_id());
		return;
	}
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*) this;
		const vector<Term*>& args = ft->get_args();
		for(unsigned int i=0; i< args.size(); i++) {
			Term* t = args[i];
			t->get_nested_vars(vars);
		}
		return;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			t->get_nested_vars(vars);
		}
		return;
	}
	default:
		assert(false);
	}
}

/*
 * Does this term contains any nested variable terms?
 */
bool Term::contains_var()
{
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
		return false;
	case VARIABLE_TERM:
		return true;
	case FUNCTION_TERM: {
		FunctionTerm* ft = (FunctionTerm*) this;
		const vector<Term*>& args = ft->get_args();
		for(unsigned int i=0; i< args.size(); i++) {
			if(args[i]->contains_var()) return true;
		}
		return false;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			if(it->first->contains_var()) return true;
		}
		return false;
	}
	default:
		assert(false);
	}
}

void Term::get_nested_terms(set<Term*>& terms, bool include_function_subterms,
		bool include_constants)
{
	if(! include_constants && get_term_type() == CONSTANT_TERM) return;
	if(terms.count(this) > 0) return;
	terms.insert(this);
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
	case VARIABLE_TERM:
		return;
	case FUNCTION_TERM: {
		if(!include_function_subterms) return;
		FunctionTerm* ft = (FunctionTerm*) this;
		const vector<Term*>& args = ft->get_args();
		for(unsigned int i=0; i< args.size(); i++) {
			args[i]->get_nested_terms(terms, include_function_subterms,
					include_constants);
		}
		return;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			it->first->get_nested_terms(terms, include_function_subterms,
					include_constants);
		}
		return;
	}
	default:
		assert(false);
	}
}


bool Term::contains_term(set<Term*>& t)
{
	if(t.count(this) > 0) return true;
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
		return false;
	case VARIABLE_TERM:
	{
		return false;
	}
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*) this;
		const vector<Term*>& args = ft->get_args();
		for(unsigned int i=0; i< args.size(); i++) {
			if(args[i]->contains_term(t)) return true;
		}
		return false;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			if(it->first->contains_term(t)) return true;
		}
		return false;
	}
	default:
		assert(false);
	}
}

bool Term::contains_term(Term* t)
{
	if(this == t) return true;
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
		return false;
	case VARIABLE_TERM:
	{
		return false;
	}
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*) this;
		const vector<Term*>& args = ft->get_args();
		for(unsigned int i=0; i< args.size(); i++) {
			if(args[i]->contains_term(t)) return true;
		}
		return false;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			if(it->first->contains_term(t)) return true;
		}
		return false;
	}
	default:
		assert(false);
	}
}

bool Term::contains_var(int var_id)
{
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
		return false;
	case VARIABLE_TERM:
	{
		VariableTerm* vt = (VariableTerm*) this;
		return(vt->get_var_id() == var_id);
	}
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*) this;
		const vector<Term*>& args = ft->get_args();
		for(unsigned int i=0; i<args.size(); i++) {
			Term* cur_arg = args[i];
			if(cur_arg->contains_var(var_id)) return true;
		}
		return false;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			if(it->first->contains_var(var_id)) return true;
		}
		return false;
	}
	default:
		assert(false);
	}
}

/*
 * Returns a new terms where occurences of old_id are replaced
 * by variable with ne_id.
 */
Term* Term::replace_term(Term* old_term, Term* new_term)
{
	map<Term*, Term*> subs;
	subs[old_term] = new_term;
	return this->substitute(subs);
}

void Term::get_vars(set<string>& vars)
{
	term_type tt = get_term_type();
	if (tt == CONSTANT_TERM)
		return;
	if (tt == VARIABLE_TERM) {
		VariableTerm* vt = (VariableTerm*) this;
		vars.insert(vt->get_name());
		return;
	}
	if (tt == FUNCTION_TERM) {
		FunctionTerm* ft = (FunctionTerm*) this;
		for (unsigned int i = 0; i < ft->get_args().size(); i++) {
			ft->get_args()[i]->get_vars(vars);
		}
	} else {
		assert(tt == ARITHMETIC_TERM);
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for (; it != at->get_elems().end(); it++) {
			it->first->get_vars(vars);
		}
	}
}

void Term::get_vars(set<int>& vars)
{
	term_type tt = get_term_type();
	if (tt == CONSTANT_TERM)
		return;
	if (tt == VARIABLE_TERM) {
		VariableTerm* vt = (VariableTerm*) this;
		vars.insert(vt->get_var_id());
		return;
	}
	if (tt == FUNCTION_TERM) {
		FunctionTerm* ft = (FunctionTerm*) this;
		for (unsigned int i = 0; i < ft->get_args().size(); i++) {
			ft->get_args()[i]->get_vars(vars);
		}
	} else {
		assert(tt == ARITHMETIC_TERM);
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for (; it != at->get_elems().end(); it++) {
			it->first->get_vars(vars);
		}
	}
}

void Term::get_vars(set<Term*>& vars)
{


	term_type tt = get_term_type();
	if (tt == CONSTANT_TERM)
		return;
	if (tt == VARIABLE_TERM) {
		VariableTerm* vt = (VariableTerm*) this;
		vars.insert(vt);
		return;
	}
	if (tt == FUNCTION_TERM) {
		FunctionTerm* ft = (FunctionTerm*) this;
		for (unsigned int i = 0; i < ft->get_args().size(); i++) {
			ft->get_args()[i]->get_vars(vars);
		}
	} else {
		assert(tt == ARITHMETIC_TERM);
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for (; it != at->get_elems().end(); it++) {
			it->first->get_vars(vars);
		}
	}
}

Term* Term::rename_variable(int old_var_id, int new_var_id)
{
	switch (get_term_type()) {
		case CONSTANT_TERM:
			return this;
		case VARIABLE_TERM: {
			VariableTerm* vt = (VariableTerm*) this;
			if (old_var_id != vt->get_var_id())
				return this;
			Term* res = VariableTerm::make(new_var_id);
			return res;
		}
		case FUNCTION_TERM: {
			FunctionTerm* ft = (FunctionTerm*) this;
			const vector<Term*>& args = ft->get_args();
			map<Term*, Term*> old_to_new;
			bool changed = false;
			for (unsigned int i = 0; i < args.size(); i++) {
				Term* old_arg = args[i];
				Term* new_arg = args[i]->rename_variable(old_var_id, new_var_id);
				if (new_arg != args[i])
					changed = true;
				old_to_new[old_arg] = new_arg;
			}

			if (!changed)
				return this;
			Term* res = ft->substitute(old_to_new);
			return res;

		}
		case ARITHMETIC_TERM: {
			ArithmeticTerm* at = (ArithmeticTerm*) this;
			bool changed = false;
			map<Term*, long int> new_elems;
			map<Term*, long int>::const_iterator it = at->get_elems().begin();
			for (; it != at->get_elems().end(); it++) {
				Term* new_t = it->first->rename_variable(old_var_id, new_var_id);
				if (new_t != it->first)
					changed = true;
				new_elems[new_t] += it->second;
			}
			if (!changed)
				return at;
			Term* res = ArithmeticTerm::make(new_elems, at->get_constant());
			return res;
		}
		default:
			assert(false);
	}
}

Term* Term::rename_variables(map<int, int>& replacements)
{
	switch (get_term_type()) {
		case CONSTANT_TERM:
			return this;
		case VARIABLE_TERM: {
			VariableTerm* vt = (VariableTerm*) this;
			int var_id = vt->get_var_id();
			if (replacements.count(var_id)==0)
				return this;
			Term* res= VariableTerm::make(replacements[var_id]);
			return res;
		}
		case FUNCTION_TERM: {
			FunctionTerm* ft = (FunctionTerm*) this;
			const vector<Term*>& args = ft->get_args();
			vector<Term*> new_args;
			bool changed = false;
			for (unsigned int i = 0; i < args.size(); i++) {
				Term* new_arg = args[i]->rename_variables(replacements);
				if (new_arg != args[i])
					changed = true;
				new_args.push_back(new_arg);
			}

			if (!changed)
				return this;
			Term* res= FunctionTerm::make(ft->get_id(), new_args,
					ft->is_invertible());
			return res;

		}
		case ARITHMETIC_TERM: {
			ArithmeticTerm* at = (ArithmeticTerm*) this;
			bool changed = false;
			map<Term*, long int> new_elems;
			map<Term*, long int>::const_iterator it = at->get_elems().begin();
			for (; it != at->get_elems().end(); it++) {
				Term* new_t = it->first->rename_variables(replacements);
				if (new_t != it->first)
					changed = true;
				new_elems[new_t] += it->second;
			}
			if (!changed)
				return at;
			Term* res= ArithmeticTerm::make(new_elems, at->get_constant());
			return res;
		}
		default:
			assert(false);
	}
}


/*
 * Does this term and the other term share any subterms?
 */
bool Term::shares_subterms(Term* other)
{
	set<Term*> this_terms;
	this->get_nested_terms(this_terms, true, true );
	set<Term*> other_terms;
	other->get_nested_terms(other_terms, true, true);
	set<Term*> intersection;
	set_intersection(this_terms.begin(), this_terms.end(),
			other_terms.begin(), other_terms.end(),
			insert_iterator<set<Term*> > (intersection, intersection.begin()));
	return intersection.size() > 0;
}

Term* Term::substitute(Term* (*sub_func)(Term* t))
{
	Term* new_t = (*sub_func)(this);
	if(new_t != this) {
		return new_t;
	}
	Term* res = NULL;
	switch (get_term_type()) {
		case CONSTANT_TERM:
		case VARIABLE_TERM: {
			res=  this;
			break;
		}
		case FUNCTION_TERM: {
			FunctionTerm* ft = (FunctionTerm*) this;
			const vector<Term*>& args = ft->get_args();
			vector<Term*> new_args;
			bool changed = false;
			for (unsigned int i = 0; i < args.size(); i++) {
				Term* new_arg = args[i]->substitute(sub_func);
				if (new_arg != args[i])
					changed = true;
				new_args.push_back(new_arg);
			}

			if (!changed) {
				res = this;
				break;
			}
			res= FunctionTerm::make(ft->get_id(), new_args, ft->is_invertible());

			break;

		}
		case ARITHMETIC_TERM: {
			ArithmeticTerm* at = (ArithmeticTerm*) this;
			bool changed = false;
			map<Term*, long int> new_elems;
			map<Term*, long int>::const_iterator it = at->get_elems().begin();
			for (; it != at->get_elems().end(); it++) {
				Term* new_t = it->first->substitute(sub_func);
				if (new_t != it->first)
					changed = true;
				new_elems[new_t]+= it->second;
			}
			if (!changed) {
				res =  at;
				break;
			}
			res = ArithmeticTerm::make(new_elems, at->get_constant());
			break;
		}
		default:
			assert(false);
	}
	return res;
}


Term* Term::substitute(Term* (*sub_func)(Term* t, void* data), void* my_data)
{
	Term* new_t = (*sub_func)(this, my_data);
	if(new_t != this) {
		return new_t;
	}
	Term* res = NULL;
	switch (get_term_type()) {
		case CONSTANT_TERM:
		case VARIABLE_TERM: {
			res=  this;
			break;
		}
		case FUNCTION_TERM: {
			FunctionTerm* ft = (FunctionTerm*) this;
			const vector<Term*>& args = ft->get_args();
			vector<Term*> new_args;
			bool changed = false;
			for (unsigned int i = 0; i < args.size(); i++) {
				Term* new_arg = args[i]->substitute(sub_func, my_data);
				if (new_arg != args[i])
					changed = true;
				new_args.push_back(new_arg);
			}

			if (!changed) {
				res = this;
				break;
			}
			res= FunctionTerm::make(ft->get_id(), new_args, ft->is_invertible());

			break;

		}
		case ARITHMETIC_TERM: {
			ArithmeticTerm* at = (ArithmeticTerm*) this;
			bool changed = false;
			map<Term*, long int> new_elems;
			map<Term*, long int>::const_iterator it = at->get_elems().begin();
			for (; it != at->get_elems().end(); it++) {
				Term* new_t = it->first->substitute(sub_func, my_data);
				if (new_t != it->first)
					changed = true;
				new_elems[new_t]+= it->second;
			}
			if (!changed) {
				res =  at;
				break;
			}
			res = ArithmeticTerm::make(new_elems, at->get_constant());
			break;
		}
		default:
			assert(false);
	}
	return res;
}

Term* Term::flip_sign()
{
	map<Term*, long int> elems;
	elems[this] = -1;
	Term* res= ArithmeticTerm::make(elems, 0);
	return res;
}

Term* Term::multiply(long int factor)
{
	map<Term*, long int> elems;
	elems[this] = factor;
	Term* res= ArithmeticTerm::make(elems, 0);
	return res;
}


Term* Term::multiply(Term* t)
{
	if(t->get_term_type() == CONSTANT_TERM) {
		ConstantTerm* ct = static_cast<ConstantTerm*>(t);
		return multiply(ct->get_constant());
	}

	if(get_term_type() == CONSTANT_TERM) {
		ConstantTerm* ct = static_cast<ConstantTerm*>(this);
		return t->multiply(ct->get_constant());
	}


	// non-linear multiplication: use an uninterpreted function
	vector<Term*> args;
	if(t < this) {
		args.push_back(t);
		args.push_back(this);
	}
	else {
		args.push_back(this);
		args.push_back(t);
	}
	Term* ft = FunctionTerm::make("multiply", args, false);
	return ft;

}
Term* Term::add(long int constant)
{
	map<Term*, long int> elems;
	elems[this] = 1;
	Term* res = ArithmeticTerm::make(elems, constant);
	return res;
}

Term* Term::add(Term* t)
{
	map<Term*, long int> elems;

	elems[this] = 1;
	elems[t] += 1;
	Term* res= ArithmeticTerm::make(elems, 0);
	return res;


}
Term* Term::subtract(Term* t)
{
	map<Term*, long int> elems;

	elems[this] = 1;
	elems[t] -= 1;
	Term* res= ArithmeticTerm::make(elems, 0);
	return res;
}

Term::~Term() {

}

Term* Term::evalute_term(map<Term*, SatValue>& assignments)
{
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
		return this;
	case VARIABLE_TERM:
	{
		if(assignments.count(this) > 0){
			return ConstantTerm::make(assignments[this].value.to_int());
		}
		return this;
	}
	case FUNCTION_TERM:
	{
		if(assignments.count(this) > 0){
			return ConstantTerm::make(assignments[this].value.to_int());
		}
		vector<Term*> new_args;
		FunctionTerm* ft = (FunctionTerm*) this;
		for(unsigned int i = 0; i < ft->get_args().size(); i++)
		{
			Term* arg = ft->get_args()[i];
			arg = arg->evalute_term(assignments);
			new_args.push_back(arg);
		}
		Term* new_t =
				FunctionTerm::make(ft->get_id(), new_args, ft->is_invertible());

		if(assignments.count(new_t) > 0)
			return ConstantTerm::make(assignments[new_t].value.to_int());
		return new_t;

	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		Term* res = ConstantTerm::make(at->get_constant());
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!=elems.end(); it++)
		{
			Term* t = it->first;
			Term* val = t->evalute_term(assignments);
			res = res->add(val->multiply(it->second));
		}
		if(assignments.count(res) > 0)
			return ConstantTerm::make(assignments[res].value.to_int());

		return res;
	}
	default:
		assert(false);
	}
}

void Term::get_all_fun_ids(set<int> & ids)
{
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
	case VARIABLE_TERM:
		return;
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*)this;
		ids.insert(ft->get_id());
		for(unsigned int i=0; i < ft->get_args().size(); i++)
		{
			ft->get_args()[i]->get_all_fun_ids(ids);
		}
		return;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!=elems.end(); it++)
		{
			it->first->get_all_fun_ids(ids);

		}
		return;
	}
	default:
		assert(false);
	}
}

void Term::get_all_first_arguments(set<int>& fn_ids, map<int, set<Term*> >&
		fn_id_to_first_arg)
{
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
	case VARIABLE_TERM:
		return;
	case FUNCTION_TERM:
	{

		FunctionTerm* ft = (FunctionTerm*)this;
		const vector<Term*>& args = ft->get_args();
		int my_id = ft->get_id();
		if(fn_ids.count(my_id) > 0) {
			Term* arg = args[0];
			fn_id_to_first_arg[my_id].insert(arg);
		}

		for(unsigned int i=0; i < args.size(); i++)
		{
			Term* cur = args[i];
			cur->get_all_first_arguments(fn_ids, fn_id_to_first_arg);
		}
		return;

	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!=elems.end(); it++)
		{
			Term* t = it->first;
			t->get_all_first_arguments(fn_ids, fn_id_to_first_arg);

		}
		return;
	}
	default:
		assert(false);
	}
}

Term* Term::replace_first_argument(map<int, Term*>&  fun_id_to_replacements)
{
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
	case VARIABLE_TERM:
		return this;
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*)this;
		const vector<Term*>& args = ft->get_args();
		bool changed = false;
		vector<Term*> new_args;
		for(unsigned int i=0; i < args.size(); i++)
		{
			Term* cur = args[i];
			Term* new_cur = cur->replace_first_argument(fun_id_to_replacements);
			if(cur != new_cur) {
				changed = true;
			}
			new_args.push_back(new_cur);
		}
		if(fun_id_to_replacements.count(ft->get_id()) > 0)
		{
			changed = true;
			new_args[0] = fun_id_to_replacements[ft->get_id()];
		}
		if(!changed) return this;
		return FunctionTerm::make(ft->get_id(), new_args, ft->is_invertible());

	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		bool changed = false;
		map<Term*, long int> new_elems;
		for(; it!=elems.end(); it++)
		{
			Term* t = it->first;
			long int c = it->second;
			Term* new_t = t->replace_first_argument(fun_id_to_replacements);
			new_elems[new_t] += c;
			if(t!= new_t) changed = true;

		}
		if(!changed) return this;
		return ArithmeticTerm::make(new_elems, at->get_constant());
	}
	default:
		assert(false);
	}
}

Term* Term::replace_argument(int fun_id, int arg_num, Term* replacement)
{
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
	case VARIABLE_TERM:
		return this;
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*)this;
		const vector<Term*>& args = ft->get_args();
		bool changed = false;
		vector<Term*> new_args;
		for(unsigned int i=0; i < args.size(); i++)
		{
			Term* cur = args[i];
			Term* new_cur = cur->replace_argument(fun_id, arg_num, replacement);
			if(cur != new_cur) {
				changed = true;
			}
			new_args.push_back(new_cur);
		}
		if(ft->get_id() == fun_id )
		{
			changed = true;
			new_args[arg_num] = replacement;
		}
		if(!changed) return this;
		return FunctionTerm::make(ft->get_id(), new_args, ft->is_invertible());

	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		bool changed = false;
		map<Term*, long int> new_elems;
		for(; it!=elems.end(); it++)
		{
			Term* t = it->first;
			long int c = it->second;
			Term* new_t = t->replace_argument(fun_id, arg_num, replacement);
			new_elems[new_t] = c;
			if(t!= new_t) changed = true;

		}
		if(!changed) return this;
		return ArithmeticTerm::make(new_elems, at->get_constant());
	}
	default:
		assert(false);
	}
}

void Term::get_all_arguments(int fun_id, int arg_num, set<Term*> & args)
{
	switch(this->get_term_type())
	{
	case CONSTANT_TERM:
	case VARIABLE_TERM:
		return;
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*)this;
		if(ft->get_id() == fun_id){
			assert((int) ft->get_args().size() > arg_num);
			args.insert(ft->get_args()[arg_num]);
		}
		for(unsigned int i=0; i < ft->get_args().size(); i++)
		{
			ft->get_args()[i]->get_all_arguments(fun_id, arg_num, args);
		}
		return;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!=elems.end(); it++)
		{
			it->first->get_all_arguments(fun_id, arg_num, args);

		}
		return;
	}
	default:
		assert(false);
	}
}


void Term::set_attribute(term_attribute_type attribute)
{

	this->attribute =attribute;
}

void Term::get_attributes(set<CNode*> & attributes)
{
	CNode* attrib_c = NULL;
	if(attribute == TERM_ATTRIB_GEQZ) {
		attrib_c = ILPLeaf::make(this, ConstantTerm::make(0), ILP_GEQ);
	}

	else if(attribute == TERM_ATTRIB_GTZ) {

		attrib_c = ILPLeaf::make(this, ConstantTerm::make(0), ILP_GT);
	}
	if(attrib_c != NULL) attributes.insert(attrib_c);


	switch(get_term_type())
	{
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*) this;
		const vector<Term*> & args = ft->get_args();
		for(unsigned int i=0; i<args.size(); i++)
		{
			Term* t = args[i];
			t->get_attributes(attributes);
		}
		break;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) this;
		const map<Term*, long int> & elems = at->get_elems();
		map<Term*, long int>::const_iterator it= elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			t->get_attributes(attributes);
		}
		break;
	}
	default:
		break;
	}

}


namespace std {
	size_t hash<Term*>::operator() (const Term* const & x) const {
		Term*& xx = (Term*&)x;
			return xx->hash_code();
	}

	  bool term_eq::operator()(const Term* l1, const Term* l2) const
	  {
		if(((Term*)l1)->get_term_type() != ((Term*)l2)->get_term_type()) {
			return false;
		}

	    bool res =  *(Term*)l1==*(Term*)l2;
	    return res;
	  }

}




/*
 * Cooper.cpp
 *
 *  Created on: Nov 25, 2011
 *      Author: isil
 */

#include "Cooper.h"
#include "cnode.h"
#include "term.h"
#include <map>

#define DEBUG false


Cooper::Cooper(CNode* _c, Term* t)
{
	this->c = _c;
	this->elim_t = t;
	this->res = False::make();

	remove_coefficients();
	delta = compute_delta();
	compute_a_and_b_terms(this->c, false);

	if(DEBUG) {
		cout << "** Rewritten c: " << c->to_string() << endl;
		cout << "******* A Terms *********" << endl;
		set<Term*>::iterator a_it = a_terms.begin();
		for(; a_it != a_terms.end(); a_it++) {
			cout << "\t" << (*a_it)->to_string() << endl;
		}
		cout << "*************************" << endl;

		cout << "******* B Terms *********" << endl;
		set<Term*>::iterator b_it = b_terms.begin();
		for(; b_it != b_terms.end(); b_it++) {
			cout << "\t" << (*b_it)->to_string() << endl;
		}
		cout << "*************************" << endl;
	}




	/*
	 * Compute left infinite projection; as this is more
	 * efficient if there are fewer b terms than a terms
	 */
	if(b_terms.size() <= a_terms.size())
	{

		if(DEBUG){
			cout << "Delta in left infinite projection: " <<  delta << endl;
		}

		for(int i=1; i<=delta.to_int(); i++)
		{
			CNode* left_inf = compute_infinite_projection(c, true,
					ConstantTerm::make(i));
			if(DEBUG) cout << "Left inf: " << left_inf->to_string() << endl;

			CNode* second_disjunct = False::make();
			for(set<Term*>::iterator it = b_terms.begin();
					it!= b_terms.end(); it++)
			{
				Term* b_i = *it;
				Term* cur_sub = b_i->add(ConstantTerm::make(i));
				map<Term*, Term*> m;
				m[elim_t] = cur_sub;
				CNode* cur_c = c->substitute(m);
				second_disjunct = Connective::make(OR, cur_c, second_disjunct);

			}

			CNode* cur_res = Connective::make(OR, left_inf, second_disjunct);
			res = Connective::make(OR, res, cur_res);


		}
	}

	/*
	 * Compute right infinite projection; as this is more
	 * efficient if there are fewer a terms than b terms
	 */
	else
	{

		for(int i=1; i<=delta.to_int(); i++)
		{
			CNode* right_inf = compute_infinite_projection(c, false,
					ConstantTerm::make(-i));

			if(DEBUG) {
				cout << "Right inf projection: " << right_inf->to_string() << endl;
			}

			CNode* second_disjunct = False::make();
			for(set<Term*>::iterator it = a_terms.begin();
					it!= a_terms.end(); it++)
			{
				Term* a_i = *it;
				Term* cur_sub = a_i->subtract(ConstantTerm::make(i));
				map<Term*, Term*> m;
				m[elim_t] = cur_sub;
				CNode* cur_c = c->substitute(m);
				second_disjunct = Connective::make(OR, cur_c, second_disjunct);

			}

			CNode* cur_res = Connective::make(OR, right_inf, second_disjunct);
			res = Connective::make(OR, res, cur_res);

		}
	}



}

CNode* Cooper::get_result()
{
	return res;
}



void Cooper::collect_coefficients(CNode* c, set<bignum>& coefficients)
{

	if(c->get_type() == ILP)
	{
		ILPLeaf* ilp = static_cast<ILPLeaf*>(c);
		if(!ilp->contains_elem(elim_t)) return;
		bignum c = ilp->get_coefficient(elim_t);
		c = c.abs();
		if(c!= 1) coefficients.insert(c);
		return;
	}

	if(c->get_type() == MOD)
	{
		ModLeaf* m = static_cast<ModLeaf*>(c);
		Term* t = m->get_term();

		if(t->get_term_type() == ARITHMETIC_TERM)
		{
			ArithmeticTerm* at = static_cast<ArithmeticTerm*>(t);
			const map<Term*, long int>& elems = at->get_elems();
			if(elems.count(elim_t) > 0)
			{
				bignum coef = elems.find(elim_t)->second;
				coef = coef.abs();
				if(coef != 1) coefficients.insert(coef);
			}
		}

		return;
	}

	if(c->is_connective())
	{
		Connective* conn = static_cast<Connective*>(c);
		const set<CNode*>& ops = conn->get_operands();
		for(set<CNode*>::const_iterator it = ops.begin(); it!= ops.end(); it++)
		{
			CNode* cur = *it;
			collect_coefficients(cur, coefficients);
		}
	}

}

bignum Cooper::get_lcm(set<bignum>& coefs)
{
	bignum lcm = 1;
	for(set<bignum>::iterator it = coefs.begin(); it!= coefs.end(); it++)
	{
		const bignum& b = *it;
		lcm = lcm.compute_lcm(b);
	}
	return lcm;

}

CNode* Cooper::normalize_coefficients(CNode* c, bignum lcm)
{
	if(c->get_type() == ILP)
	{
		ILPLeaf* ilp = static_cast<ILPLeaf*>(c);
		if(!ilp->contains_elem(elim_t)) return ilp;
		bignum c = ilp->get_coefficient(elim_t);
		bignum multiply_factor = lcm/c;
		multiply_factor = multiply_factor.abs();

		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int> new_elems;

		map<Term*,long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* cur = it->first;
			long int old_coef = it->second;
			if(cur == elim_t) {

				if(old_coef > 0) new_elems[cur] =1;
				else new_elems[cur] = -1;
			}

			else {
				new_elems[cur] = (multiply_factor*old_coef).to_int();
			}
		}

		long int new_constant = (multiply_factor*ilp->get_constant()).to_int();
		CNode* new_ilp = ILPLeaf::make(ilp->get_operator(), new_elems,
				new_constant);
		return new_ilp;
	}


	if(c->get_type() == MOD)
	{
		ModLeaf* m = static_cast<ModLeaf*>(c);
		Term* t = m->get_term();
		long int mod_c = m->get_mod_constant();

		if(!t->contains_term(elim_t)) return m;
		if(t->get_term_type() == ARITHMETIC_TERM)
		{
			ArithmeticTerm* at = static_cast<ArithmeticTerm*>(t);
			const map<Term*, long int>& elems = at->get_elems();
			if(elems.count(elim_t) == 0) return m;
			bignum coef = elems.find(elim_t)->second;
			bignum mult_factor = lcm/coef;

			map<Term*, long int> new_elems;

			for(map<Term*, long int>::const_iterator it = elems.begin();
					it!= elems.end(); it++)
			{
				Term* t = it->first;
				long int old_coef = it->second;
				if(t==elim_t) new_elems[t] =1;
				else new_elems[t] = (mult_factor*old_coef).to_int();

			}

			Term* new_at = ArithmeticTerm::make(new_elems, 0);
			int new_constant = (mult_factor*mod_c).to_int();
			CNode* new_ml = ModLeaf::make(new_at, new_constant);
			return new_ml;


		}

		if(t == elim_t)
		{
			int new_constant = (lcm*mod_c).to_int();
			CNode* new_ml = ModLeaf::make(t, new_constant);
			return new_ml;
		}
		return m;


	}

	if(c->is_connective())
	{
		Connective* conn = static_cast<Connective*>(c);
		bool changed = false;
		set<CNode*> new_ops;
		const set<CNode*>& ops = conn->get_operands();
		for(set<CNode*>::const_iterator it = ops.begin(); it!= ops.end(); it++)
		{
			CNode* cur = *it;
			CNode* new_cur = normalize_coefficients(cur, lcm);
			if(cur != new_cur) changed = true;
			new_ops.insert(new_cur);
		}

		if(!changed) return c;
		return Connective::make(conn->get_type(), new_ops);
	}

	return c;

}

bignum Cooper::compute_delta()
{
	bignum delta = compute_delta_rec(1, c);
	return delta.abs();
}

bignum Cooper::compute_delta_rec(bignum delta, CNode* c)
{
	if(c->get_type() == MOD)
	{
		ModLeaf* ml = static_cast<ModLeaf*>(c);
		bignum mod_c = ml->get_mod_constant();
		return mod_c.compute_lcm(delta);
	}

	if(c->is_connective())
	{
		bignum new_delta = delta;
		Connective* conn = static_cast<Connective*>(c);
		const set<CNode*>& ops = conn->get_operands();
		for(set<CNode*>::const_iterator it = ops.begin(); it != ops.end(); it++)
		{
			CNode* cur = *it;
			new_delta = compute_delta_rec(new_delta, cur);
		}

		return new_delta;
	}

	return delta;


}


CNode* Cooper::compute_infinite_projection(CNode* c, bool left,
		Term* rt)
{
	if(c->get_type() == EQ)
	{
		EqLeaf* eq = static_cast<EqLeaf*>(c);
		Term* rhs = eq->get_rhs();
		Term* lhs = eq->get_lhs();
		if(rhs!= elim_t && lhs != elim_t) return c;

		return False::make();
	}

	if(c->get_type() == ILP)
	{
		ILPLeaf* ilp = static_cast<ILPLeaf*>(c);
		if(!ilp->contains_elem(elim_t)) return c;
		if(ilp->get_operator() == ILP_EQ){
			return False::make();
		}
		int coef = ilp->get_coefficient(elim_t);


		if(coef>0) {
			if(left) {
				return True::make();
			}
			else {
				return False::make();
			}
		}

		else {
			if(left) {
				return False::make();
			}
			else {
				return True::make();;
			}
		}

	}

	if(c->get_type() == MOD)
	{
		map<Term*, Term*> m;
		m[elim_t] = rt;
		return c->substitute(m);
	}

	if(c->is_connective())
	{
		Connective* conn = static_cast<Connective*>(c);
		const set<CNode*>& ops = conn->get_operands();
		set<CNode*> new_ops;
		bool changed = false;
		for(set<CNode*>::const_iterator it = ops.begin(); it!= ops.end(); it++)
		{
			CNode* cur = *it;
			CNode* new_cur = compute_infinite_projection(cur, left,
					 rt);
			if(new_cur != cur) changed=true;
			new_ops.insert(new_cur);
		}
		if(!changed) return c;
		return Connective::make(conn->get_type(), new_ops);
	}
	return c;


}

void Cooper::compute_a_and_b_terms(CNode* c, bool in_neg)
{
	if(c->get_type() == EQ)
	{
		EqLeaf* eq = static_cast<EqLeaf*>(c);
		Term* rhs = eq->get_rhs();
		Term* lhs = eq->get_lhs();
		if(rhs!= elim_t && lhs != elim_t) return;
		Term* other;
		if(rhs == elim_t) other = lhs;
		else other = rhs;

		if(in_neg) {
			a_terms.insert(other);
			b_terms.insert(other);
			return;
		}

		Term* other_plus1 = other->add(ConstantTerm::make(1));
		Term* other_minus1 = other->subtract(ConstantTerm::make(1));
		a_terms.insert(other_plus1);
		b_terms.insert(other_minus1);
		return;
	}
	if(c->get_type() == ILP)
	{
		ILPLeaf* ilp = static_cast<ILPLeaf*>(c);
		if(!ilp->contains_elem(elim_t)) return;
		int coef = ilp->get_coefficient(elim_t);
		int constant = ilp->get_constant();

		map<Term*, long int> new_elems = ilp->get_elems();
		new_elems.erase(elim_t);
		Term* at = ArithmeticTerm::make(new_elems, -constant);

		if(ilp->get_operator() ==ILP_LEQ)
		{
			if(!in_neg)
			{
				if(coef == 1) {
					at = at->multiply(ConstantTerm::make(-1));
					at = at->add(ConstantTerm::make(1));
					a_terms.insert(at);

				}

				else {
					assert(coef == -1);
					at = at->subtract(ConstantTerm::make(1));
					b_terms.insert(at);
				}
			}

			// actually a > because inside negation
			else {
				if(coef > 0){
					// bterm
					at = at->multiply(ConstantTerm::make(-1));
					b_terms.insert(at);
				}
				else {
					a_terms.insert(at);
				}

			}

		}
		else {
			assert(ilp->get_operator()==ILP_EQ);
			if(coef == 1) {
				at = at->multiply(ConstantTerm::make(-1));
			}
			if(in_neg) {
				a_terms.insert(at);
				b_terms.insert(at);
				return;
			}


			Term* at_plus1 = at->add(ConstantTerm::make(1));
			Term* at_minus1=at->subtract(ConstantTerm::make(1));
			a_terms.insert(at_plus1);
			b_terms.insert(at_minus1);

		}

		return;
	}

	if(c->is_connective())
	{
		Connective* conn = static_cast<Connective*>(c);
		const set<CNode*>& ops = conn->get_operands();
		for(set<CNode*>::const_iterator it = ops.begin(); it != ops.end(); it++)
		{
			CNode* cur = *it;
			compute_a_and_b_terms(cur, conn->get_type() == NOT);
		}
	}
}

/*
 * Rewrites the formula Ex. F to an equivalent formula Ex. F'
 * such that no leaf in the formula contains x with coefficients.
 */
void Cooper::remove_coefficients()
{
	set<bignum> coefs;
	collect_coefficients(c, coefs);
	bignum lcm = get_lcm(coefs);
	if(DEBUG) cout << "lcm: " << lcm << endl;
	if(lcm == 1) return;

	/*
	 * Make new mod leaf
	 */
	CNode* mod = ModLeaf::make(elim_t, lcm.to_int());
	if(DEBUG) cout << "mod: " << mod->to_string() << endl;

	/*
	 * Normalize all coefficients of x to lcm
	 */
	CNode* normalized_c = normalize_coefficients(c, lcm);
	if(DEBUG) cout << "normalized_c: " << normalized_c->to_string() << endl;

	c = Connective::make(AND, mod, normalized_c);
}

Cooper::~Cooper() {

}

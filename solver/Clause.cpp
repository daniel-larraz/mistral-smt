/*
 * Clause.cpp
 *
 *  Created on: Feb 8, 2009
 *      Author: tdillig
 */

#include "Clause.h"
#include "Connective.h"
#include "CNode.h"
#include "EqLeaf.h"
#include "ILPLeaf.h"
#include "QuantifiedLeaf.h"
#include "assert.h"
#include "term.h"
#include "cnode.h"
#include "util.h"
#include <algorithm>

#define DENEST_PREFIX "$d"
#define DEBUG false

Clause::Clause()
{
}

Clause::Clause(CNode* node)
{

	assert(node->is_conjunct());

	if(node->is_literal()) {
		add_literal(node);
	}
	else {
		Connective* c_and = (Connective*) node;
		set<CNode*>::const_iterator it = c_and->get_operands().begin();
		for(; it!= c_and->get_operands().end(); it++)
		{
			add_literal(*it);
		}
	}


}




void Clause::add_literal(CNode* cur)
{

	/*
	 * Be sure to use the canonic node here
	 */
	cur = cur->fold_negated_ilps();
	switch(cur->get_type())
	{
		/*
		 * For now, we just make up a fake EqLeaf.
		 */
		case BOOLEAN_VAR:
		{
			BooleanVar* bv = (BooleanVar*) cur;
			pos_eq.insert(bv->to_eqleaf());
			break;
		}
		case ILP:
		{
			pos_ilp.insert((ILPLeaf*)cur);
			break;
		}
		case EQ:
		{
			pos_eq.insert((EqLeaf*) cur);
			break;
		}


		case MOD:
		{
			ModLeaf* ml = (ModLeaf*) cur;
			pos_mod.insert(ml);
			break;
		}

		case NOT:
		{
			Connective* not_c = (Connective*) cur;
			cur = *not_c->get_operands().begin();
			if(cur->get_type() == BOOLEAN_VAR)
			{
				BooleanVar* bv = (BooleanVar*) cur;
				neg_eq.insert(bv->to_eqleaf());
			}
			else if(cur->get_type() == ILP) {
				neg_ilp.insert((ILPLeaf*)cur);
			}
			else if(cur->get_type() == EQ) {
				neg_eq.insert((EqLeaf*)cur);
			}
			else if(cur->get_type() == MOD){
				ModLeaf* ml = (ModLeaf*) cur;
				neg_mod.insert(ml);
			}
			else{
				assert(false);
			}
			break;
		}
		case TRUE_NODE:
		{
			break;
		}
		default:
			assert(false);
	}
}

void Clause::denest(map<Term*, Term*>* denestings)
{

	if(DEBUG)
		cout << "********DENESTING CLAUSE: " << this->to_string("&") << endl;
	int counter = 0;
	set<CNode*> to_add;

	set<ILPLeaf*>::iterator it = pos_ilp.begin();
	set<ILPLeaf*> new_pos_ilp;
	set<ILPLeaf*> new_neg_ilp;
	set<EqLeaf*> new_pos_eq;
	set<EqLeaf*> new_neg_eq;
	set<ModLeaf*> new_pos_mod;
	set<ModLeaf*> new_neg_mod;
	for(; it!= pos_ilp.end(); it++)
	{
		ILPLeaf* ilp = *it;
		CNode* new_ilp = denest_leaf(ilp, to_add, counter,
				denestings);
		switch(new_ilp->get_type())
		{
		case EQ:
		{
			new_pos_eq.insert((EqLeaf*)new_ilp);
			break;
		}
		case ILP:
		{
			new_pos_ilp.insert((ILPLeaf*)new_ilp);
			break;
		}
		default:
			assert(false);

		}
	}
	pos_ilp = new_pos_ilp;

	it = neg_ilp.begin();

	for(; it!= neg_ilp.end(); it++)
	{
		ILPLeaf* ilp = *it;
		CNode* new_ilp = denest_leaf(ilp, to_add, counter,
				denestings);
		switch(new_ilp->get_type())
		{
		case EQ:
		{
			new_neg_eq.insert((EqLeaf*)new_ilp);
			break;
		}
		case ILP:
		{
			new_neg_ilp.insert((ILPLeaf*)new_ilp);
			break;
		}
		default:
			assert(false);

		}
	}
	neg_ilp = new_neg_ilp;



	set<EqLeaf*>::iterator it2 = pos_eq.begin();

	for(; it2!= pos_eq.end(); it2++)
	{
		CNode* new_eq = denest_leaf(*it2, to_add, counter,
				denestings);
		assert(new_eq->get_type() == EQ);
		new_pos_eq.insert((EqLeaf*)new_eq);
	}
	pos_eq = new_pos_eq;

	it2 = neg_eq.begin();

	for(; it2!= neg_eq.end(); it2++)
	{
		CNode* new_eq = denest_leaf(*it2, to_add, counter,
				denestings);
		assert(new_eq->get_type() == EQ);
		new_neg_eq.insert((EqLeaf*)new_eq);
	}
	neg_eq = new_neg_eq;



	set<ModLeaf*>::iterator it4 = pos_mod.begin();
	for(; it4!=pos_mod.end(); it4++)
	{
		ModLeaf* ml = *it4;
		CNode* new_mod = denest_leaf(ml, to_add, counter, denestings);
		assert(new_mod->get_type() == MOD);
		new_pos_mod.insert((ModLeaf*)new_mod);

	}
	pos_mod = new_pos_mod;

	 it4 = neg_mod.begin();
	for(; it4!=neg_mod.end(); it4++)
	{
		ModLeaf* ml = *it4;
		CNode* new_mod = denest_leaf(ml, to_add, counter, denestings);
		assert(new_mod->get_type() == MOD);
		new_neg_mod.insert((ModLeaf*)new_mod);

	}
	neg_mod = new_neg_mod;

	/*
	 * Now, add denestings to pos_ilp/pos_eq.
	 */
	set<CNode*>::iterator it3 = to_add.begin();
	for(; it3!= to_add.end(); it3++)
	{
		CNode* l = *it3;
		assert(l->get_type() == EQ || l->get_type() == ILP);
		if(l->get_type() == EQ){
			pos_eq.insert((EqLeaf*)l);
		}
		else pos_ilp.insert((ILPLeaf*)l);
	}


	if(DEBUG)
		cout << "********DONE DENESTING: " << this->to_string("&") << endl;
}


/*
 * Clause functions
 */
CNode* Clause::to_cnode(bool use_and)
{
	set<CNode*> operands;
	operands.insert(pos_eq.begin(), pos_eq.end());
	set<EqLeaf*>::iterator it = neg_eq.begin();
	for(; it!= neg_eq.end(); it++)
	{
		EqLeaf* cur = *it;
		CNode *n = Connective::make_not(cur);
		operands.insert(n);
	}
	operands.insert(pos_ilp.begin(), pos_ilp.end());
	set<ILPLeaf*>::iterator it2 = neg_ilp.begin();
	for(; it2!= neg_ilp.end(); it2++)
	{
		ILPLeaf* cur = *it2;
		CNode *n = Connective::make_not(cur);
		operands.insert(n);
	}
	operands.insert(pos_universal.begin(), pos_universal.end());
	set<QuantifiedLeaf*>::iterator it3 = neg_universal.begin();
	for(; it3!= neg_universal.end(); it3++)
	{
		QuantifiedLeaf* cur = *it3;
		CNode *n = Connective::make_not(cur);
		operands.insert(n);
	}
	operands.insert(pos_mod.begin(), pos_mod.end());
	set<ModLeaf*>::iterator it4 = neg_mod.begin();
	for(; it4 != neg_mod.end(); it4++)
	{
		ModLeaf* ml = *it4;
		CNode* n = Connective::make_not(ml);
		operands.insert(n);
	}

	CNode* inner = NULL;
	if(use_and) {
		inner = Connective::make_and(operands, false);
	}
	else {
		inner = Connective::make_or(operands, false);
	}


	return inner;
}


bool Clause::subsumes(Clause & other)
{
	bool subsume1 = includes(other.pos_eq.begin(),other.pos_eq.end(),
							pos_eq.begin(), pos_eq.end());
	if(!subsume1) return false;

	bool subsume2 = includes(other.neg_eq.begin(),other.neg_eq.end(),
							neg_eq.begin(), neg_eq.end());
	if(!subsume2) return false;

	bool subsume3 = includes(other.pos_ilp.begin(),other.pos_ilp.end(),
							pos_ilp.begin(), pos_ilp.end());
	if(!subsume3) return false;

	bool subsume4 = includes(other.neg_ilp.begin(),other.neg_ilp.end(),
							neg_ilp.begin(), neg_ilp.end());
	if(!subsume4) return false;

	bool subsume5 = includes(other.pos_universal.begin(),
			other.pos_universal.end(), pos_universal.begin(),
			pos_universal.end());
	if(!subsume5) return false;

	bool subsume6 = includes(other.pos_mod.begin(),
			other.pos_mod.end(), pos_mod.begin(),
			pos_mod.end());
	if(!subsume6) return false;

	bool subsume7 = includes(other.neg_mod.begin(),
			other.neg_mod.end(), neg_mod.begin(),
			neg_mod.end());
	if(!subsume7) return false;

	return includes(other.neg_universal.begin(),
					other.neg_universal.end(), neg_universal.begin(),
					neg_universal.end());
}

bool Clause::drop_clause()
{
	set<Leaf*> temp;
	set_intersection( pos_eq.begin(), pos_eq.end(),
			neg_eq.begin(), neg_eq.end(),
			inserter(temp,temp.begin()) );
	if(temp.size()>0)
		return true;

	set_intersection( pos_ilp.begin(), pos_ilp.end(),
			neg_ilp.begin(), neg_ilp.end(),
			inserter(temp,temp.begin()) );
	if(temp.size()>0)
		return true;

	set_intersection( pos_universal.begin(), pos_universal.end(),
			neg_universal.begin(), neg_universal.end(),
			inserter(temp,temp.begin()) );
	if(temp.size()>0)
		return true;

	set_intersection( pos_mod.begin(), pos_mod.end(),
			neg_mod.begin(), neg_mod.end(),
			inserter(temp,temp.begin()) );
	return (temp.size()>0);
}

string Clause::to_string(string c)
{
	string res;
	set<EqLeaf*>::iterator it = pos_eq.begin();
	unsigned int i = 0;
	for(; it!= pos_eq.end(); it++, i++)
	{
		EqLeaf* cur = *it;
		res+= cur->to_string();
		res+= c;
	}
	it = neg_eq.begin();
	i = 0;
	for(; it!= neg_eq.end(); it++, i++)
	{
		EqLeaf* cur = *it;
		res+= "!" + cur->to_string();
		res+= c;
	}
	set<ILPLeaf*>::iterator it2 = pos_ilp.begin();
	i = 0;
	for(; it2!= pos_ilp.end(); it2++, i++)
	{
		Leaf* cur = *it2;
		res+= cur->to_string();
		res+= c;
	}
	it2 = neg_ilp.begin();
	i = 0;
	for(; it2!= neg_ilp.end(); it2++, i++)
	{
		Leaf* cur = *it2;
		res+= "!" + cur->to_string();
		res+= c;
	}

	set<ModLeaf*>::iterator it_mod = pos_mod.begin();
	for(; it_mod != pos_mod.end(); it_mod++)
	{
		Leaf* cur = *it_mod;
		res += cur->to_string();
		res += c;
	}

	for(it_mod=neg_mod.begin(); it_mod!=neg_mod.end(); it_mod++)
	{
		Leaf* cur = *it_mod;
		res += "!" + cur->to_string();
		res +=c;
	}

	set<QuantifiedLeaf*>::iterator it3 = pos_universal.begin();
	for(; it3 != pos_universal.end(); it3++)
	{
		Leaf* cur = *it3;
		res+= cur->to_string();
		res+= c;
	}

	it3 = neg_universal.begin();
	for(; it3 != neg_universal.end(); it3++)
	{
		Leaf* cur = *it3;
		res+= "!" + cur->to_string();
		res+= c;
	}
	return res.substr(0, res.size()-c.size());
}


Clause::~Clause() {
	// TODO Auto-generated destructor stub
}
//---------------------------------------

Term* Clause::denest_term(Term* t, set<CNode*>& to_add, int& counter,
		map<Term*, Term*>* denestings, bool denest_arithmetic,
		bool denest_function)
{

	term_type tt = t->get_term_type();
	if(tt == CONSTANT_TERM) return t;
	if(tt == VARIABLE_TERM) return t;


	if(tt == ARITHMETIC_TERM)
	{
		if(denest_arithmetic && reverse_denestings.count(t) > 0){
			return reverse_denestings[t];
		}
		ArithmeticTerm* at = (ArithmeticTerm*) t;
		map<Term*, Term*> old_to_new;
		map<Term*, long int> new_elems;
		bool changed = false;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for(; it!= at->get_elems().end(); it++)
		{
			Term* old_t = it->first;
			Term* new_t = denest_term(old_t, to_add, counter, denestings,
					false, true);
			if(new_t != old_t) changed = true;
			old_to_new[old_t] = new_t;
			new_elems[new_t] = it->second;
		}

		if(!denest_arithmetic)
		{
			if(!changed) return t;
			return at->substitute(old_to_new);
		}


		int var_id = CNode::get_varmap().get_id(DENEST_PREFIX +
				int_to_string(counter++));
		Term* vt = VariableTerm::make(var_id);
		if(denestings != NULL) (*denestings)[vt] = at;
		reverse_denestings[at] = vt;

		assert(new_elems.count(vt) == 0);
		new_elems[vt] = -1;
		CNode* ilp= ILPLeaf::make(ILP_EQ, new_elems, -at->get_constant());
		ilp = ilp->fold_negated_ilps();
		to_add.insert(ilp);
		return vt;
	}
	if(tt == FUNCTION_TERM)
	{
		if(denest_function && reverse_denestings.count(t) > 0)
			return reverse_denestings[t];

		FunctionTerm* ft = (FunctionTerm*) t;
		bool changed = false;
		map<Term*, Term*> old_to_new_args;
		for(unsigned int i=0; i<ft->get_args().size(); i++)
		{
			Term* old_t = ft->get_args()[i];
			Term* new_t = denest_term(old_t, to_add, counter,
					denestings, true, false);
			if(new_t != old_t) changed = true;
			old_to_new_args[old_t] = new_t;
		}
		if(!denest_function) {
			if(!changed) {
				return ft;
			}
			Term* res = ft->substitute(old_to_new_args);

			return res;
		}

		int var_id = CNode::get_varmap().get_id(DENEST_PREFIX +
				int_to_string(counter++));
		Term* vt = VariableTerm::make(var_id);
		Term* new_ft = NULL;
		if(changed) {
			new_ft = ft->substitute(old_to_new_args);
		}
		else new_ft = ft;

		if(denestings != NULL) (*denestings)[vt] = ft;
		reverse_denestings[ft] = vt;
		CNode* eq = EqLeaf::make(new_ft, vt);
		to_add.insert(eq);
		return vt;


	}
	assert(false);

}

CNode* Clause::denest_leaf(Leaf* l, set<CNode*>& to_add, int& counter,
		map<Term*, Term*>* denestings)
{
	if(l->get_type() == EQ)
	{
		EqLeaf* eq = (EqLeaf*) l;
		Term* new_lhs = denest_term(eq->get_lhs(), to_add, counter, denestings,
				true, false);
		Term* new_rhs = denest_term(eq->get_rhs(), to_add, counter, denestings,
				true, false);


		if(new_lhs == eq->get_lhs() && new_rhs == eq->get_rhs()) return eq;
		return EqLeaf::make(new_lhs, new_rhs);
	}

	if(l->get_type() == ILP)
	{
		ILPLeaf* ilp = (ILPLeaf*) l;
		bool changed = false;
		map<Term*, long int > new_elems;

		map<Term*, long int >::const_iterator it = ilp->get_elems().begin();
		for(; it!= ilp->get_elems().end(); it++)
		{
			if(it->second==0) continue;
			Term* new_t = denest_term(it->first, to_add, counter, denestings,
					false, true);
			if(new_t != it->first) changed = true;
			new_elems.insert(pair<Term*, int>(new_t, it->second));
		}

		if(!changed) return ilp;
		CNode* res =ILPLeaf::make(ilp->get_operator(), new_elems,
				ilp->get_constant());
		res = res->fold_negated_ilps();
		return res;
	}

	if(l->get_type() == MOD)
	{
		ModLeaf* ml = (ModLeaf*) l;
		Term* t = ml->get_term();
		t = denest_term(ml->get_term(), to_add, counter, denestings, false, true);
		if(t == ml->get_term())
			return ml;
		return ModLeaf::make(t, ml->get_mod_constant());


	}

	assert(false);
}



void Clause::make_false()
{
	pos_eq.clear();
	neg_eq.clear();
	pos_ilp.clear();
	neg_ilp.clear();
	pos_universal.clear();
	neg_universal.clear();
	pos_mod.clear();
	neg_mod.clear();

	Term* t = VariableTerm::make("a");
	Term* zero = ConstantTerm::make(0);
	EqLeaf* n = (EqLeaf*)EqLeaf::make(t, zero);
	pos_eq.insert(n);
	neg_eq.insert(n);

}

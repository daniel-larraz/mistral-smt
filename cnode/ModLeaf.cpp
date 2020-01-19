/*
 * ModLeaf.cpp
 *
 *  Created on: Feb 12, 2009
 *      Author: tdillig
 */

#include "ModLeaf.h"
#include "term.h"
#include "cnode.h"
#include "util.h"
#include "assert.h"

#define MOD_PREFIX "$m"

ModLeaf::ModLeaf(Term* t, long int k) {
	node_type = MOD;
	this->t= t;
	this->k = k;
	negations_folded = this;
	hash_c = t->hash_code();
	hash_c = (hash_c*79) + k;

}


/*
 * Converts this mod constraint into a set of ILP leaves
 * First arg: resulting set of ilp leaves
 * Second arg: Indicates phase of the mod leaf
 * Third arg: id of the temp variable to introduce
 */
void ModLeaf::to_ilp(set<ILPLeaf*>& ilp_leaves, bool pos, int temp_id)
{
	/*
	 * a%c = 0 is translated as a=t*c where t is some fresh temporary
	 */
	if(pos){
		map<Term*, long int> elems;
		elems[this->t] = 1;
		VariableTerm* t = get_ilp_temp(temp_id);
		elems[t]= -this->k;
		CNode* _ilp =  ILPLeaf::make(ILP_EQ, elems, 0);
		_ilp = _ilp->fold_negated_ilps();
		assert(_ilp->get_type() == ILP);
		ILPLeaf* ilp = (ILPLeaf*) _ilp;
 		ilp_leaves.insert(ilp);
		return;
	}

	/*
	 * a%c!=0 is translated as a = c*t+t2 & 0<t2<c
	 */
	// First make a = c*t+t2
	map<Term*, long int> elems;
	elems[this->t] = 1;
	pair<VariableTerm*, VariableTerm*> p = get_ilp_temps(temp_id);
	VariableTerm* t1 = p.first;
	VariableTerm* t2 = p.second;
	elems[t1] = -this->k;
	elems[t2] = -1;
	CNode* _ilp =  ILPLeaf::make(ILP_EQ, elems, 0);
	_ilp = _ilp->fold_negated_ilps();
	assert(_ilp->get_type() == ILP);
	ILPLeaf* ilp = (ILPLeaf*) _ilp;
	ilp_leaves.insert(ilp);


	// add t2>0
	map<Term*, long int> elems2;
	elems2[t2] = 1;
	CNode* _ilp2 = ILPLeaf::make(ILP_GT, elems2, 0);
	_ilp2 = _ilp2->fold_negated_ilps();
	assert(_ilp2->get_type() == ILP);
	ILPLeaf* ilp2 = (ILPLeaf*) _ilp2;
	ilp_leaves.insert(ilp2);


	// add t2<c
	map<Term*, long int> elems3;
	elems3[t2] = 1;
	CNode* _ilp3 =  ILPLeaf::make(ILP_LT, elems3, this->k);
	_ilp3 = _ilp3->fold_negated_ilps();
	assert(_ilp3->get_type() == ILP);
	ILPLeaf* ilp3 = (ILPLeaf*) _ilp3;
	ilp_leaves.insert(ilp3);
}

CNode* ModLeaf::make(Term* t, long int k)
{


	if(k==0){
		return False::make();
	}
	if(k==1){
		return True::make();
	}

	if(t->get_term_type() == CONSTANT_TERM)
	{
		ConstantTerm* c = (ConstantTerm*) t;
		long int constant = c->get_constant();
		if(constant%k == 0) return True::make();
		return False::make();
	}
	if(t->get_term_type() == ARITHMETIC_TERM)
	{
		ArithmeticTerm* at = (ArithmeticTerm*) t;
		if(at->has_only_negative_coefficients()){
			t =  at->multiply(-1);
		}
	}

	if(t->get_term_type() == ARITHMETIC_TERM)
	{
		ArithmeticTerm* at = (ArithmeticTerm*) t;
		assert(!at->has_only_negative_coefficients());

		long int elem_gcd = at->get_gcd(false);
		if(elem_gcd%k ==0) {
			if(at->get_constant()%k == 0){
				return True::make();
			}
			else {
				return False::make();
			}
		}
		long int combined_gcd = gcd(elem_gcd, k);
		if(at->get_constant()%combined_gcd != 0) {
			return False::make();
		}

		// Do mod reduction
		long int constant = at->get_constant();
		long int abs_const = labs(constant);
		long int new_constant = abs_const%k;
		if(constant < 0 && new_constant > 0) new_constant = k-new_constant;

		map<Term*, long int> new_elems;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for(; it != at->get_elems().end(); it++) {
			Term* cur_t = it->first;
			long int coef = it->second;
			if(coef % k == 0) continue;
			new_elems[cur_t] += coef;
		}
		t = ArithmeticTerm::make(new_elems, new_constant);

	}
	if(k<0) k = -k;
	ModLeaf* ml = new ModLeaf(t, k);
	CNode* res =  CNode::get_node(ml);
	return res;
}

CNode* ModLeaf::make(Term* t, long int k, Term* r)
{
	Term* new_t = t->subtract(r);
	return make(new_t, k);
}
CNode* ModLeaf::make(Term* t, long int k, long int r)
{
	Term* new_t = t->add(-r);
	return make(new_t, k);
}




Term* ModLeaf::get_term()
{
	return t;
}

long int ModLeaf::get_mod_constant()
{
	return k;
}


bool ModLeaf::operator==(const CNode& other)
{
	if(other.get_type() != MOD) return false;
	ModLeaf& ml = (ModLeaf&) other;
	return (ml.t == t && ml.k==k);

}
CNode* ModLeaf::substitute(map<Term*, Term*>& subs)
{


	Term* new_t = t->substitute(subs);
	if(new_t == t) return this;
	CNode* res = make(new_t, k);
	return res;
}
string ModLeaf::to_string()
{
	string res = t->to_string();
	res += "%" +int_to_string(k);
	res += "=0";;
	return res;
}

VariableTerm* ModLeaf::get_ilp_temp(int temp_id)
{
	string name = MOD_PREFIX + int_to_string(temp_id);
	return (VariableTerm*)VariableTerm::make(name);
}

pair<VariableTerm*, VariableTerm*> ModLeaf::get_ilp_temps(int counter)
{
	string name = MOD_PREFIX + int_to_string(counter);
	string name1 = name +"_a";
	string name2 = name+"_b";
	VariableTerm* t1 = (VariableTerm*) VariableTerm::make(name1);
	VariableTerm* t2 = (VariableTerm*) VariableTerm::make(name2);
	return pair<VariableTerm*, VariableTerm*>(t1, t2);
}

ModLeaf::~ModLeaf()
{

}

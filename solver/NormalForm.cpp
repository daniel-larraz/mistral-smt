/*
 * NormalForm.cpp
 *
 *  Created on: Sep 2, 2008
 *      Author: tdillig
 */

#include "NormalForm.h"
#include "cnode.h"
#include "Leaf.h"
#include "VarMap.h"
#include "Connective.h"
#include <iostream>
#include <assert.h>
#include "mistral.h"
using namespace std;



NormalForm::NormalForm(CNode* node, bool is_dnf)
{
	this->is_dnf = is_dnf;
	this->clauses = make_normal_form(node);
}

set<Clause*>* make_leaf(CNode* node, bool phase)
{

	if(node->get_type() == ILP)
	{
		Clause* inner = new Clause();
		if(phase) inner->pos_ilp.insert((ILPLeaf*)node);
		else  inner->neg_ilp.insert((ILPLeaf*)node);
		set<Clause*>* outer = new set<Clause* >();
		outer->insert(inner);
		return outer;
	}

	if(node->get_type() == BOOLEAN_VAR)
	{
		Clause* inner = new Clause();
		BooleanVar* bv = (BooleanVar*) node;
		if(phase) inner->pos_eq.insert(bv->to_eqleaf());
		else  inner->neg_eq.insert(bv->to_eqleaf());
		set<Clause*>* outer = new set<Clause* >();
		outer->insert(inner);
		return outer;
	}

	if(node->get_type() == EQ)
	{
		Clause* inner = new Clause();
		if(phase) inner->pos_eq.insert((EqLeaf*)node);
		else  inner->neg_eq.insert((EqLeaf*)node);
		set<Clause*>* outer = new set<Clause* >();
		outer->insert(inner);
		return outer;
	}
	if(node->get_type() == MOD)
	{
		Clause* inner = new Clause();
		if(phase) inner->pos_mod.insert((ModLeaf*)node);
		else  inner->neg_mod.insert((ModLeaf*)node);
		set<Clause*>* outer = new set<Clause* >();
		outer->insert(inner);
		return outer;

	}

	if(node->get_type() == UNIVERSAL)
	{
		Clause* inner = new Clause();
		if(phase) inner->pos_universal.insert((QuantifiedLeaf*)node);
		else  inner->neg_universal.insert((QuantifiedLeaf*)node);
		set<Clause*>* outer = new set<Clause* >();
		outer->insert(inner);
		return outer;
	}

	assert(false);
}

set<Clause* >* NormalForm::make_normal_form(CNode* node)
{
	assert(node->get_type() != TRUE_NODE && node->get_type() != FALSE_NODE);
	if(node->is_leaf())
	{
		return make_leaf(node, true);
	}
	if(node->get_type() == NOT)
	{
		CNode* inner_node = *((Connective*)node)->get_operands().begin();
		return make_leaf(inner_node, false);
	}

	assert(node->is_connective());
	Connective* cnode = (Connective*) node;
	const set<CNode*> & args = cnode->get_operands();
	vector<set<Clause* >* > args_normal;

	set<CNode*>::iterator it = args.begin();
	for(; it!= args.end(); it++)
	{
		args_normal.push_back(make_normal_form((*it)));
	}

	if(is_outer_connective(node->get_type()))
	{
		if(args_normal.size() == 0) return new set<Clause*>();
		set<Clause*>* new_outer = args_normal[0];
		for(unsigned int i=1; i<args_normal.size(); i++)
		{
			new_outer = add_clauses(new_outer, args_normal[i]);
		}
		return new_outer;
	}

	// Bad case: we actually need to cross product the sets
	set<Clause*>* result = args_normal[0];
	for(unsigned int i=1; i<args_normal.size(); i++){
		result = product_clauses(result,args_normal[i]);
	}
	return result;
}

/*
 * In DNF, this does: DNF1 \/ DNF2
 * In CNF, CNF1 /\ CNF2
 * It also removes any redundancies.
 */
set<Clause*>* NormalForm::add_clauses(set<Clause* >* nf1,
										  set<Clause* >* nf2)
{
	set<Clause* >* res = new set<Clause*>();
	res->insert(nf1->begin(), nf1->end());
	res->insert(nf2->begin(), nf2->end());


	set<Clause* >::iterator it1 = nf1->begin();
	for(; it1!=nf1->end(); it1++){
		Clause* clause1 = *it1;
		set<Clause* >::iterator it2 = nf2->begin();
		for(; it2!=nf2->end(); it2++){
			Clause* clause2 = *it2;
			bool clause2_subset = clause2->subsumes(*clause1);
			if(clause2_subset){
				cout << "error 1" << endl;
				res->erase(clause1);
				break;
			}
			bool clause1_subset = clause1->subsumes(*clause2);
			if(clause1_subset){
				cout << "error 2" << endl;
				res->erase(clause2);
			}

		}
	}

	delete nf1;
	delete nf2;
	return res;

}

void NormalForm::remove_redundant_clauses(set<Clause*>* clauses)
{
	set<Clause*>::iterator it1 = clauses->begin();
	set<Clause*> to_delete;
	for(; it1!= clauses->end(); it1++)
	{
		set<Clause*>::iterator it2 = clauses->begin();
		for(;it2!=clauses->end(); it2++)
		{
			Clause *c1 =  *it1;
			Clause *c2 =  *it2;
			if(c1 == c2)
				continue;
			if(c1->subsumes(*c2)){
				to_delete.insert(c2);
				cout << "error 3" << endl;
			}
			else if(c2->subsumes(*c1)){
				to_delete.insert(c1);
				cout << "error 4" << endl;
			}
		}
	}
	it1 = to_delete.begin();
	for(; it1!= to_delete.end(); it1++){
		clauses->erase(*it1);
		delete *it1;
	}

}

set<Clause* >* NormalForm::product_clauses(
		set<Clause*  >* nf1, set<Clause*  >* nf2)
{
	set<Clause* >* res = new set<Clause*  >();
	set<Clause*>::iterator it1 = nf1->begin();
	for(; it1 != nf1->end(); it1++){
		set<Clause*  >::iterator it2 = nf2->begin();
		for(; it2 != nf2->end(); it2++){
			Clause* inner = combine_clauses(*it1, *it2);
			if(inner == NULL) continue;
			res->insert(inner);
		}
	}
	delete_nf(nf1);
	delete_nf(nf2);
	remove_redundant_clauses(res);
	return res;
}



/*
 * Returns the combination of the sets, NULL if the combination is
 * redundant. While combining the two clauses, it also removes any
 * redundant literals.
 */
Clause* NormalForm::combine_clauses(Clause* clause1,
		Clause* clause2)
{
	Clause* res = new Clause();
	res->pos_eq.insert(clause1->pos_eq.begin(), clause1->pos_eq.end());
	res->pos_eq.insert(clause2->pos_eq.begin(), clause2->pos_eq.end());

	res->neg_eq.insert(clause1->neg_eq.begin(), clause1->neg_eq.end());
	res->neg_eq.insert(clause2->neg_eq.begin(), clause2->neg_eq.end());

	res->pos_ilp.insert(clause1->pos_ilp.begin(), clause1->pos_ilp.end());
	res->pos_ilp.insert(clause2->pos_ilp.begin(), clause2->pos_ilp.end());

	res->neg_ilp.insert(clause1->neg_ilp.begin(), clause1->neg_ilp.end());
	res->neg_ilp.insert(clause2->neg_ilp.begin(), clause2->neg_ilp.end());

	res->pos_universal.insert(clause1->pos_universal.begin(),
			clause1->pos_universal.end());
	res->pos_universal.insert(clause2->pos_universal.begin(),
			clause2->pos_universal.end());

	res->neg_universal.insert(clause1->neg_universal.begin(),
			clause1->neg_universal.end());
	res->neg_universal.insert(clause2->neg_universal.begin(),
			clause2->neg_universal.end());



	if(res->drop_clause())
	{
		cout << "error 5" << endl;
		delete res;
		return NULL;
	}

	return res;
}


bool NormalForm::is_outer_connective(cnode_type kind)
{
	if(is_dnf && kind == OR) return true;
	if(!is_dnf && kind == AND) return true;
	return false;
}

string NormalForm::to_string(VarMap& vm)
{
	string res;
	string outer_connective = is_dnf ? " | " : " & ";
	string inner_connective = is_dnf ? " & " :" | ";
	set<Clause*>::iterator it1 = clauses->begin();
	unsigned int i = 0;
	for(; it1 != clauses->end(); it1++, i++){
		res+="(";
		res+= (*it1)->to_string(inner_connective);

		res+=")";
		if(i!=clauses->size()-1) res += outer_connective;
	}
	return res;
}

void NormalForm::delete_nf(set<Clause*>* nf)
{
	set<Clause*>::iterator it = nf->begin();
	for(; it!= nf->end(); it++){
		delete *it;
	}
	delete nf;
}

set<Clause* >* NormalForm::get_clauses()
{
	return clauses;
}

CNode* NormalForm::get_constraint_from_clause(Clause *c, bool use_and)
{
	set<CNode*> operands;
	operands.insert(c->pos_eq.begin(), c->pos_eq.end());
	set<EqLeaf*>::iterator it = c->neg_eq.begin();
	for(; it!= c->neg_eq.end(); it++)
	{
		EqLeaf* cur = *it;
		CNode *n = Connective::make_not(cur);
		operands.insert(n);
	}
	operands.insert(c->pos_ilp.begin(), c->pos_ilp.end());
	set<ILPLeaf*>::iterator it2 = c->neg_ilp.begin();
	for(; it2!= c->neg_ilp.end(); it2++)
	{
		ILPLeaf* cur = *it2;
		CNode *n = Connective::make_not(cur);
		operands.insert(n);
	}
	operands.insert(c->pos_universal.begin(), c->pos_universal.end());
	set<QuantifiedLeaf*>::iterator it3 = c->neg_universal.begin();
	for(; it3!= c->neg_universal.end(); it3++)
	{
		QuantifiedLeaf* cur = *it3;
		CNode *n = Connective::make_not(cur);
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

CNode* NormalForm::get_constraint()
{


	set<CNode*> operands;
	set<Clause* >::iterator it = clauses->begin();
	for(; it != clauses->end(); it++)
	{
		CNode * inner = get_constraint_from_clause(*it, is_dnf);
		operands.insert(inner);
	}
	CNode* outer = NULL;
	if(is_dnf) {
		outer = Connective::make_or(operands, false);
	}
	else {
		outer = Connective::make_and(operands, false);
	}

	return outer;

}


/*
 * Normal forms don't own their leaf nodes; the
 * corresponding CNode is the owner of the leaves.
 */
NormalForm::~NormalForm() {
	delete_nf(clauses);
}

// ---------------------------------------------------

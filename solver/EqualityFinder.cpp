/*
 * EqualityFinder.cpp
 *
 *  Created on: Mar 15, 2009
 *      Author: isil
 */

#include "EqualityFinder.h"
#include "cnode.h"
#include "term.h"
#include "Clause.h"
#include "ClauseSolve.h"
#include "VariableEliminator.h"
#include "ExistentialEliminator.h"
#include "mistral.h"
#include <algorithm>
#define ASSERT_ENABLED true

EqualityFinder::EqualityFinder(CNode* node, Term* var,
		bool find_disjunctive_eqs)
{
	this->node = node;
	this->var = var;
	this->disjunctive = find_disjunctive_eqs;
	this->no_equality = false;
	find_equalities(node, True::make(), equalities);

}

const set<Term*> & EqualityFinder::get_equalities()
{
	assert(!disjunctive);
	return equalities;
}

const map<Term*, CNode*>& EqualityFinder::get_disjunctive_equalities()
{
	assert(disjunctive);
	return disjunctive_equalities;
}

inline void EqualityFinder::process_equality_for_disjunct(CNode* disjunct,
		set<Term*>&
		cur_equalities)
{
	if(!disjunctive) return;
	/*
	 * At least one child is not equal to anything
	 */
	if(cur_equalities.size() == 0)
	{
		this->disjunctive_equalities.clear();
		return;
	}
	Term* eq = *cur_equalities.begin();
	map<Term*, Term*> subs;
	subs[var] = eq;
	CNode* constraint = disjunct->substitute(subs);
	if(disjunctive_equalities.count(eq) == 0) {
		disjunctive_equalities[eq] = constraint;
	}
	else {
		CNode* existing = disjunctive_equalities[eq];
		CNode* new_c = Connective::make(OR, existing, constraint);
		disjunctive_equalities[eq] = new_c;
	}

}
inline void EqualityFinder::add_to_disjunctive_equalities(Term* t,
		CNode* constraint)
{
	if(disjunctive_equalities.count(t) == 0) {
		disjunctive_equalities[t] = constraint;
	}
	else {
		CNode* old_constraint = disjunctive_equalities[t];
		CNode* new_constraint = Connective::make(OR, old_constraint,
				constraint);
		disjunctive_equalities[t] = new_constraint;

	}
}

void EqualityFinder::add_to_disjunctive_equalities(map<Term*, CNode*>& eqs)
{
	map<Term*, CNode*>::iterator it = eqs.begin();
	for(; it!= eqs.end(); it++)
	{
		add_to_disjunctive_equalities(it->first, it->second);
	}
}

void EqualityFinder::find_equalities(CNode* cur, CNode* active_constraint,
		set<Term*>& cur_equalities)
{
	/*
	 * Base case: cur & active_constraint are conjuncts
	 */
	if(cur->is_conjunct() && active_constraint->is_conjunct())
	{
		CNode* and_c = Connective::make(AND, cur, active_constraint);
		if(!disjunctive) {
			find_equalities_conjunct(and_c, cur_equalities);
		}
		else {
			set<Term*> eqs;
			find_equalities_conjunct(and_c, eqs);
			if(eqs.size() == 0) {
				no_equality = true;
				return;
			}

			/*
			 * Prefer constants and variables over other ones.
			 */
			ConstantTerm* ct = NULL;
			VariableTerm* vt = NULL;
			set<Term*>::iterator it = eqs.begin();
			for(; it!= eqs.end(); it++)
			{
				Term* cur = *it;
				term_type tt = cur->get_term_type();
				if(tt == CONSTANT_TERM) {
					ct = (ConstantTerm*)cur;
					break;
				}
				if(tt == VARIABLE_TERM) {
					vt = (VariableTerm*) cur;
				}
			}

			Term* t = *eqs.begin();
			if(ct != NULL) t = ct;
			else if(vt != NULL) t= vt;
			map<Term*, Term*> subs;
			subs[var] = t;
			CNode* constraint = and_c->substitute(subs);
			add_to_disjunctive_equalities(t, constraint);

		}
		return;
	}

	/*
	 * Pseudo base case: cur is conjunct, but not active constraint
	 */
	if(cur->is_conjunct())
	{
		CNode* and_c = Connective::make(AND, cur, active_constraint);
		find_equalities(and_c, True::make(), cur_equalities);
		return;
	}


	if(cur->get_type() == OR)
	{

		Connective* or_c = (Connective*) cur;
		const set<CNode*>& children = or_c->get_operands();
		CNode* first = *children.begin();
		if(ASSERT_ENABLED) assert(children.size() >=1);
		find_equalities(first, active_constraint, cur_equalities);
		if(no_equality) return;

		set<CNode*>::const_iterator it = children.begin();
		it++;
		for(; it!=children.end(); it++)
		{
			set<Term*> intersection;
			set<Term*> child_eqs;
			find_equalities(*it, active_constraint, child_eqs);
			if(no_equality) return;
			if(disjunctive) continue;
			set_intersection(cur_equalities.begin(), cur_equalities.end(),
					child_eqs.begin(), child_eqs.end(),
					insert_iterator<set<Term*> >(intersection,
							intersection.begin()));

			cur_equalities = intersection;

		}
		return;

	}

	if(cur->get_type() == AND)
	{
		Connective* and_c = (Connective*) cur;
		const set<CNode*>& children = and_c->get_operands();

		CNode* or_child = NULL;
		CNode* new_active = active_constraint;

		/*
		 * Optimization: If there are any non-or children that contain
		 * equalities, we don't want to go down the disjunct.
		 */
		set<CNode*> literal_children;
		set<CNode*>::const_iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* child = *it;
			if(child->get_type() == OR) continue;
			literal_children.insert(child);
		}
		CNode* opt_node = Connective::make_and(literal_children);
		EqualityFinder ef(opt_node, var, disjunctive);
		if(!ef.no_equality) {
			if(disjunctive)
			{
				add_to_disjunctive_equalities(ef.disjunctive_equalities);
			}
			else
			{
				cur_equalities.insert(ef.equalities.begin(), ef.equalities.end());
			}
			return;
		}



		it = children.begin();
		for(; it!=children.end(); it++)
		{
			CNode* cur_child = *it;
			if(or_child == NULL && cur_child->get_type() == OR)
			{
				or_child = cur_child;
				continue;
			}
			new_active = Connective::make(AND, cur_child, new_active);
		}
		if(ASSERT_ENABLED) assert(or_child != NULL);
		find_equalities(or_child, new_active, cur_equalities);
		return;
	}



	assert(false);
}

void EqualityFinder::find_equalities_conjunct(CNode* c,
						set<Term*>& cur_eqs)
{

	if(!c->contains_term(var)) return;
	c->collect_term_equalities(var, cur_eqs);
	Clause cl(c);
	map<Term*, Term*> denestings;
	cl.denest( &denestings);

	ClauseSolve cs(&cl, NULL);
	bool res = cs.is_sat();
	if(!res){
		return;
	}
	Term* rep = cs.find_representative(var);

	if(rep != NULL){
		set<Term*> & eq_class = cs.eq_members[rep];
		cur_eqs.insert(eq_class.begin(), eq_class.end());
		cur_eqs.erase(var);
	}

	if(var->get_term_type() != VARIABLE_TERM) return;

	VariableTerm* vt = (VariableTerm*) var;


	VariableEliminator ve_nc(c, vt, UNSAT_SIMPLIFY, true, true);
	VariableEliminator ve_sc(c, vt, UNSAT_SIMPLIFY, false, true);


	CNode* nc = ve_nc.get_result();
	CNode* sc = ve_sc.get_result();
	if(nc != sc){
		if(ASSERT_ENABLED){

			bool implied = implies(nc, sc);
			if(!implied) return;
			assert(!implies(sc, nc));
		}
		return;
	}
	const map<VariableTerm*, set<pair<Term*, Term*>  > >& new_inequalities =
		ve_nc.get_new_inequalities();

	if(new_inequalities.count(vt) == 0){
		return;
	}
	const set<pair<Term*, Term*> > & sandwich_pairs =
		new_inequalities.find(vt)->second;
	set<pair<Term*, Term*> >::const_iterator it = sandwich_pairs.begin();
	for(; it!= sandwich_pairs.end(); it++)
	{
		Term* lhs = it->first;
		Term* rhs = it->second;
		CNode* eq = EqLeaf::make(lhs, rhs);
		if(implies(c, eq)) {
			cur_eqs.insert(lhs);
			cur_eqs.insert(rhs);
		}

	}
	set<Term*>::iterator it2 = cur_eqs.begin();
	set<Term*> renamed_eqs;
	for(; it2!=cur_eqs.end(); it2++)
	{
		Term* t = *it2;
		renamed_eqs.insert(t->substitute(denestings));
	}
	cur_eqs = renamed_eqs;



}

bool EqualityFinder::implies(CNode* c1, CNode* c2)
{
	//c1 &!c2 has to be unsat
	CNode *res = Connective::make(AND, c1, Connective::make_not(c2));
	Solver s(res, UNSAT_SIMPLIFY);
	return s.get_result()->get_type() == FALSE_NODE;
}

EqualityFinder::~EqualityFinder() {

}

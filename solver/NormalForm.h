/*
 * NormalForm.h
 *
 *  Created on: Sep 2, 2008
 *      Author: tdillig
 */

#ifndef NORMALFORM_H_
#define NORMALFORM_H_

#include <set>
#include <map>
#include <string>
using namespace std;
#include "EqLeaf.h"
#include "ILPLeaf.h"
#include "CNode.h"
#include "Leaf.h"
#include "QuantifiedLeaf.h"
#include "Clause.h"
class Leaf;
class VarMap;
class Connective;
class NodeMap;

#include <iostream>
using namespace std;



/*
 * Normal form can be used to convert constraints to
 * DNF or CNF. The constructor assumes negations have been
 * pushed in.
 *
 * To efficiently simplify the formulas while converting to
 * normal form, leaves need to be shared. This is because to
 * check contradictions and tautologies, we keep leaves in two different
 * sets neg_leaf and pos_leaf according to their phase and
 * check for set intersection. If the set intersection is non-empty
 * we can detect contradictions (in DNF) and tautologies (in CNF).
 * Having a shared leaf representation is crucial for
 * detecting contradictions and tautologies efficiently
 * without resorting to deep equality checks.
 *
 * In addition, we check whether any of the outer clauses subsume
 * one another to avoid entire redundant clauses.
 */
class NormalForm {
private:
	set<Clause* >* clauses;
	bool is_dnf; // cnf if false
public:

	/*
	 * The constructor assumes negations have been pushed in.
	 */
	NormalForm(CNode* n, bool is_dnf);
	set<Clause* >* get_clauses();
	string to_string(VarMap& vm);

	/*
	 * Returns a fresh constraint from the normal form
	 * representation -- Must be deleted by whoever
	 * captures its return value.
	 */
	CNode* get_constraint();
	static CNode* get_constraint_from_clause(Clause *c, bool use_and);
	virtual ~NormalForm();
private:
	set<Clause* >* make_normal_form(CNode* n);
	bool is_outer_connective(cnode_type kind);
	Clause* combine_clauses(Clause* clause1, Clause* clause2);
	set<Clause* >* product_clauses(set<Clause* >* nf1,
			set<Clause* >* nf2);
	void delete_nf(set<Clause*>* nf);
	set<Clause* >* add_clauses(set<Clause* >* nf1,
			set<Clause*>* nf2);
	void remove_redundant_clauses(set<Clause*>* clauses);

};

#endif /* NORMALFORM_H_ */

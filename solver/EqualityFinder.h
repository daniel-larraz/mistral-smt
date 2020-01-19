/*
 * EqualityFinder.h
 *
 *  Created on: Mar 15, 2009
 *      Author: isil
 */


#ifndef EQUALITYFINDER_H_
#define EQUALITYFINDER_H_

#include <map>
#include <set>
#include <string>

using namespace std;
class Term;
class CNode;

/*
 * Inference of equalities implied by this constraint.
 * Currently, we infer only non-disjunctive equalities, but
 * we could very easily extend this to return disjunctive equalities as
 * well. The inference is sound & complete -- all equalities it finds
 * are actually implied and it is guaranteed to find all equalities
 * implied by the CNode* node.
 */
class EqualityFinder {
private:
	set<Term*> equalities;
	map<Term*, CNode*> disjunctive_equalities;
	CNode* node;
	Term* var;
	bool disjunctive;
	bool no_equality;

public:
	EqualityFinder(CNode* node, Term* var, bool find_disjunctive_eqs);
	const set<Term*> & get_equalities();
	const map<Term*, CNode*>& get_disjunctive_equalities();
	~EqualityFinder();
private:
	void find_equalities(CNode* cur, CNode* active_constraint,
			set<Term*>& cur_equalities);
	void find_disjunctive_equalities(CNode* cur, CNode* active_constraint,
			map<Term*, CNode*>& cur_equalities);
	void find_equalities_conjunct(CNode* c, set<Term*>& cur_eqs);
	inline void process_equality_for_disjunct(CNode* disjunct,
			set<Term*>& cur_equalities);
	bool implies(CNode* c1, CNode* c2);
	void add_to_disjunctive_equalities(map<Term*, CNode*>& eqs);
	inline void add_to_disjunctive_equalities(Term* t, CNode* constraint);
};

#endif /* EQUALITYFINDER_H_ */

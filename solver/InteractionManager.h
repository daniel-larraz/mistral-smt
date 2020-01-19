/*
 * ComparableTerms.h
 *
 *  Created on: Sep 6, 2008
 *      Author: tdillig
 */

#ifndef INTERACTIONMANAGER_H_
#define INTERACTIONMANAGER_H_

#include <map>
#include <set>
#include <vector>
#include <iostream>
#include "bignum.h"
using namespace std;

#include "Term.h"
class ClauseSolve;
class FunctionTerm;
class VarMap;
class EqLeaf;
class Matrix;
class Equation;
class VariableTerm;

class TermComparator {
private:
	Term* find_representative(Term* t)
	{
		while(t!=t->representative)
		{
			if(t->representative == NULL) return t;
			t = t->representative;
		}
		return t;
	}

public:
    bool operator()(const Term* const & _q1, const Term* const & _q2)
    {
    	Term* t1 = (Term*&)_q1;
    	Term* t2 = (Term*&)_q2;
    	Term* rep1 = find_representative(t1);
    	Term* rep2 = find_representative(t2);
    	return rep1<rep2;
    }

};

/*
 * Represents a set of ILP queries that need to be
 * made in order to merge equaivalence classes
 * class1 and class2. An ILP query with terms t1 and t2
 * represents the query t1 = t2
 * that will allow equivalence classes of t1 and t2
 * to merge.
 */
class ILPQuery {
public:
	ILPQuery(Term* rhs, Term* lhs);
	string to_string();
	Term* t1;
	Term* t2;
};

class InteractionManager {
private:
	ClauseSolve* s;

	/*
	 * A set of ILP queries we need to make (in the worst case)
	 * until the decision procedure can decide SAT or UNSAT.
	 */
	set<ILPQuery*> queries;

	set<Term*> representatives;
	set<EqLeaf*>& inequalities;
	map<Term*, set<Term*> >& eq_members;
	map<Term*, int >& eq_size;
	map<Term*, int> eq_constants;


	/*
	 * Existing (i.e., already known) equalities and inequalities.
	 * Note that inequalities are represented as a set of sets because the
	 * inner set corresponds to a disjunction of inequalities obtained from
	 * e.g., f(a, b)!= f(c,d) -> a!=c | b!=d.
	 */
	set<pair<Term*, Term*> > existing_equalities;
	set< set<pair<Term*, Term*> > > existing_inequalities;

public:
	InteractionManager(ClauseSolve* s,
			set<Term*> & equality_terms,
			set<int>& function_terms);
	virtual ~InteractionManager();
	bool add_inferred_equalities();
	bool add_inferred_inequalities();

	/*
	 * Queries should be built once the initial set of implied
	 * equalities and inequalities are added.
	 */
	void build_queries();

	set<ILPQuery*> & get_queries();
	set<ILPQuery*> & refine_queries();
	string queries_to_string();
private:
	bool add_inequality(Term* lhs, Term* rhs);


	Term* get_shared_member(VariableTerm* vt);
	bool eq_class_contains_fn_term(Term* t);

	/*
	 * Makes a canonical pair such that if we call
	 * make_term_pair(t1, t2) and make_term_pair(t2, t1),
	 * we get the same pair back.
	 */
	inline pair<Term*, Term*> make_term_pair(Term* t1, Term* t2);

	void get_inferred_equalities(set<Term*>& relevant_classes,
			set<pair<Term*, Term*> >& inferred_eqs);
	void get_inferred_inequalities(set<Term*>& relevant_classes,
			set<pair<Term*, Term*> >& inferred_ineqs);

	/*
	 * Are the given pair of relevant congruence classes relevant for making a
	 * query? A pair of classes is relevant to a query if their union
	 * can either (a) result in a contradiction, (b) may lead to
	 * inference of equalities between ilp variables, and (c) may
	 * lead to inference of disequalities between ilp variables.
	 */
	inline bool is_relevant_pair(Term* t1, Term* t2);

	/*
	 * A term is relevant to the ilp domain if it's either a constant
	 * or a variable used in the ilp domain.
	 */
	inline bool is_relevant_term_to_ilp_domain(Term* t);

	/*
	 * Add the query t1 = t2? to the set of queries after doing
	 * some redundancy checks.
	 */
	inline void add_query(Term* t1, Term* t2);





	void find_disequality_terms(Term* t1, Term* t2,
			set<pair<Term*, Term*> >& terms);
	void find_disequality_terms_internal(Term* t1, Term* t2,
			set<pair<Term*, Term*> >& terms,
			map<pair<Term*, Term*>, set<pair<Term*, Term*> > >& visited,
			bool check_visited);

	void add_disequality(Term* t1, Term* t2,
			set<pair<Term*, Term*> >& to_add);



};

#endif /* INTERACTIONMANAGER_H_ */

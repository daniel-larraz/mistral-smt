/*
 * ExistentialEliminator.h
 *
 *  Created on: Nov 26, 2011
 *      Author: isil
 */

#ifndef EXISTENTIALELIMINATOR_H_
#define EXISTENTIALELIMINATOR_H_

#include <map>
#include <set>
using namespace std;

class CNode;
class Term;
class FunctionTerm;

class ExistentialEliminator {
private:
	CNode* c;
	Term* elim_t;
	CNode* result;
	bool overapprox;

	bool simplify;


	/*
	 * For each function id, this map contains another map
	 * from function terms containing x (var to be eliminated)
	 * to a fresh variable that we will replace this function term with.
	 */
	map<int, map<Term*, Term*> > function_terms_to_vars;

	/*
	 * Additional terms to eliminate caused by replacing
	 * function terms with variables
	 */
	set<Term*> new_elim_terms;

	/*
	 * A map from function identifiers to function terms
	 * with this identifier.
	 */
	map<int, set<Term*> > function_ids_to_terms;


public:
	ExistentialEliminator(CNode* c, Term* t, bool overapproximation);
	CNode* get_result();
	~ExistentialEliminator();

private:
	CNode* eliminate_existential(CNode* c);

	/*
	 * Populates the map function_terms_to_vars and new_elim_terms,
	 * and returns a new constraint where function terms containing elim_t
	 * are replaced with a fresh variable term.
	 */
	CNode* collect_function_terms_containing_elim_t(CNode* c);

	/*
	 * Populates the function_ids_to_terms map.
	 */
	void build_map_from_fun_id_to_terms(CNode* c);


	CNode* get_functional_consistency_axioms();

	/*
	 * Generates a constraint stating that the arguments of ft1 and ft2 are equal.
	 */
	CNode* args_equal(FunctionTerm* ft1, FunctionTerm* ft2);

	bool contained_in_function_term(CNode* c, Term* t);

	CNode* replace_elim_t_in_function(CNode* c, Term* elim_t);

	CNode* find_disjunctive_equalities(CNode* c, Term* elim_t,
				bool parent_conjunct);

};

#endif /* EXISTENTIALELIMINATOR_H_ */

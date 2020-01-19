/*
 * MinPrimeImplicant.h
 *
 *  Created on: Nov 18, 2011
 *      Author: isil
 */

#ifndef MINPRIMEIMPLICANT_H_
#define MINPRIMEIMPLICANT_H_

#include <map>
#include <set>
#include "SatValue.h"
using namespace std;

class CNode;
class VariableTerm;
class BooleanVar;
class Term;

class MinPrimeImplicant {
private:
	CNode* orig_constraint;
	CNode* constraint;
	map<VariableTerm*, int>& costs;
	map<CNode*, BooleanVar*> literal_to_bool;
	map<Term*, Term*> vars_to_cost_vars;
	int min_cost;
	int max_cost;
	map<Term*, SatValue> min_assignment;
	Term* opt_function;
	set<CNode*>& background;
	Term* bg_violated_cost_var;


public:
	/*
	 * Finds variables in the minimum prime implicant of c consistent
	 * with background.
	 */
	MinPrimeImplicant(CNode* c, set<CNode*>& background,
			map<VariableTerm*, int>& costs);
	int get_cost();
	const map<Term*, SatValue>& get_min_assignment();
	~MinPrimeImplicant();

private:
	void build_boolean_abstraction();
	void add_theory_constraints();
	void add_cost_constraints();
	void add_background_constraints();
	void init_opt_function();
	void init_upper_bound();
	void init_max_cost();

};

#endif /* MINPRIMEIMPLICANT_H_ */

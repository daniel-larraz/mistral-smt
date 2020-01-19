/*
 * Clause.h
 *
 *  Created on: Feb 8, 2009
 *      Author: tdillig
 */

#ifndef CLAUSE_H_
#define CLAUSE_H_
#include <set>
#include <map>
#include <string>
using namespace std;

class EqLeaf;
class ILPLeaf;
class QuantifiedLeaf;
class CNode;
class Term;
class Leaf;
class ModLeaf;

class Clause {
public:
	set<EqLeaf*> pos_eq;
	set<EqLeaf*> neg_eq;
	set<ILPLeaf*> pos_ilp;
	set<ILPLeaf*> neg_ilp;
	set<ModLeaf*> pos_mod;
	set<ModLeaf*> neg_mod;
	set<QuantifiedLeaf*> pos_universal;
	set<QuantifiedLeaf*> neg_universal;

	/*
	 * A mapping from old terms to new their denesting variables
	 * We use this map to avoid introducing redundant variables.
	 */
	map<Term*, Term*> reverse_denestings;


public:
	Clause();
	Clause(CNode* node);

	/*
	 * Returns true if this clause subsumes other.
	 */
	bool subsumes(Clause & other);

	/*
	 * Checks whether this clause has an obvious tautology or
	 * contradiction
	 */
	bool drop_clause();

	string to_string(string c);

	/*
	 * Converts clause to CNode.
	 */
	CNode* to_cnode(bool use_and = true);




	/*
	 * Introduces temporaries to ensure function terms do not
	 * contain arithmetic terms.
	 */
	void denest(map<Term*, Term*>* denestings = NULL);

	virtual ~Clause();
private:
	void add_literal(CNode* leaf);
	Term* denest_term(Term* t, set<CNode*>& to_add, int& counter,
			map<Term*, Term*>* denestings, bool denest_arithmetic,
			bool denest_function);
	CNode* denest_leaf(Leaf* l, set<CNode*>& to_add, int& counter,
			map<Term*, Term*>* denestings);
	void make_false();

};

#endif /* CLAUSE_H_ */

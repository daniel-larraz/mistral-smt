/*
 * CNF.h
 *
 *  Created on: Jul 25, 2009
 *      Author: tdillig
 */

#ifndef CNF_H_
#define CNF_H_

#include "SatSolver.h"
#include "Vec.h"
#include <set>
#include <map>
#include <string>

class CNode;
class Leaf;

using namespace std;

class CNF {
private:
	set<vec<minisat::Lit>* >  cnf;
	map<CNode*, minisat::Var> node_to_var_map;
	map<minisat::Var, CNode*> var_to_node_map;

public:
	CNF(CNode* node, minisat::Solver& s);
	~CNF();
	vec<minisat::Lit>* add_clause(CNode* clause, minisat::Solver& s);
	void and_cnf(CNF& other);
	string to_string();
	set<vec<minisat::Lit>* > & get_cnf();
	Leaf* get_leaf_from_literal(minisat::Var l);
	void and_node(CNode* node, minisat::Solver& s);
	map<minisat::Var, CNode*>& get_var_to_node_map();
private:
	minisat::Lit make_cnf_rec(minisat::Solver& s,
			CNode* node,  bool insert_literal);


};

#endif /* CNF_H_ */

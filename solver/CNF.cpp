/*
 * CNF.cpp
 *
 *  Created on: Jul 25, 2009
 *      Author: tdillig
 */

#include "CNF.h"
#include "cnode.h"
#include "util.h"

CNF::CNF(CNode* node, minisat::Solver& s)
{
	if(node->get_type() != OR)
	{
		minisat::Lit outer = make_cnf_rec(s, node,  true);
		vec<minisat::Lit>* v = new vec<minisat::Lit>();
		v->push(outer);
		cnf.insert(v);
	}

	else
	{
		Connective* or_c = (Connective*) node;
		const set<CNode*>& ops = or_c->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		vec<minisat::Lit>* v = new vec<minisat::Lit>();
		for(; it!=ops.end(); it++)
		{
			CNode* child = *it;
			minisat::Lit child_lit = make_cnf_rec(s, child, false);
			v->push(child_lit);
		}
		cnf.insert(v);
	}

}

void CNF::and_cnf(CNF& other)
{
	set<vec<minisat::Lit>*>& other_clauses = other.get_cnf();
	set<vec<minisat::Lit>*>::iterator it = other_clauses.begin();
	for(; it != other_clauses.end(); it++)
	{
		this->cnf.insert(*it);
	}

	map<CNode*, minisat::Var>::iterator it2 =  other.node_to_var_map.begin();
	for(; it2!= other.node_to_var_map.end(); it2++)
	{
		CNode* n = it2->first;
		this->node_to_var_map[n] = it2->second;
	}
	map<minisat::Var, CNode*>::iterator it3 =  other.var_to_node_map.begin();
	for(; it3!= other.var_to_node_map.end(); it3++)
	{
		this->var_to_node_map[it3->first] = it3->second;
	}
}

map<minisat::Var, CNode*>& CNF::get_var_to_node_map()
{
	return var_to_node_map;
}

vec<minisat::Lit>* CNF::add_clause(CNode* clause, minisat::Solver& s)
{
	assert(clause->is_disjunct());
	Connective* disjunct = (Connective*) clause;
	set<CNode*>::const_iterator it = disjunct->get_operands().begin();
	vec<minisat::Lit>* v = new vec<minisat::Lit>();
	for(; it!= disjunct->get_operands().end(); it++)
	{
		CNode* lit = *it;
		v->push(make_cnf_rec(s, lit, true));

	}
	return v;
}


void CNF::and_node(CNode* node, minisat::Solver& s)
{
	minisat::Lit outer = make_cnf_rec(s, node,  true);
	vec<minisat::Lit>* v = new vec<minisat::Lit>();
	v->push(outer);
	cnf.insert(v);
}

minisat::Lit CNF::make_cnf_rec(minisat::Solver& s,
		CNode* node,  bool insert_literal)
{
	assert(node->get_type() != TRUE_NODE);
	assert(node->get_type() != FALSE_NODE);

	/*
	 * If this is a negation, set node to be the inner leaf.
	 */
	bool is_neg = (node->get_type() == NOT);
	if(is_neg){
		node = *((Connective*) node)->get_operands().begin();
	}

	minisat::Var my_id;
	if(node_to_var_map.count(node) > 0) {
		my_id = node_to_var_map[node];
	}
	else {
		my_id = s.newVar();
		node_to_var_map[node] = my_id;
		var_to_node_map[my_id] = node;
	}

	/*
	 * If the node is a leaf or negation, insert it into its own clause
	 * and return its id.
	 */

	if(node->is_literal())
	{
		minisat::Lit l(my_id, is_neg);
		if(!insert_literal) return l;
		vec<minisat::Lit>* v = new vec<minisat::Lit>();
		v->push(l);
		cnf.insert(v);
		return l;
	}

	// AND and OR case
	minisat::Lit my_lit(my_id, false);
	minisat::Lit my_lit_neg(my_id, true);

	/*
	 * OR case
	 */
	if(node->get_type() == OR)
	{
		vec<minisat::Lit>* v = new vec<minisat::Lit>();
		v->push(my_lit_neg);
		Connective* c = (Connective*) node;
		const set<CNode*>& children = c->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!=children.end(); it++)
		{
			CNode* child = *it;
			minisat::Lit child_lit = make_cnf_rec(s, child, false);
			v->push(child_lit);

		}
		cnf.insert(v);
		return my_lit;


	}

	assert(node->get_type() == AND);
	Connective* and_c = (Connective*) node;
	const set<CNode*>& children = and_c->get_operands();
	set<CNode*>::iterator it = children.begin();
	for(; it!= children.end(); it++)
	{
		CNode* child = *it;
		minisat::Lit child_lit = make_cnf_rec(s, child, false);
		vec<minisat::Lit>* v = new vec<minisat::Lit>();
		v->push(my_lit_neg);
		v->push(child_lit);
		cnf.insert(v);
	}
	return my_lit;




}

string CNF::to_string()
{
	string res;
	set<vec<minisat::Lit>*>::iterator it = cnf.begin();
	int i=0;
	for(; it!= cnf.end(); it++, i++)
	{
		res += "(";
		vec<minisat::Lit>* v = *it;
		int size = v->size();
		for(int j=0; j<size; j++)
		{
			minisat::Lit l = (*v)[j];
			string var;
			if(minisat::sign(l)) var += "~";
			var += "x" + int_to_string(minisat::var(l));
			res += var;
			if(j!=size-1) res += " | ";
		}
		res += ")";
		if(i!= (int)cnf.size() -1) res += " & ";


	}
	return res;
}
set<vec<minisat::Lit>* > & CNF::get_cnf()
{
	return cnf;
}

Leaf* CNF::get_leaf_from_literal(minisat::Var l)
{
	if(var_to_node_map.count(l) == 0) return NULL;
	CNode* node = var_to_node_map[l];
	if(node->is_leaf()) return (Leaf*)node;
	return NULL;

}

CNF::~CNF()
{
	set<vec<minisat::Lit>* >::iterator it = cnf.begin();
	for(; it != cnf.end(); it++)
	{
		delete *it;
	}
}

/*
 * Solver.cpp
 *
 *  Created on: Sep 5, 2008
 *      Author: tdillig
 */

#include "Solver.h"
#include "NormalForm.h"
#include "mistral.h"
#include "VarMap.h"
#include "cnode.h"
#include "term.h"
#include <assert.h>


#include "time.h"
#include "UniversalInstantiator.h"
#include "UnsatCoreFinder.h"
#include "BooleanAbstractor.h"
#include "CNF.h"
#include "DPLLSolver.h"
#include "Simplifier.h"
#include "ConflictDatabase.h"
#include <fstream>

#define DEBUG false

#define COLLECT_CONSTRAINTS false
#define CONSTRAINT_COLLECT_PATH "/home/isil/constraints/"


Solver::Solver()
{
	res = NULL;
	fresh_var_counter = 0;
	solve_count = 0;
	literal_count = 0;
	clause_cache_hit_count = 0;
	cache_hits = 0;
	solve_time = 0;
	imply_time = 0;
	num_imply = 0;
}



Solver::Solver(CNode* node, simplification_level level,
		map<Term*, SatValue>* assignments, bool use_dnf)
{

	/*
	 * First, check the cache
	 */
	CNode* simp = node->get_simplification(level);
	if(simp != NULL && assignments == NULL) {
		res = simp;
		return;
	}



	/*
	 * Get attributes on the terms
	 */
	CNode* term_attribs = node->get_attribute_constraints();


	CNode* node_and_attribs = Connective::make(AND, node, term_attribs);

	if(use_dnf)
	{
		bool sat = this->dnf_solve(node_and_attribs, assignments);
		if(sat) {
			res = node;
			node->set_simplification(node, UNSAT_SIMPLIFY);
		}
		else {
			res = False::make();
			node->set_simplification(res, THEORY_SIMPLIFY);
		}

		return;
	}

	BooleanAbstractor ba(node_and_attribs);

	//cout << "BA learned inplications: "
	//		<< ba.get_learned_implications()->to_string() << endl;

	set<CNode*> learned;
	ConflictDatabase::get_conflict_clauses(node_and_attribs, learned);
	learned.insert(ba.get_learned_implications());
	CNode* learned_node = Connective::make_and(learned);

	set<Term*> ilp_terms;
	//node->get_all_ilp_terms(ilp_terms);

	DPLLSolver s(learned_node, ilp_terms, assignments);
	s.restrict(term_attribs);

	//cout << "Implications learned from boolean abstractor: " <<
		//ba.get_learned_implications()->to_string() << endl;
	s.push(node);


	bool sat = s.is_sat();


	if(COLLECT_CONSTRAINTS)
	{
		collect_constraint(node, sat, CONSTRAINT_COLLECT_PATH);
	}


	s.pop();


	if(!sat) {
		res =  False::make();
		node->set_simplification(res, THEORY_SIMPLIFY);
		return;
	}
	if(level == UNSAT_SIMPLIFY){
		res = node;
	}
	else if(level == BOOLEAN_SIMPLIFY)
	{
		CNode* background = s.get_background_assumptions();
		Simplifier simp(node, background);
		res = simp.get_simplification();
	}
	else {
		bool switch_to_boolean = (level == HYBRID_SIMPLIFY);
		Simplifier simp(node, &s, switch_to_boolean);
		res = simp.get_simplification();
	}
	node->set_simplification(res, level);



}

CNode* Solver::solve(CNode* node, CNode* assumptions, simplification_level level,
		map<Term*, SatValue>* assignments)
{
	CNode* res;
	bool can_cache = (assumptions->get_type() == TRUE_NODE);
	/*
	 * First, check the cache
	 */
	CNode* simp = node->get_simplification(level);
	if(simp != NULL && assignments == NULL) {
		node = simp;
		if(can_cache){
			//res = node;
			return node;
		}
	}

	/*
	 * Get attributes on the terms
	 */
	CNode* term_attribs = node->get_attribute_constraints();


	CNode* node_and_attribs = Connective::make(AND, node, term_attribs);
	CNode* assumption_attribs = assumptions->get_attribute_constraints();
	CNode* assumption_and_attribs = Connective::make(AND, assumptions,
			assumption_attribs);
	CNode* all = Connective::make(AND, assumption_and_attribs, node_and_attribs);
	BooleanAbstractor ba(all);
	set<CNode*> learned;
	ConflictDatabase::get_conflict_clauses(all, learned);
	learned.insert(ba.get_learned_implications());
	CNode* learned_node = Connective::make_and(learned);

	set<Term*> ilp_terms;
	//node->get_all_ilp_terms(ilp_terms);

	DPLLSolver s(learned_node, ilp_terms, assignments);
	CNode* bg = Connective::make(AND, term_attribs, assumption_and_attribs);
	s.restrict(bg);
	//cout << "Implications learned from boolean abstractor: " <<
		//ba.get_learned_implications()->to_string() << endl;
	s.push(node);


	bool sat = s.is_sat();
	if(COLLECT_CONSTRAINTS)
	{
		collect_constraint(Connective::make(AND,node, bg), sat,
				CONSTRAINT_COLLECT_PATH);
	}



	s.pop();


	if(!sat) {
		CNode* res =  False::make();
		if(can_cache) node->set_simplification(res, THEORY_SIMPLIFY);
		return res;
	}
	if(level == UNSAT_SIMPLIFY){
		res = node;
	}
	else if(level == BOOLEAN_SIMPLIFY)
	{
		CNode* background = s.get_background_assumptions();
		Simplifier simp(node, background);
		res = simp.get_simplification();
	}
	else {
		bool switch_to_boolean = (level == HYBRID_SIMPLIFY);



		Simplifier simp(node, &s, switch_to_boolean);
		res = simp.get_simplification();
	}
	if(can_cache) node->set_simplification(res, level);
	return res;
}


Solver::Solver(CNode* node, CNode* assumptions, simplification_level level,
		map<Term*, SatValue>* assignments)

{
	CNode* relevant_assumptions = get_relevant_background(assumptions, node);

	//CNode* res1 = solve(node, assumptions, level, assignments);


	CNode* res2 = solve(node, relevant_assumptions, level, assignments);

	//cout << "Reduction: " << assumptions->get_size() << " -> " <<
	//				relevant_assumptions->get_size() << endl;
	/*if(res1!=res2)
	{
		cout << "Solving formula: " << node->to_string() << endl;
		cout << "Original assumptions: " << assumptions->to_string() << endl;
		cout << "Relevant assumptions: " << relevant_assumptions->to_string() << endl;
		cout << "Reduction: " << assumptions->get_size() << " -> " <<
				relevant_assumptions->get_size() << endl;

		cout << "RES1: " << res1->to_string() << endl;
		cout << "RES2: " << res2->to_string() << endl;
		assert(false);
	}*/
	res = res2;

}

CNode* Solver::get_result()
{
	return res;
}

string Solver::get_stats()
{
	string res = "Solve time total: " + float_to_string(((double)solve_time)/
	((double)CLOCKS_PER_SEC)) + "\n";

	res+= "Clause Solve called: " + int_to_string(solve_count) + "\n";
	res+= "Clause Solve called & cache hit: " +
		int_to_string(clause_cache_hit_count) + "\n";
	res += "CNode cache hits: " + int_to_string(cache_hits) + "\n";
	res += "Clause solve with literal: " + int_to_string(literal_count) + "\n";
	res += "Num implication checks: " + int_to_string(num_imply) + "\n";
	res += "Implication time:  " + float_to_string(((double)imply_time)/
		((double)CLOCKS_PER_SEC)) + "\n";
	return res;
}



/*
 * Convert to DNF, if any clause is SAT, we return SAT.
 */
bool Solver::dnf_solve(CNode* node, map<Term*, SatValue>* assignments,
		bool verbose, bool ilp_only)
{
	if(node->get_type() == TRUE_NODE) return true;
	if(node->get_type() == FALSE_NODE) return false;

	NormalForm dnf(node, true);
	if(DEBUG || true){
		cerr << " SOLVING: " << dnf.get_constraint()->to_string() << endl;
		display("DNF for solving:\n");
		display(dnf.get_constraint()->to_string());
		display("\n");
	}

	set<Clause*>* clauses = dnf.get_clauses();
	set<Clause*>::iterator it = clauses->begin();
	for(; it!= clauses->end(); it++)
	{
		Clause* cur_clause = *it;
		CNode* node = cur_clause->to_cnode(true);
		ClauseSolve cs(node, assignments);
		if(cs.is_sat()){
			return true;
		}
	}
	return false;
}

inline void Solver::add_to_replacement_map(Term* to_replace, Term* replacement,
      map<Term*, Term*>& replacement_map)
{
   if(replacement_map.count(to_replace) > 0)
   {
       Term* rep = replacement_map[to_replace];
       if(rep->get_term_type() == CONSTANT_TERM)
           return;
   }
   replacement_map[to_replace] = replacement;

}


CNode* Solver::propagate_equalities(CNode* node,
       CNode*& active_constraint)
{



   if(node->get_type() != AND) return node;
   Connective* and_node = (Connective*) node;
   map<Term*, Term*> replacement_map;
   const set<CNode*>& children  = and_node->get_operands();
   set<CNode*>::const_iterator it = children.begin();
   for(; it!=children.end(); it++)
   {
       CNode* child = *it;
       cnode_type ct = child->get_type();
       if(ct != EQ && ct != ILP) continue;

       if(ct == EQ)
       {
           EqLeaf* eq = (EqLeaf*) child;
           Term* rhs = eq->get_rhs();
           Term* lhs = eq->get_lhs();
           if(rhs->shares_subterms(lhs)) continue;
           if(rhs->get_term_type() == VARIABLE_TERM)
           {
               add_to_replacement_map(rhs, lhs, replacement_map);
           }
           else if (lhs->get_term_type() == VARIABLE_TERM){
               add_to_replacement_map(lhs, rhs, replacement_map);
           }

       }
       else {
           ILPLeaf* ilp = (ILPLeaf*) child;
           if(ilp->get_operator() != ILP_EQ) continue;
           Term* term_to_replace = NULL;
           bool flip_term_sign;
           const map<Term*, long int>& elems = ilp->get_elems();
           map<Term*, long int>::const_iterator it = elems.begin();
           for(; it!=elems.end(); it++)
           {
               Term* t = it->first;
               if(t->get_term_type() == FUNCTION_TERM) continue;
               int coef = it->second;
               if(coef == 1) {
                   term_to_replace = t;
                   flip_term_sign = true;
                   break;
               }
               else if(coef == -1) {
                   term_to_replace = t;
                   flip_term_sign = false;
                   break;
               }
           }
           if(term_to_replace == NULL) continue;
           map<Term*, long int> rep_terms;
           it = elems.begin();
           for(; it!= elems.end(); it++)
           {
               Term* t = it->first;
               if(t == term_to_replace) continue;
               if(flip_term_sign) {
                   rep_terms[t] = -it->second;
               }
               else {
                   rep_terms[t] = it->second;
               }
           }

           long int constant;
           if(flip_term_sign) constant = ilp->get_constant();
           else constant = -ilp->get_constant();
           Term* replacement_t = ArithmeticTerm::make(rep_terms, constant);
           if(term_to_replace->shares_subterms(replacement_t)) continue;

           add_to_replacement_map(term_to_replace, replacement_t, replacement_map);


       }

   }
   if(replacement_map.size() == 0) return and_node;

   CNode* res= and_node->substitute(replacement_map);
   active_constraint = active_constraint->substitute(replacement_map);
   return res;
}


bool Solver::implies(CNode* node1, CNode* node2)
{
	CNode* res = Connective::make(AND, node1, Connective::make_not(node2));
	Solver s(res, UNSAT_SIMPLIFY);
	return s.get_result()->get_type() == FALSE_NODE;
}


bool Solver::equivalent(CNode* node1, CNode* node2)
{
	return implies(node1, node2) && implies(node2, node1);
}


/*
 * Slices out parts of the background that are irrelevant for simplifying
 * the formula.
 */
CNode* Solver::get_relevant_background(CNode* background,
		CNode* formula)
{
	set<Term*> vars;
	formula->get_nested_terms(vars, true, false);

	/*cout << "relevant vars in: " << formula->to_string() << endl;
	set<Term*>::iterator it = vars.begin();
	for(; it != vars.end(); it++)
	{
		cout << "\t" << (*it)->to_string() << endl;
	}*/

	while(get_related_vars(background, vars))
	{

	}



	return get_relevant_background_internal(background, vars);


}

CNode* Solver::get_relevant_background_internal(CNode* background,
		set<Term*>& vars)
{
	if(background->is_literal()) {
		if(background->contains_term(vars)) return background;
		return True::make();
	}

	Connective* c = (Connective*) background;
	//if(c->get_type() == OR) return c;

	set<CNode*> new_children;
	bool changed = false;

	const set<CNode*>& children = c->get_operands();
	set<CNode*>::iterator it = children.begin();
	for(; it!= children.end(); it++)
	{
		CNode* child = *it;
		CNode* new_child = get_relevant_background_internal(child, vars);
		if(new_child != child) changed = true;
		//if(new_child->get_type() == TRUE_NODE) continue;
		new_children.insert(new_child);

	}

	if(!changed) return background;
	if(new_children.size() == 0) return True::make();
	CNode* new_bg = Connective::make(c->get_type(), new_children);
	return new_bg;


}


bool Solver::get_related_vars(CNode* node, set<Term*>& vars)
{
	switch(node->get_type())
	{
	case TRUE_NODE:
	case FALSE_NODE:
		return false;
	case EQ:
	case ILP:
	case MOD:
	case UNIVERSAL:
	case NOT:
	case BOOLEAN_VAR:
	{
		if(!node->contains_term(vars)) return false;
		int old_size = vars.size();
		node->get_nested_terms(vars, true, false);
		return old_size != (int)vars.size();
	}
	case OR:
	case AND:
	{
		Connective* c = (Connective*)node;
		const set<CNode*>& children = c->get_operands();
		set<CNode*>::const_iterator it = children.begin();
		bool found = false;
		for(; it!= children.end(); it++)
		{
			CNode* child = *it;
			if(get_related_vars(child, vars)) found = true;

		}
		return found;
	}
	default:
		assert(false);

	}
}

void Solver::collect_constraint(CNode* node, bool sat, const string & path)
{

	//if(node->get_size() < 40) return;

	double p = ((double)node->get_size()*node->get_size())/3000.0;

	int t = p*10000.0;
	int r = rand()%10000;
	if(r<0) r = -r;
	if(r>=t) return;



	string id;
	while(true)
	{
		int name = rand();
		if(name < 0) name *=-1;
		id = path + int_to_string(name) + ".mcf";
		ifstream myfile;
		myfile.open(id.c_str());
		if(!myfile.is_open())
		{
			myfile.close();
			break;
		}
		myfile.close();
	}
	node = Connective::make(AND, node, node->get_attribute_constraints());

	string file;
	file = "Type: solve\n";
	file+= string("Status: ") + (sat ? "SAT" : "UNSAT") + "\n";
	file+=node->to_string() + "\n";


	ofstream myfile;
	myfile.open(id.c_str());
	assert(myfile.is_open());
	myfile << file;
	myfile.close();
}

Solver::~Solver()
{

}

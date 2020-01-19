/*
 * ConstraintSolver.cpp
 *
 *  Created on: Sep 16, 2008
 *      Author: tdillig
 */

#include "ConstraintSolver.h"
#include "ExistentialEliminator.h"
#include "VariableEliminator.h"
#include "mistral.h"
#include "assert.h"
#include "NormalForm.h"
#include "UniversalInstantiator.h"
#include "Solver.h"
#include "util.h"
#include "EqualityFinder.h"
#include <algorithm>
#include "ClauseSolve.h"
#include "Constraint.h"
#include "term.h"
#include "cnode.h"
#include <map>
#include "ConflictDatabase.h"
#include "MSAFinder.h"
#include "mistral-parser.h"

#define TRUE_ID 1
#define FALSE_ID 0
#define INVALID -1
#include "time.h"

#define DEBUG false
#define SIMPLIFICATION_LEVEL  THEORY_SIMPLIFY
#define ELIM_SIMPLIFICATION_LEVEL THEORY_SIMPLIFY
#define KEEP_SIMPLIFIED false

/*
 * Remember the constraints that are the "hardest" to solve
 */
#define KEEP_HARDEST_CONSTRAINTS true
#define NUM_HARDEST 5

//#define USE_OLD_ELIMINATOR true


//---------------




ConstraintSolver::ConstraintSolver()
{

	clear_local_data();
	clear_stats();
}




string ConstraintSolver::stats_to_string()
{
	string res = "\n********************\nConstraint Solver stats:\n";
	res+= "Num queries: " + int_to_string(num_sat_queries) + "\n";
	res+= "Solve time: " +
		float_to_string(((double)solve_time) /
				((double)CLOCKS_PER_SEC)) + "\n";
	res+="Num queries involving background knowledge: " +
	int_to_string(num_bg_queries) + "\n";
	res+=get_hardest(hardest);

	res+="Num Variable Eliminations (overapproximation): " +
		int_to_string(num_eliminate_over_queries) + "\n";
	res+= "Elimination time: " +
			float_to_string(((double)eliminate_over_time) /
					((double)CLOCKS_PER_SEC)) + "\n";

	res+=get_hardest(hardest_eliminate_overapproximate);



	res+="Num Variable Eliminations (underapproximation): " +
		int_to_string(num_eliminate_under_queries) + "\n";
	res+= "Elimination time: " +
			float_to_string(((double)eliminate_under_time) /
					((double)CLOCKS_PER_SEC)) + "\n";
	res+=get_hardest(hardest_eliminate_underapproximate);
	res+="Num EQ find:" +
			int_to_string(num_eqs) + "\n";
		res+= "EQ time: " +
				float_to_string(((double)eq_time) /
						((double)CLOCKS_PER_SEC)) + "\n";




	res+= "BG simplification time: " +
			float_to_string(((double)bg_simp_time) /
					((double)CLOCKS_PER_SEC)) + "\n";


	return res;
}

string ConstraintSolver::get_hardest(vector<pair<int, string> > & hardest)
{
	string res;
	if(KEEP_HARDEST_CONSTRAINTS)
	{
		if(hardest.size() ==0) return res;
		set<pair<int, string> > sorted;
		sorted.insert(hardest.begin(), hardest.end());
		res+= "Top " + int_to_string(hardest.size()) + "\n";
		set<pair<int, string> >::reverse_iterator it = sorted.rbegin();
		int i=1;
		for(; it!= sorted.rend(); it++, i++) {
			res+= "(" + int_to_string(i) + ") " + float_to_string((((double)it->first) /
			((double)CLOCKS_PER_SEC) )) +" seconds: " +	it->second + "\n";
		}
	}
	return res;
}

void ConstraintSolver::clear_stats()
{

	/*
	 * Clear stats
	 */
	num_sat_queries = 0;
	solve_time = 0;
	num_bg_queries = 0;
	eq_time = 0;
	num_eqs = 0;


	hardest.clear();

	num_eliminate_over_queries = 0;
	num_eliminate_under_queries = 0;
	eliminate_over_time = 0;
	eliminate_under_time = 0;
	bg_simp_time = 0;

	hardest_eliminate_overapproximate.clear();
	hardest_eliminate_underapproximate.clear();
}

void ConstraintSolver::clear_local_data()
{
	bg_enabled = true;
	constraints.clear();
	reverse_constraints.clear();
	clear_bg();

	CNode *c_false = False::make();
	CNode *c_true = True::make();
	constraint_type false_c = constraint_type(c_false, c_false);
	constraint_type true_c = constraint_type(c_true, c_true);
	constraints[FALSE_ID] = false_c;
	constraints[TRUE_ID] = true_c;
	reverse_constraints[false_c] = FALSE_ID;
	reverse_constraints[true_c] = TRUE_ID;
	id_count = 2;


}

void ConstraintSolver::clear()
{

	CNode::clear();
	ConflictDatabase::clear();
	clear_local_data();


}

void ConstraintSolver::disable_background()
{
	bg_enabled = false;
}

void ConstraintSolver::clear_bg()
{
	bg_enabled = true;
	general_background = NULL;
	background.clear();
	bg_keys.clear();
	fn_to_qvars.clear();
	fn_ids.clear();
	bg_false = false;
	nc_reps.clear();
	sc_reps.clear();

}

CNode* ConstraintSolver::get_nc(c_id& id)
{
	return constraints[id].first;
}
CNode* ConstraintSolver::get_sc(c_id& id)
{
	return constraints[id].second;
}

c_id ConstraintSolver::make_ncsc(c_id nc_id, c_id sc_id)
{
	CNode* nc= constraints[nc_id].first;
	CNode* sc = constraints[sc_id].second;
	constraint_type ct(nc, sc);
	return get_id(ct);
}

c_id ConstraintSolver::nc(c_id id)
{
	CNode* nc= constraints[id].first;
	constraint_type ct(nc, nc);
	return get_id(ct);
}
c_id ConstraintSolver::sc(c_id id)
{
	CNode* sc= constraints[id].second;
	constraint_type ct(sc, sc);
	return get_id(ct);
}

ConstraintSolver::~ConstraintSolver()
{
	//CNode::clear();
}

c_id ConstraintSolver::get_true_constraint()
{
	return TRUE_ID;
}

c_id ConstraintSolver::get_false_constraint()
{
	return FALSE_ID;
}

c_id ConstraintSolver::get_atom(Term* t1, Term* t2, atom_op_type op)
{
	CNode* res = NULL;
	switch(op)
	{
	case ATOM_EQ:
	{
		// swap if t2 is a mod term
		if(is_mod_term(t2))
		{
			Term* temp = t1;
			t1 = t2;
			t2 = temp;
		}
		// special case for mod leaves
		if(!is_mod_term(t2) && is_valid_mod_term(t1))
		{
			FunctionTerm* ft = (FunctionTerm*)t1;
			Term* arg1 = ft->get_args()[0];
			Term* arg2 = ft->get_args()[1];
			assert(arg2->get_term_type() == CONSTANT_TERM);
			long int k = ((ConstantTerm*) arg2)->get_constant();
			res = ModLeaf::make(arg1, k, t2);
		}

		else res = EqLeaf::make(t1, t2);
		break;
	}
	case ATOM_NEQ:
	{
		c_id cur_id = get_atom(t1, t2, ATOM_EQ);
		CNode* eq = constraints[cur_id].first;
		res = Connective::make_not(eq);
		break;
	}
	case ATOM_LT:
	{
		res = ILPLeaf::make(t1, t2, ILP_LT);
		break;
	}
	case ATOM_LEQ:
	{
		res = ILPLeaf::make(t1, t2, ILP_LEQ);
		break;
	}
	case ATOM_GT:
	{
		res = ILPLeaf::make(t1, t2, ILP_GT);
		break;
	}
	case ATOM_GEQ:
	{
		res = ILPLeaf::make(t1, t2, ILP_GEQ);
		break;
	}
	case ATOM_MOD:
	{
		assert(t2->type == CONSTANT_TERM);
		ConstantTerm* c = (ConstantTerm*)t2;
		res = ModLeaf::make(t1, c->get_constant());
		break;
	}
	default:
		assert(false);
	}

	constraint_type ct(res, res);
	return get_id(ct);


}

bool ConstraintSolver::is_mod_term(Term* t)
{
	if(t->get_term_type() != FUNCTION_TERM) return false;
	FunctionTerm* ft = (FunctionTerm*) t;
	return(ft->get_name() == "%");
}

bool ConstraintSolver::is_valid_mod_term(Term* t)
{
	if(t->get_term_type() != FUNCTION_TERM) return false;
	FunctionTerm* ft = (FunctionTerm*) t;
	if(ft->get_name() != "%") return false;
	const vector<Term*>& args = ft->get_args();
	assert(args.size() == 2);
	Term* t1 = args[0];
	Term* t2 = args[1];
	if(t2->get_term_type() != CONSTANT_TERM) return false;
	return !is_mod_term(t1);
}

bool ConstraintSolver::is_precise(c_id id) const
{
	const constraint_type& ct = constraints.find(id)->second;
	return ct.first == ct.second;
}

c_id ConstraintSolver::get_new_id(c_id old_id)
{
	constraint_type& ct = constraints[old_id];
	c_id id = id_count++;
	assert(constraints.count(id) == 0);
	constraints[id] = ct;
	return id;
}

c_id ConstraintSolver::get_id(constraint_type& c)
{
	c_id id = id_count++;
	assert(constraints.count(id) == 0);
	constraints[id] = c;
	reverse_constraints[c] = id;
	return id;
}

c_id ConstraintSolver::get_constraint_from_string(string & s)
{
	CNode* constraint = parse_constraint(s, NULL);
	constraint = is_sat(constraint, SIMPLIFICATION_LEVEL, true);
	if(constraint == NULL) return INVALID;
	constraint_type ct = constraint_type(constraint, constraint);
	return get_id(ct);
}

c_id ConstraintSolver::get_constraint_from_cnode(CNode* n)
{
	constraint_type ct = constraint_type(n, n);
	return get_id(ct);
}

inline CNode* ConstraintSolver::is_sat(CNode* node,
		simplification_level level,  bool use_nc, void* _assignments)
{

	if(bg_enabled && bg_false) return False::make();
	cnode_type t = node->get_type();
	if(t == FALSE_NODE || t==TRUE_NODE) return node;

	CNode* full_constraint = node;
	CNode* assumptions = True::make();
	if(bg_enabled && general_background != NULL) {
		assumptions = general_background;
		full_constraint = Connective::make(AND, general_background,
				full_constraint);
	}
	if(bg_enabled) {
		CNode* dependencies = get_background_dependencies(full_constraint,
				use_nc);
		assumptions = Connective::make(AND, assumptions, dependencies);
	}

	map<Term*, SatValue>* assignments = (map<Term*, SatValue>*)_assignments;
	num_sat_queries++;
	if(assumptions->get_type() != TRUE_NODE) num_bg_queries++;
	clock_t start, finish;


	//cout << "ASSUMPTIONS: " << assumptions->to_string() << endl;
	//cout << "Node: " << node->to_string() << endl;

	start = clock();
	Solver s(node, assumptions,  level, assignments);
	finish = clock();
	CNode * new_node = s.get_result();
	int cur_time = finish-start;
	solve_time += cur_time;

	//cerr << "Cur time: " << ((double)cur_time)/ ((double)CLOCKS_PER_SEC) << endl;



	/* if(((double)cur_time)/ ((double)CLOCKS_PER_SEC) > 3) {
		cout << "NODE: " << node->to_string() << endl;
		cout << "Assumptions: " << assumptions->to_string() << endl;

		cout << "Attrributes: " <<
				Connective::make(AND, node, assumptions)->get_attribute_constraints()->to_string()
				<< endl;
		assert(false);
	}*/


	add_to_hardest(hardest, cur_time, "[S] " + node->to_string()
			+ " assumptions: " + assumptions->to_string() + " attributes: " +
			node->get_attribute_constraints()->to_string() + "\n Simplification: " +
			new_node->to_string());


	/*if(((((double)cur_time) /
			((double)CLOCKS_PER_SEC) )) > 0.3) {

		cout << "Constraint: " << node->to_string() <<  endl;
		cout << "Simplification" << new_node->to_string() << endl;
		assert(false);
	}*/



	return new_node;
}

inline CNode* ConstraintSolver::is_sat(CNode* node, CNode* assumption,
		simplification_level level,  bool use_nc, void* _assignments)
{

	cnode_type t = node->get_type();
	if(t == FALSE_NODE || t==TRUE_NODE) return node;

	CNode* full_constraint = node;
	CNode* assumptions = True::make();
	if(bg_enabled) {
		if(general_background != NULL) {
			assumptions = general_background;
			full_constraint = Connective::make(AND, general_background,
					full_constraint);
		}

		CNode* dependencies = get_background_dependencies(full_constraint,
				use_nc);
		assumptions = Connective::make(AND, assumptions, dependencies);
	}



	map<Term*, SatValue>* assignments = (map<Term*, SatValue>*)_assignments;
	num_sat_queries++;
	if(assumptions->get_type() != TRUE_NODE) num_bg_queries++;
	clock_t start, finish;

	assumptions = Connective::make(AND, assumptions, assumption);


	start = clock();
	Solver s(node, assumptions,  level, assignments);
	finish = clock();
	CNode * new_node = s.get_result();
	int cur_time = finish-start;
	solve_time += cur_time;




	add_to_hardest(hardest, cur_time, "[S] " + node->to_string()
			+ " assumptions: " + assumptions->to_string() + " attributes: " +
			node->get_attribute_constraints()->to_string() + "\n Simplification: " +
			new_node->to_string());


	return new_node;
}


inline CNode* ConstraintSolver::is_valid(CNode* c,simplification_level level)
{
	//cout << "Querying validity: " << c->to_string() << endl;
	CNode* node = Connective::make_not(c);
	CNode* new_node = is_sat(node,  level, true);
	new_node = Connective::make_not(new_node);
	return new_node;
}


void ConstraintSolver::to_dnf(c_id c, set<c_id> & dnf_set)
{
	constraint_type& ct = constraints[c];
	CNode* cur = ct.first;
	assert(cur != NULL);
	cur = Connective::make_not(cur);
	CNode* cnf = cur->to_cnf();
	CNode* dnf = Connective::make_not(cnf);
	if(dnf->get_type() != OR)
	{
		constraint_type ct = constraint_type(dnf, dnf);
		c_id res_id = get_id(ct);
		dnf_set.insert(res_id);
		return;
	}
	Connective* outer_c = static_cast<Connective*>(dnf);
	for(auto it = outer_c->get_operands().begin();
			it != outer_c->get_operands().end(); it++)
	{
		CNode* cur = *it;
		constraint_type ct = constraint_type(cur, cur);
		c_id res_id = get_id(ct);
		dnf_set.insert(res_id);
	}

}


bool ConstraintSolver::is_sat(c_id & id)
{
	constraint_type& ct = constraints[id];
	CNode* cur = ct.first;
	assert(cur != NULL);
	CNode* new_node = is_sat(cur, SIMPLIFICATION_LEVEL, true);
	ct.first = new_node;

	if(cur == ct.second)
		ct.second = new_node;
	return new_node->get_type()!= FALSE_NODE;
}

bool ConstraintSolver::is_sat_discard(c_id & id)
{
	constraint_type& ct = constraints[id];
	CNode* cur = ct.first;
	assert(cur != NULL);
	CNode* new_node = is_sat(cur, UNSAT_SIMPLIFY, true);
	ct.first = new_node;

	if(cur == ct.second)
		ct.second = new_node;
	return new_node->get_type()!= FALSE_NODE;
}

bool ConstraintSolver::get_assignment(c_id id, map<Term*, SatValue> & assignments)
{
	constraint_type& ct = constraints[id];
	CNode* cur = ct.first;
	assert(cur != NULL);

	CNode* new_node = is_sat(cur,  UNSAT_SIMPLIFY,
			true, &assignments);

	if(new_node->get_type() == FALSE_NODE) return false;

	cout << "Returning true for: " << cur->to_string() << " assignment size: "
			<< assignments.size() << endl;
	return true;

}

bool ConstraintSolver::get_assignment(c_id id,
		set<pair<string, string> > & assignments)
{
	constraint_type& ct = constraints[id];
	CNode* cur = ct.first;
	assert(cur != NULL);
	map<Term*, SatValue> term_assignments;

	CNode* new_node = is_sat(cur,  UNSAT_SIMPLIFY,
			true, &term_assignments);
	if(new_node->get_type() == FALSE_NODE) return false;
	map<Term*, SatValue>::iterator it = term_assignments.begin();


	for(; it != term_assignments.end(); it++)
	{
		string key = it->first->to_string();
		string assignment = it->second.to_string();
		assignments.insert(pair<string, string>(key, assignment));
	}

	return true;

}

string ConstraintSolver::bg_to_string()
{
	string res = "";
	if(general_background != NULL)
	 res+= "General background: " + general_background->to_string() + "\n";

	map<CNode*, CNode*>::iterator it = nc_reps.begin();
	for(; it!= nc_reps.end(); it++)
	{
		CNode* c = it->first;
		CNode* nc = it->second;
		assert(sc_reps.count(c) > 0);
		CNode* sc = sc_reps[c];
		res += c->to_string() + "=>" + nc->to_string() + " \n";
		res += sc->to_string() + "=> " + c->to_string() + "\n";

	}
	return res;
}

c_id ConstraintSolver::get_general_background()
{
	if(general_background == NULL) {
		return get_true_constraint();
	}
	constraint_type ct = constraint_type(general_background, general_background);
	c_id res_id = get_id(ct);
	return res_id;
}

bool ConstraintSolver::is_valid(c_id id)
{
	constraint_type& ct = constraints[id];
	CNode* c = ct.second;
	assert(c!=NULL);
	CNode* new_node = is_valid(c, SIMPLIFICATION_LEVEL);
	ct.second = new_node;
	if(c == ct.first)
		ct.first = new_node;
	return new_node->get_type() == TRUE_NODE;

}

bool ConstraintSolver::is_valid_discard(c_id id)
{
	constraint_type& ct = constraints[id];
	CNode* c = ct.second;
	assert(c!=NULL);
	CNode* new_node = is_valid(c, UNSAT_SIMPLIFY);
	ct.second = new_node;
	if(c == ct.first)
		ct.first = new_node;
	return new_node->get_type() == TRUE_NODE;

}

bool ConstraintSolver::implies(c_id id1, c_id id2)
{
	CNode* c1 = constraints[id1].first;
	CNode* c2 = constraints[id2].second;
	assert(c1!=NULL && c2!=NULL);
	CNode* c_not = Connective::make_not(c1);
	CNode* res = Connective::make(OR, c_not, c2);
	res = is_valid(res, UNSAT_SIMPLIFY);
	return res->get_type() == TRUE_NODE;
}

bool ConstraintSolver::implies(CNode* n1, CNode* n2)
{
	CNode* c_not = Connective::make_not(n1);
	CNode* res = Connective::make(OR, c_not, n2);

	res = Connective::make_not(res);
	Solver s(res, UNSAT_SIMPLIFY);
	return s.get_result()->get_type() == FALSE_NODE;
}


c_id ConstraintSolver::and_constraint(c_id id1, c_id id2)
{
	constraint_type& ct1 = constraints[id1];
	constraint_type& ct2 = constraints[id2];
	CNode* c1_nc = ct1.first;
	CNode* c1_sc = ct1.second;
	CNode* c2_nc = ct2.first;
	CNode* c2_sc = ct2.second;
	assert(c1_nc!=NULL && c1_sc!=NULL && c2_nc!=NULL && c2_sc != NULL);



	//CNode *_res_nc = Connective::make(AND, c1_nc, c2_nc);

	//CNode *_res_sc = Connective::make(AND, c1_sc, c2_sc);

	if(KEEP_SIMPLIFIED) {
		assert(false);


	}

	CNode *res_nc = Connective::make(AND, c1_nc, c2_nc)->refactor();
	CNode *res_sc = Connective::make(AND, c1_sc, c2_sc)->refactor();

	constraint_type ct = constraint_type(res_nc, res_sc);
	c_id res_id = get_id(ct);

	return res_id;

}
c_id ConstraintSolver::or_constraint(c_id id1, c_id id2)
{
	constraint_type& ct1 = constraints[id1];
	constraint_type& ct2 = constraints[id2];
	CNode* c1_nc = ct1.first;
	CNode* c1_sc = ct1.second;
	CNode* c2_nc = ct2.first;
	CNode* c2_sc = ct2.second;
	assert(c1_nc!=NULL && c1_sc!=NULL && c2_nc!=NULL && c2_sc != NULL);

	CNode *res_nc = Connective::make(OR, c1_nc, c2_nc)->refactor();
	CNode *res_sc = Connective::make(OR, c1_sc, c2_sc)->refactor();
	constraint_type ct = constraint_type(res_nc, res_sc);
	c_id res_id = get_id(ct);
	return res_id;
}
c_id ConstraintSolver::not_constraint(c_id id)
{
	constraint_type& _ct = constraints[id];
	CNode* c_nc = _ct.first;
	CNode* c_sc = _ct.second;
	assert(c_nc!=NULL && c_sc != NULL);
	CNode *res_nc = Connective::make_not(c_sc);
	CNode *res_sc = Connective::make_not(c_nc);
	constraint_type ct(res_nc, res_sc);
	return get_id(ct);
}


string ConstraintSolver::constraint_to_string(c_id id)
{
	constraint_type& ct = constraints[id];
	CNode* cur_nc = ct.first;
	CNode* cur_sc = ct.second;
	assert(cur_nc != NULL && cur_sc != NULL);
	string nc_str = cur_nc->to_string();
	if(cur_nc == cur_sc)
		return nc_str;
	return "(" + nc_str + ", " +
		cur_sc->to_string() +  ")";

}

bool ConstraintSolver::contains_inequality(c_id id)
{
	constraint_type& ct = constraints[id];
	CNode* nc = ct.first;
	return nc->contains_inequality();
}

bool ConstraintSolver::is_equal(c_id id1, c_id id2)
{
	if(id1 == id2) return true;
	constraint_type& ct1 = constraints[id1];
	constraint_type& ct2 = constraints[id2];
	return implies(ct1.first, ct2.first)  && implies(ct1.second, ct2.second);
}

bool ConstraintSolver::is_equivalent(c_id id1, c_id id2)
{
	return implies(id1, id2) && implies(id2, id1);
}

void ConstraintSolver::get_terms(c_id id, set<Term*>& terms,
		bool include_nested_terms)
{
	constraint_type& ct = constraints[id];
	CNode* nc = ct.first;
	CNode* sc = ct.second;
	assert(nc != NULL && sc != NULL);

	nc->get_nested_terms(terms, include_nested_terms, true);
	if(sc!=nc) sc->get_nested_terms(terms, include_nested_terms, true);

}



void ConstraintSolver::find_equalities(c_id id, Term* t, set<Term*> & eqs)
{
	constraint_type& ct = constraints[id];
	CNode * cur_nc = ct.first;
	assert(cur_nc != NULL);
	EqualityFinder ef(cur_nc, t, false);
	eqs = ef.get_equalities();
}


Term* ConstraintSolver::find_equality(c_id id, Term* t)
{
	constraint_type& ct = constraints[id];
	CNode * cur_nc = ct.first;
	assert(cur_nc != NULL);
	EqualityFinder ef(cur_nc, t, false);
	const set<Term*> & eqs = ef.get_equalities();

	if(eqs.size() == 0) return NULL;
	Term* new_t = *eqs.begin();
	term_type new_type = new_t->get_term_type();
	// Always favor constants and variables over other kinds of terms
	if(new_type != CONSTANT_TERM && new_type != VARIABLE_TERM)
	{
		set<Term*>::const_iterator it = eqs.begin();
		it++;
		for(; it!= eqs.end(); it++){
			Term* cur = *it;
			term_type tt = cur->get_term_type();
			if(tt == CONSTANT_TERM || tt==VARIABLE_TERM) {
				new_t = cur;
				break;
			}
		}
	}

	return new_t;
}



bool ConstraintSolver::has_equality_relation(c_id id, Term* t1, Term* t2)
{
	constraint_type& ct = constraints[id];
	CNode * cur_nc = ct.first;
	assert(cur_nc != NULL);

	EqualityFinder ef(cur_nc, t1, false);
	const set<Term*> & eqs = ef.get_equalities();
	set<Term*>::iterator it = eqs.begin();
	for(; it!= eqs.end(); it++) {
		Term* cur = *it;
		if(cur == t2) return true;
		if(cur->get_term_type() != ARITHMETIC_TERM) continue;
		ArithmeticTerm* at = (ArithmeticTerm*) cur;
		const map<Term*, long int>& elems = at->get_elems();
		map<Term*, long int>::const_iterator it2 = elems.begin();
		for(; it2!= elems.end(); it2++){
			Term* cur_t = it2->first;
			if(cur_t == t2) return true;
		}

	}
	return false;

}


void ConstraintSolver::get_disjunctive_equalities(c_id id, Term* t,
		map<Term*, Constraint> & equalities)
{
	constraint_type& ct = constraints[id];
	CNode * cur_nc = ct.first;
	assert(cur_nc != NULL);
	EqualityFinder ef(cur_nc, t, true);
	const map<Term*, CNode*> & eqs = ef.get_disjunctive_equalities();

	map<Term*, CNode*>::const_iterator it = eqs.begin();
	for(; it != eqs.end(); it++)
	{
		Term* t = it->first;
		CNode* c = it->second;
		constraint_type ct(c, c);
		c_id new_id = get_id(ct);
		Constraint res_c;
		res_c.id = new_id;
		equalities[t] = res_c;
	}

}


CNode* ConstraintSolver::eliminate_var(CNode* n, VariableTerm* t,
		simplification_level level, bool over)
{
	int start = clock();

#ifdef USE_OLD_ELIMINATOR
	VariableEliminator elim(n, t, THEORY_SIMPLIFY, over);
#endif

#ifndef USE_OLD_ELIMINATOR
	ExistentialEliminator elim(n, t, over);
#endif

	//delete me
	//VariableEliminator elim2(n, t, THEORY_SIMPLIFY, over);
	//delete me end

	int end = clock();
	int time = end-start;

	string var = t->to_string();
	if(over)
	{
		num_eliminate_over_queries++;
		eliminate_over_time+=time;

		add_to_hardest(hardest_eliminate_overapproximate, time, n->to_string() +
				" : " +var);
	}
	else
	{
		num_eliminate_under_queries++;
		eliminate_under_time+=time;
		add_to_hardest(hardest_eliminate_underapproximate, time, n->to_string() +
				" : " +var);
	}
	CNode* res= elim.get_result();
	//delete me
	/*
	CNode* res2 = elim2.get_result();
	CNode* r1 = Connective::make(AND, res, Connective::make_not(res2));
	CNode* r2 = Connective::make(AND, res2, Connective::make_not(res));
	CNode* e1 = is_sat(r1, UNSAT_SIMPLIFY, true);
	CNode* e2 = is_sat(r2, UNSAT_SIMPLIFY, true);
	if(e1->get_type() != FALSE_NODE ||e2->get_type() != FALSE_NODE)
	{
		cout << "NOt equal:" << n->to_string() << endl;
		cout << "elim: " << t->to_string() << endl;
		cout << "new res: " << res->to_string() << endl;
		cout << "old res: " << res2->to_string() << endl;
		assert(false);
	}
	*/
	//delete me end


	return res;
}

CNode* ConstraintSolver::eliminate_var(CNode* n, vector<VariableTerm*>& elim_t,
		simplification_level level, bool over)
{
	string vars = "( ";
	for(unsigned int i=0; i < elim_t.size(); i++)
	{
		vars+= elim_t[i]->to_string();
		if(i < elim_t.size() - 1) vars+=", ";
	}
	vars+=" )";
	int start = clock();
	//cout << "Eliminating " << vars
	//	<< " in " <<n->to_string() << endl;
	CNode* res = n;
#ifdef USE_OLD_ELIMINATOR
	VariableEliminator ve(res, elim_t, THEORY_SIMPLIFY, over);
	res = ve.get_result();
#endif
#ifndef USE_OLD_ELIMINATOR
	for(vector<VariableTerm*>::iterator it = elim_t.begin();
							it != elim_t.end(); it++)
	{
		VariableTerm* cur = *it;
		ExistentialEliminator elim(res, cur, over);
		res = elim.get_result();
	}
#endif
	//cout << "Finished" << endl;
	int end = clock();
	int time = end-start;




	if(over)
	{
		num_eliminate_over_queries++;
		eliminate_over_time+=time;
		add_to_hardest(hardest_eliminate_overapproximate, time,
				n->to_string() + ": " + vars);
	}
	else
	{
		num_eliminate_under_queries++;
		eliminate_under_time+=time;
		add_to_hardest(hardest_eliminate_underapproximate, time,
				n->to_string() + ": " + vars);
	}
	return res;
}



void ConstraintSolver::add_to_hardest(vector<pair<int, string> > & hardest,
		int cur_time, const string& cur)
{
	if(!KEEP_HARDEST_CONSTRAINTS || cur_time == 0) return;

/*	if(((((double)cur_time) /
			((double)CLOCKS_PER_SEC) )) > 0.25) {

		cout << "Constraint: " << cur << endl;
		assert(false);
	} */

	if(hardest.size() < NUM_HARDEST) hardest.push_back(
			pair<int, string>(cur_time, cur));
	else{
		int min = hardest[0].first;
		int min_index = 0;
		for(unsigned int i=1; i<NUM_HARDEST; i++) {
			if(hardest[i].first < min) {
				min = hardest[i].first;
				min_index = i;
			}
		}
		if(cur_time > min){
			hardest[min_index] = pair<int, string>(cur_time, cur);
		}
	}


}


c_id ConstraintSolver::eliminate_evar(c_id id, VariableTerm* var)
{
	constraint_type& _ct = constraints[id];
	CNode* nc = _ct.first;
	CNode* sc = _ct.second;
	nc = eliminate_var(nc, var,  ELIM_SIMPLIFICATION_LEVEL, true);
	sc = eliminate_var(sc, var, ELIM_SIMPLIFICATION_LEVEL, false);
	constraint_type ct(nc, sc);
	c_id new_id = get_id(ct);
	return new_id;
}



c_id ConstraintSolver::eliminate_evars(c_id id, set<VariableTerm*>& vars)
{

	vector<VariableTerm*> vars_vec;
	set<VariableTerm*>::iterator it = vars.begin();
	for(; it!= vars.end(); it++)
	{
		vars_vec.push_back(*it);
	}

	constraint_type& _ct = constraints[id];
	CNode* nc = _ct.first;
	CNode* sc = _ct.second;
	nc = eliminate_var(nc, vars_vec, ELIM_SIMPLIFICATION_LEVEL, true);
	sc = eliminate_var(sc, vars_vec, ELIM_SIMPLIFICATION_LEVEL, false);
	constraint_type ct(nc, sc);
	c_id new_id = get_id(ct);
	return new_id;


}

c_id ConstraintSolver::eliminate_uvar(c_id id, VariableTerm* var)
{
	constraint_type& _ct = constraints[id];
	CNode* nc = _ct.first;
	CNode* sc = _ct.second;

	CNode* not_nc = Connective::make_not(nc);
	CNode* not_sc = Connective::make_not(sc);



	CNode* new_not_nc = eliminate_var(not_nc, var,
			ELIM_SIMPLIFICATION_LEVEL, false);

	CNode* new_not_sc;
	if(not_nc == not_sc) new_not_sc = new_not_nc;
	else
	{
		new_not_sc = eliminate_var(not_sc, var,
					ELIM_SIMPLIFICATION_LEVEL, true);
	}
	CNode* res_nc = Connective::make_not(new_not_nc);
	CNode* res_sc = Connective::make_not(new_not_sc);

	constraint_type ct(res_nc, res_sc);
	c_id new_id = get_id(ct);
	return new_id;
}

c_id ConstraintSolver::eliminate_uvars(c_id id, set<VariableTerm*> &vars)
{

	vector<VariableTerm*> vars_vec;
	set<VariableTerm*>::iterator it = vars.begin();
	for(; it!= vars.end(); it++)
	{
		vars_vec.push_back(*it);
	}

	constraint_type& _ct = constraints[id];
	CNode* nc = _ct.first;
	CNode* sc = _ct.second;

	CNode* not_nc = Connective::make_not(nc);
	CNode* not_sc = Connective::make_not(sc);



	CNode* new_not_nc = eliminate_var(not_nc, vars_vec,
			ELIM_SIMPLIFICATION_LEVEL, false);

	CNode* new_not_sc;
	if(not_nc == not_sc) new_not_sc = new_not_nc;
	else
	{
		new_not_sc = eliminate_var(not_sc, vars_vec,
					ELIM_SIMPLIFICATION_LEVEL, true);
	}
	CNode* res_nc = Connective::make_not(new_not_nc);
	CNode* res_sc = Connective::make_not(new_not_sc);

	constraint_type ct(res_nc, res_sc);
	c_id new_id = get_id(ct);
	return new_id;
}




c_id ConstraintSolver::divide(c_id id, long int c, Term* t)
{
	cout << "divide: " << t->to_string() << " by " << c << endl;
	constraint_type& _ct = constraints[id];
	CNode* nc = _ct.first;
	CNode* sc = _ct.second;
	nc = nc->divide(c, t);
	sc = sc->divide(c, t);
	constraint_type ct(nc, sc);
	c_id new_id = get_id(ct);
	return new_id;
}

CNode* ConstraintSolver::eliminate_free_var_nc(CNode* nc, VariableTerm* v)
{
	CNode* nc_res = nc;
	set<CNode*> nc_literals;
	nc->get_literals_containing_term(v, nc_literals);

	set<CNode*>::iterator it = nc_literals.begin();
	for(; it!= nc_literals.end(); it++)
	{
		CNode* cur = *it;
		CNode* not_cur = Connective::make_not(cur);
		CNode* nc_true = nc_res->replace(cur, True::make());

		if(nc_literals.count(not_cur) == 0)
		{
			nc_res = nc_true;
		}
		else {
			CNode* nc_false = nc_res->replace(cur, False::make());
			nc_res = Connective::make(OR, nc_true, nc_false);
		}

	}
	return nc_res;
}
CNode* ConstraintSolver::eliminate_free_var_sc(CNode* sc, VariableTerm* v)
{
	CNode* sc_res =sc;
	set<CNode*> sc_literals;
	sc->get_literals_containing_term(v, sc_literals);

	set<CNode*>::iterator it = sc_literals.begin();
	for(; it!= sc_literals.end(); it++)
	{
		CNode* cur = *it;
		CNode* not_cur = Connective::make_not(cur);
		CNode* sc_false = sc_res->replace(cur, False::make());

		if(sc_literals.count(not_cur) == 0)
		{
			sc_res = sc_false;
		}
		else {
			CNode* sc_true = sc_res->replace(cur, True::make());
			sc_res = Connective::make(AND, sc_true, sc_false);
		}

	}

	return sc_res;
}


c_id ConstraintSolver::eliminate_free_var(c_id id, VariableTerm* var)
{

	constraint_type& _ct = constraints[id];
	CNode* nc = _ct.first;
	CNode* sc = _ct.second;

	set<CNode*> nc_literals;
	set<Term*> nc_terms;
	nc->get_literals_containing_term(var, nc_literals);
	set<CNode*>::iterator it = nc_literals.begin();
	for(; it != nc_literals.end(); it++) {
		CNode* cur = *it;
		cur->get_vars(nc_terms);
	}



	CNode* nc_res;
	if(nc_terms.size() == 1) {
		nc_res = eliminate_free_var_nc(nc, var);
	}
	else {
		nc_res = eliminate_var(nc, var, ELIM_SIMPLIFICATION_LEVEL, true);
	}


	set<CNode*> sc_literals;
	set<Term*> sc_terms;
	sc->get_literals_containing_term(var, sc_literals);
	it = sc_literals.begin();
	for(; it != sc_literals.end(); it++) {
		CNode* cur = *it;
		cur->get_vars(sc_terms);
	}

	CNode* sc_res;
	if( sc_terms.size() == 1) {
		sc_res = eliminate_free_var_sc(sc, var);
	}
	else {
		CNode* neg_sc = Connective::make_not(sc);
		sc_res = eliminate_var(neg_sc, var, ELIM_SIMPLIFICATION_LEVEL, true);
		sc_res = Connective::make_not(sc_res);
	}
	constraint_type ct_res(nc_res, sc_res);
	c_id res_id = get_id(ct_res);
	return res_id;






/*
	CNode* nc_res = eliminate_free_var_nc(nc, var);
	CNode* sc_res = eliminate_free_var_sc(sc, var);
	constraint_type res_ct(nc_res, sc_res);
	c_id res_id = get_id(res_ct);
	is_sat(res_id);
	is_valid(res_id);
	return res_id; */



	nc = eliminate_var(nc, var, ELIM_SIMPLIFICATION_LEVEL, true);

	CNode* neg_sc = Connective::make_not(sc);
	//cout << "Eliminating var from: " << neg_sc->to_string() << " var: " <<
		//	var->to_string() << endl;
	//int start = clock();
	sc = eliminate_var(neg_sc, var, ELIM_SIMPLIFICATION_LEVEL, true);
	//int end = clock();
	//cout << "Result: " << sc->to_string() << endl;
	/*int time = end-start;
	if(((((double)time) /
			((double)CLOCKS_PER_SEC) )) > 0.5) {
		assert(false);
	}*/


	sc = Connective::make_not(sc);
	constraint_type ct(nc, sc);
	c_id new_id = get_id(ct);
	return new_id;

}
c_id ConstraintSolver::eliminate_free_vars(c_id id, set<VariableTerm*>& vars)
{

	constraint_type& _ct = constraints[id];
	CNode* nc = _ct.first;
	CNode* sc = _ct.second;

	CNode* nc_res = nc;
	CNode* sc_res = sc;
	set<VariableTerm*>::iterator it = vars.begin();
	for(; it!= vars.end(); it++) {
		nc_res = this->eliminate_free_var_nc(nc_res, *it);
		sc_res = this->eliminate_free_var_sc(sc_res, *it);
	}

	constraint_type res_ct(nc_res, sc_res);
	c_id res_id = get_id(res_ct);
	is_sat(res_id);
	is_valid(res_id);
	return res_id;

	vector<VariableTerm*> vars_vec;
	set<VariableTerm*>::iterator it2 = vars.begin();
	for(; it2!= vars.end(); it2++)
	{
		vars_vec.push_back(*it);
	}





	nc = eliminate_var(nc, vars_vec, ELIM_SIMPLIFICATION_LEVEL, true);

	sc = Connective::make_not(sc);
	sc = eliminate_var(sc, vars_vec, ELIM_SIMPLIFICATION_LEVEL, true);
	sc = Connective::make_not(sc);
	constraint_type ct(nc, sc);
	c_id new_id = get_id(ct);
	return new_id;
}




c_id ConstraintSolver::assume(c_id id, c_id other_id)
{


	constraint_type c = constraints[id];
	CNode* nc = c.first;
	CNode* sc = c.second;


	constraint_type other = constraints[other_id];
	CNode* other_nc = other.first;
	CNode* other_sc = other.second;




	Solver t1(other_sc, UNSAT_SIMPLIFY, NULL);
	if(t1.get_result()->get_type() != FALSE_NODE)
	{

		nc = is_sat(nc, other_sc, THEORY_SIMPLIFY, true, NULL);
		//Solver s_nc(nc, other_sc,  THEORY_SIMPLIFY, NULL);
		//nc = s_nc.get_result();
	}
	else nc = True::make();

	Solver t2(other_nc, UNSAT_SIMPLIFY, NULL);
	if(t2.get_result()->get_type() != FALSE_NODE)
	{
		sc = is_sat(sc, other_nc, THEORY_SIMPLIFY, true, NULL);
		//Solver s_sc(sc, other_nc,  THEORY_SIMPLIFY, NULL);
		//sc = s_sc.get_result();
	}
	else sc = True::make();
	constraint_type new_ct(nc, sc);
	c_id new_id = get_id(new_ct);
	return new_id;
}


bool ConstraintSolver::contains_term(c_id id, Term* t)
{
	constraint_type ct = constraints[id];
	CNode* nc= ct.first;
	CNode* sc = ct.second;

	if(nc->contains_term(t)) return true;
	if(nc == sc) return false;
	return sc->contains_term(t);
}


bool ConstraintSolver::contains_term(c_id id, set<Term*>& t)
{
	constraint_type ct = constraints[id];
	CNode* nc= ct.first;
	CNode* sc = ct.second;
	if(nc->contains_term(t)) return true;
	if(nc == sc) return false;
	return sc->contains_term(t);

}



c_id ConstraintSolver::replace_term(c_id old_id, Term* t1,
		Term* t2)
{
	map<Term*, Term*> replacements;
	replacements[t1] = t2;

	constraint_type ct = constraints[old_id];
	CNode* nc= ct.first;
	CNode* sc = ct.second;
	CNode* new_nc = nc->substitute(replacements);
	if(nc == sc) {

		if(nc == new_nc) return old_id;
		constraint_type ct(new_nc, new_nc);
		return get_id(ct);
	}

	CNode* new_sc = sc->substitute(replacements);
	ct = constraint_type(new_nc, new_sc);
	return get_id(ct);
}



c_id ConstraintSolver::replace_terms(c_id old_id, map<Term*, Term*>&
		replacements)
{


	constraint_type ct = constraints[old_id];
	CNode* nc= ct.first;
	CNode* sc = ct.second;
	CNode* new_nc = nc->substitute(replacements);
	if(nc == sc) {
		if(nc == new_nc) return old_id;
		constraint_type ct(new_nc, new_nc);
		return get_id(ct);
	}

	CNode* new_sc = sc->substitute(replacements);
	ct = constraint_type(new_nc, new_sc);
	return get_id(ct);
}

c_id ConstraintSolver::replace_constraint(c_id old_id, c_id to_replace,
		c_id replacement)

{
	constraint_type c = constraints[old_id];
	constraint_type c1 = constraints[to_replace];
	constraint_type c2= constraints[replacement];

	CNode* c_nc = c.first;
	CNode* c_sc = c.second;

	CNode* to_replace_nc = c1.first;
	CNode* to_replace_sc = c1.second;

	CNode* replacement_nc = c2.first;
	CNode* replacement_sc = c2.second;

	CNode* new_nc = c_nc->replace(to_replace_nc, replacement_nc);
	CNode* new_sc = c_sc->replace(to_replace_sc, replacement_sc);

	constraint_type ct = constraint_type(new_nc, new_sc);
	return get_id(ct);
}


c_id ConstraintSolver::replace_constraints(c_id old_id,
		map<Constraint, Constraint>& replacements)
{
	constraint_type ct = constraints[old_id];
	map<CNode*, CNode*> nc_reps;
	map<CNode*, CNode*> sc_reps;
	map<Constraint, Constraint>::iterator it = replacements.begin();
	for(; it!= replacements.end(); it++)
	{
		constraint_type ct_key = constraints[it->first.id];
		constraint_type ct_value = constraints[it->second.id];
		nc_reps[ct_key.first] = ct_value.first;
		sc_reps[ct_key.second] = ct_value.second;

	}

	CNode* nc= ct.first;
	CNode* sc = ct.second;
	CNode* new_nc = nc->substitute(nc_reps);
	CNode* new_sc = sc->substitute(sc_reps);
	ct = constraint_type(new_nc, new_sc);
	return get_id(ct);
}


/*
Term* base_t;
Term* delta_t;

bool arrayterm_has_base(FunctionTerm* ft)
{
	string name = ft->get_name();
	if(name != ARRAYREF_TERM) return false;
	const vector<Term*>& args = ft->get_args();
	assert(args.size() == 2);
	Term* arg1 = args[0];
	if(arg1->get_term_type() != FUNCTION_TERM) return false;
	FunctionTerm* arg_ft = (FunctionTerm*) arg1;
	string arg_name = arg_ft->get_name();
	if(arg_name != DEREF_TERM) return false;
	const vector<Term*>& deref_args = arg_ft->get_args();
	assert(deref_args.size() == 1);
	Term* deref_arg = deref_args[0];
	if(deref_arg != base_t) return false;
	return true;
}

Term* increment_index_fun(Term* t)
{
	switch(t->get_term_type())
	{
	case CONSTANT_TERM:
		return t;
	case VARIABLE_TERM:
		if(t == base_t) {
			map<Term*, long int> elems;
			elems[t] = 1;
			elems[delta_t] = 1;
			return ArithmeticTerm::make(elems, 0);
		}
		else return t;

	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*) t;

		string name = ft->get_name();

		if(name == ARRAYREF_TERM)
		{
			if(!arrayterm_has_base(ft)) return t;
			const vector<Term*>& args = ft->get_args();
			Term* old_index = args[1];
			map<Term*, long int> elems;
			elems[old_index] = 1;
			elems[delta_t] = 1;
			Term* new_index = ArithmeticTerm::make(elems, 0);

			vector<Term*> new_args;
			new_args.push_back(args[0]);
			new_args.push_back(new_index);
			Term* new_array = FunctionTerm::make(ft->get_id(), new_args);
			return new_array;
		}

		else if(name == SIZE_FIELD_TERM)
		{
			const vector<Term*>& args = ft->get_args();
			Term* _array = args[0];
			if(_array->get_term_type() != FUNCTION_TERM) {
				return t;
			}
			FunctionTerm* array = (FunctionTerm*) _array;
			if(!arrayterm_has_base(array)) {
				return t;
			}

			Term* new_arg  = array;
			vector<Term*> new_args;
			new_args.push_back(new_arg);
			t= FunctionTerm::make(ft->get_id(), new_args);

			map<Term*, long int> elems;
			elems[t] = 1;
			elems[delta_t] = -1;
			return ArithmeticTerm::make(elems, 0);
		}
		else return t;


	}
	default:
		return t;

	}
}

c_id ConstraintSolver::increment_index(c_id old_id, AccessPath* base,
		AccessPath* delta)
{
	base_t = make_term(base);
	assert(base_t!=NULL);
	delta_t = make_term(delta);
	assert(delta_t!=NULL);
	assert(delta_t != base_t);
	constraint_type ct = constraints[old_id];
	CNode* nc= ct.first;
	CNode* sc = ct.second;

	CNode* new_nc = nc->substitute(increment_index_fun);
	CNode* new_sc;
	if(nc!=sc)
		new_sc = sc->substitute(increment_index_fun);
	else new_sc = new_nc;
	ct = constraint_type(new_nc, new_sc);
	return get_id(ct);


}

void ConstraintSolver::get_free_vars(c_id id, set<string>& vars)
{
	constraint_type ct = constraints[id];
	CNode* nc = ct.first;
	CNode* sc = ct.second;
	assert(nc!=NULL && sc!=NULL);
	nc->get_vars(vars);
	if(nc!=sc) sc->get_vars(vars);
}
*/

void ConstraintSolver::get_free_vars(c_id id, set<Term*>& vars)
{
	constraint_type ct = constraints[id];
	CNode* nc = ct.first;
	CNode* sc = ct.second;
	assert(nc!=NULL && sc!=NULL);
	nc->get_vars(vars);
	if(nc!=sc) sc->get_vars(vars);
}



int ConstraintSolver::msa(set<VariableTerm*> & msa_res, c_id id,
		map<VariableTerm*, int>& costs)
{
	constraint_type ct = constraints[id];
	CNode* nc = ct.first;

	assert(nc!=NULL);
	MSAFinder msa(nc, costs);
	msa_res = msa.get_vars_in_msa();
	return msa.get_cost();
}

pair<CNode*, CNode*> ConstraintSolver::get_cnodes(c_id id)
{
	constraint_type ct = constraints[id];
	return ct;
}

int ConstraintSolver::msa(set<VariableTerm*> & msa_res, c_id id, set<c_id> & bg,
		map<VariableTerm*, int>& costs)
{
	constraint_type ct = constraints[id];
	CNode* nc = ct.first;

	assert(nc!=NULL);
	set<CNode*> bg_nodes;
	set<c_id>::iterator it = bg.begin();
	for(; it != bg.end(); it++) {
		constraint_type cur = constraints[*it];
		bg_nodes.insert(cur.first);

	}



	MSAFinder msa(nc, bg_nodes, costs);
	msa_res = msa.get_vars_in_msa();

	return msa.get_cost();
}


/*
 * Given a map from d(i) to its NC(i) or SC(i), returns (by reference)
 * another map that contains the relevant instantiations of this map
 * according to terms used in c.
 */
void ConstraintSolver::instantiate_axioms(CNode* constraint,
		map<CNode*, CNode*>& axioms, map<CNode*, CNode*> & instantiated_axioms)
{

	set<CNode*>& axiom_keys = bg_keys;

	/*
	 * Identify the instantiation set for each function id.
	 */
	map<int, set<Term*> > instantiation_set;
	constraint->get_all_first_arguments(fn_ids, instantiation_set);

	set<Term*> all_inst_terms;
	{
		map<int, set<Term*> >::iterator it = instantiation_set.begin();
		for(; it!= instantiation_set.end(); it++)
		{
			set<Term*>& cur_inst = it->second;
			all_inst_terms.insert(cur_inst.begin(), cur_inst.end());
		}
	}

	set<CNode*>::iterator it = axiom_keys.begin();
	for(; it!= axiom_keys.end(); it++)
	{
		CNode* cur_key = *it;
		CNode* cur_val = axioms[cur_key];

		set<int> fun_ids;
		cur_key->get_all_fun_ids(fun_ids);
		assert(fun_ids.size() <=1);

		if(fun_ids.size() == 0)
		{
			instantiated_axioms[cur_key] = cur_val;
		}

		// We need to instantiate cur val with all values in the instantiation set
		else {
			int fn_id = *fun_ids.begin();
			set<Term*>::iterator it = all_inst_terms.begin();
			for(; it!= all_inst_terms.end(); it++)
			{
				Term* inst_term = *it;
				map<int, Term*> subs;
				subs[fn_id] = inst_term;
				CNode* inst_key = cur_key->replace_first_argument(subs);
				CNode* inst_val = cur_val->replace_first_argument(subs);
				instantiated_axioms[inst_key] = inst_val;

			}


		}
	}
}

void ConstraintSolver::replace_term_in_axioms(Term* old_t, Term* new_t)
{

	map<Term*, Term*> subs;
	subs[old_t] = new_t;
	if(general_background != NULL)
		general_background = general_background->substitute(subs);

	map<CNode*, pair<CNode*, CNode*> >::iterator it = background.begin();
	for(; it!= background.end(); it++)
	{
		pair<CNode*, CNode*> & cur = it->second;
		cur.first = cur.first->substitute(subs);
		cur.second = cur.second->substitute(subs);
	}

	map<CNode*, CNode*>::iterator it2 = nc_reps.begin();
	for(; it2!= nc_reps.end(); it2++)
	{
		it2->second = it2->second->substitute(subs);
	}
	it2 = sc_reps.begin();
	for(; it2!= sc_reps.end(); it2++)
	{
		it2->second = it2->second->substitute(subs);
	}
}

CNode* ConstraintSolver::get_background_dependencies(CNode* constraint, bool use_nc)
{
/*	{	cout << "======BG DEPENDENCIES========" << endl;

	map<CNode*, pair<CNode*, CNode*> >::iterator it = background.begin();
	for(; it!= background.end(); it++) {
		cout << "\t " << it->first->to_string() << " -> (" <<
				it->second.first->to_string() << ", "
				<< it->second.second->to_string() << endl;
	}
	cout << "======BG DEPENDENCIES end========" << endl;
	}*/

	set<CNode*> dependencies;

	/*
	 * First, identify all the relevant axioms we need to take into
	 * account to determine satisfiability.
	 */
	set<CNode*> axiom_keys;
	get_relevant_axioms(constraint, axiom_keys);

	/*
	 * Identify the instantiation set for each function id.
	 */
	map<int, set<Term*> > instantiation_set;
	constraint->get_all_first_arguments(fn_ids, instantiation_set);

	/*
	 * Finally, we go over the axioms keys; if they contain any
	 * function ids, we look up their instantiation set and conjoin the
	 * instantiated axioms; if they don't contain function terms,
	 * we just conjoin the value in the background map.
	 */
	set<CNode*>::iterator it = axiom_keys.begin();
	for(; it!= axiom_keys.end(); it++)
	{
		CNode* cur_key = *it;
		set<int> fn_ids;
		cur_key->get_all_fun_ids(fn_ids);
		assert(fn_ids.size() <=1);

		CNode* axiom;
		if(use_nc) axiom = background[cur_key].first;
		else axiom = background[cur_key].second;



		// Simple case: This is a ground axiom
		if(fn_ids.size() == 0)
		{
			dependencies.insert(axiom);
		}

		/* Difficult case: We have a quantified axiom; we need
		 * to insert all relevant instantiations of this axiom
		*/
		else {
			int fn_id = *fn_ids.begin();
			set<Term*>& inst_set = instantiation_set[fn_id];

			set<Term*>::iterator it = inst_set.begin();
			for(; it!= inst_set.end(); it++)
			{
				Term* t = *it;
				map<int, Term*> replacements;
				replacements[fn_id] = t;
				CNode* cur_inst_axiom =
						axiom->replace_first_argument(replacements);
				dependencies.insert(cur_inst_axiom);

			}

		}
	}

	CNode* res = Connective::make_and(dependencies);
	return res;
}

CNode* ConstraintSolver::include_background_dependencies(CNode* constraint,
		bool use_nc)
{

	CNode* dependencies = get_background_dependencies(constraint, use_nc);
	return Connective::make(AND, constraint, dependencies);

}

void ConstraintSolver::get_relevant_axioms(CNode* constraint, set<CNode*>&
		relevant_axioms)
{
	CNode* generalized_constraint =
			constraint->replace_first_argument(fn_to_qvars);
	set<CNode*> literals;
	generalized_constraint->get_all_literals(literals);
	set_intersection(bg_keys.begin(), bg_keys.end(), literals.begin(),
			literals.end(), insert_iterator<set<CNode*> > (relevant_axioms,
					relevant_axioms.begin()));
}


int ConstraintSolver::nc_size(c_id id)
{
	constraint_type key_t = constraints[id];
	CNode* nc = key_t.first;
	return nc->get_size();
}


int ConstraintSolver::sc_size(c_id id)
{
	constraint_type key_t = constraints[id];
	CNode* sc = key_t.second;
	return sc->get_size();
}



c_id ConstraintSolver::propagate_background(c_id id)
{
	constraint_type key_t = constraints[id];
	CNode* nc = key_t.first;
	CNode* sc = key_t.second;


	CNode* nc_dependencies = get_background_dependencies(nc, true);
	CNode* sc_dependencies = get_background_dependencies(nc, false);
	set<CNode*> nc_constraints;
	nc_constraints.insert(nc);
	nc_constraints.insert(nc_dependencies);
	nc_constraints.insert(sc_dependencies);
	CNode* new_nc = Connective::make_and(nc_constraints);


	set<CNode*> sc_constraints;
	nc_dependencies = get_background_dependencies(sc, true);
	sc_dependencies = get_background_dependencies(sc, false);
	sc_constraints.insert(sc);
	sc_constraints.insert(nc_dependencies);
	sc_constraints.insert(sc_dependencies);
	CNode* new_sc = Connective::make_and(sc_constraints);



	constraint_type new_ct(new_nc, new_sc);
	return get_id(new_ct);



	//------------------------------------
/*
	map<CNode*, CNode*> inst_nc_reps;
	map<CNode*, CNode*> inst_sc_reps;

	instantiate_axioms(nc, nc_reps, inst_nc_reps);
	instantiate_axioms(sc, sc_reps, inst_sc_reps);


	while(true)
	{
		CNode* new_nc = nc->substitute(inst_nc_reps);
 		if(new_nc == nc) break;
		nc = new_nc;
	}

	while(true)
	{
		CNode* new_sc = sc->substitute(inst_sc_reps);
		if(new_sc == sc) break;
		sc = new_sc;
	}
	constraint_type ct(nc, sc);
	return get_id(ct); */
}

void ConstraintSolver::add_to_rep_map(CNode* key, CNode* orig_nc, CNode* orig_sc)
{

	CNode* nc = orig_nc;
	CNode* sc = orig_sc;
	if(nc_reps.count(key) > 0)
	{
		CNode* existing_nc = nc_reps[key];
		nc = Connective::make(AND, nc, existing_nc);
	}

	if(sc_reps.count(key) > 0)
	{
		CNode* existing_sc = sc_reps[key];
		sc = Connective::make(OR, sc, existing_sc);
	}

	nc_reps[key] = nc;
	sc_reps[key] = sc;

	CNode* key_negation = Connective::make_not(key);
	CNode* nc_of_neg = Connective::make_not(orig_sc);
	CNode* sc_of_neg = Connective::make_not(orig_nc);
	if(nc_reps.count(key_negation) > 0)
	{
		CNode* existing_nc = nc_reps[key_negation];
		nc_of_neg = Connective::make(AND, nc_of_neg, existing_nc);
	}
	if(sc_reps.count(key_negation) > 0)
	{
		CNode* existing_sc = sc_reps[key_negation];
		sc_of_neg = Connective::make(OR, sc_of_neg, existing_sc);
	}

	nc_reps[key_negation] = nc_of_neg;
	sc_reps[key_negation] = sc_of_neg;


}

void ConstraintSolver::add_axiom(c_id key_id, c_id id, bool check_function_term)
{


	constraint_type key_t = constraints[key_id];
	CNode* key = key_t.first;
	assert(key == key_t.second);
	if(!key->is_literal()){
		cerr << "Trying to add axiom with non-literal: " << key->to_string() << endl;
		return;
	}


	constraint_type value_t = constraints[id];
	CNode* nc = value_t.first;
	CNode* sc = value_t.second;
	add_to_rep_map(key, nc, sc);



	nc = include_background_dependencies(nc, true);
	sc = include_background_dependencies(sc, false);




	add_background(key, nc, sc);






	CNode* key_negation = Connective::make_not(key);
	CNode* nc_neg = Connective::make_not(nc);
	CNode* sc_neg = Connective::make_not(sc);
	add_background(key_negation, sc_neg, nc_neg);



	if(!check_function_term) return;
	set<int> fun_ids;
	key->get_all_fun_ids(fun_ids);
	if(fun_ids.size() == 0) return;
	assert(fun_ids.size() == 1);
	int fn_id = *fun_ids.begin();
	map<int, set<Term*> > _args;
	key->get_all_first_arguments(fun_ids, _args );
	set<Term*>& args = _args[fn_id];
	assert(args.size() == 1);
	Term* qvar = *args.begin();
	fn_to_qvars[fn_id] = qvar;
	fn_ids.insert(fn_id);

}

CNode* ConstraintSolver::simplify(CNode* c)
{
	int start = clock();
	Solver s(c, SIMPLIFICATION_LEVEL, NULL);
	int end = clock();
	int cur_time = end-start;
	bg_simp_time += cur_time;
	add_to_hardest(hardest, cur_time, "[S] " + c->to_string());
	c = s.get_result();
	return c;

}

/*
 * sc => key => nc
 */
void ConstraintSolver::add_background(CNode* key, CNode* nc, CNode* sc)
{

	nc = Connective::make_implies(key, nc);
	sc = Connective::make_implies(sc, key);


	if(background.count(key) > 0)
	{
		pair<CNode*, CNode*> & existing = background[key];
		nc = Connective::make(AND, existing.first, nc);
		sc = Connective::make(AND, existing.second, sc);


	}


	// Simplify nc and sc
	nc = simplify(nc);
	sc = simplify(sc);

	background[key] = make_pair(nc, sc);


	bg_keys.insert(key);


}


void ConstraintSolver::set_background_knowledge(c_id id)
{

	constraint_type c = constraints[id];
	if(c.first->get_type() == TRUE_NODE) return;

	if(general_background == NULL) {
		general_background = c.first;
		if(general_background->get_type() == FALSE_NODE) bg_false = true;
		return;
	}
	else {
		general_background =
				Connective::make(AND, general_background, c.first)->refactor();
	}
	/*
	 * Ensure that general_background becomes False if UNSAT.
	 */
	int start = clock();
	Solver s(general_background, UNSAT_SIMPLIFY, NULL);
	int end = clock();
	int cur_time = end-start;
	bg_simp_time += cur_time;
	add_to_hardest(hardest, cur_time, "[U] " + general_background->to_string());

	general_background = s.get_result();
	if(general_background->get_type() == FALSE_NODE) bg_false = true;
	if(general_background->get_type() == TRUE_NODE) general_background = NULL;

}





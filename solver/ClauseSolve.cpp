/*
 * ClauseSolve.cpp
 *
 *  Created on: Feb 8, 2009
 *      Author: tdillig
 */

#include "ClauseSolve.h"
#include "UniversalInstantiator.h"
#include "Solver.h"
#include "term.h"
#include "cnode.h"
#include "Clause.h"
#include "Matrix.h"
#include "ilp-solve.h"

#define DEBUG false
#define ASSERT_ENABLED false

#define STATS false

#define MOD_PREFIX "$m"


ClauseSolve::ClauseSolve(CNode* node,
		map<Term*, SatValue>* assignments)
{
	repeated_solve = false;
	reset_branch_counters();
	if(STATS) init_stats();
	while(true)
	try{
		this->assignments = assignments;
		m = NULL;
		if(DEBUG) {
			cout << "Clause solve called with " << node->to_string() << endl;
		}
		sat = solve(node);
		if(STATS) print_stats();
		return;
	} catch(...)
	{
		if(DEBUG)
			cout << "Repeating clause... " << endl;
		clear();
		repeated_solve = true;
	}


}

ClauseSolve::ClauseSolve(Clause* clause,
		map<Term*, SatValue>* assignments)
{
	repeated_solve = false;
	if(STATS) init_stats();
	while(true)
	{
	try {
		this->assignments = assignments;
		this->cl = clause;
		init_top_level_terms();
		cl->denest(&denestings);
		m = NULL;
		reset_branch_counters();
		sat = clause_sat();
		if(STATS) print_stats();
		return;
	}
	catch(...)
	{
		if(DEBUG)
			cout << "Repeating clause... " << endl;
		clear();
		repeated_solve = true;
	}
	}


}

void ClauseSolve::print_stats()
{

	cout << "Clause Solve Stats:" << endl;
	cout << "--------------------" << endl;
	cout << "Time total ilp: " << (double)time_total_ilp/CLOCKS_PER_SEC << endl;
	cout << "Time total union find: " << (double)time_total_union_find/
			CLOCKS_PER_SEC << endl;
	cout << "Num interaction queries: " << num_interaction_queries << endl;
	cout << "Time preparing/refining queries: " <<
			(double)time_preparing_queries/CLOCKS_PER_SEC << endl;
	cout << "Time denesting: " << (double)time_denesting/CLOCKS_PER_SEC << endl;
	cout << "Time initial ilp: " << (double)time_initial_ilp/
			CLOCKS_PER_SEC<< endl;
	cout << "Time initial union find: " << (double)time_initial_union_find/
			CLOCKS_PER_SEC << endl;
}

void ClauseSolve::init_stats()
{
	time_denesting = 0;
	time_initial_ilp = 0;
	time_initial_union_find = 0;
	time_total_ilp = 0;
	time_total_union_find = 0;
	time_preparing_queries = 0;
	start = 0;
	num_interaction_queries = 0;
}

void ClauseSolve::clear()
{
	cl = NULL;
	eq_members.clear();
	eq_size.clear();
	eq_class_const.clear();
	eq_parents.clear();
	var_to_col_map.clear();
	vars.clear();
	ilp_vars.clear();
	function_vars.clear();
	neq_constraints.clear();
	top_level_terms.clear();
	denestings.clear();
	constants.clear();
}

void ClauseSolve::init_top_level_terms_term(Term* t)
{
	switch(t->get_term_type())
	{
	case CONSTANT_TERM:
	case VARIABLE_TERM:
		return;
	case FUNCTION_TERM:
	{
		FunctionTerm* ft = (FunctionTerm*) t;
		const vector<Term*>& args = ft->get_args();
		for(unsigned int i=0; i<args.size(); i++)
		{
			Term* cur = args[i];
			init_top_level_terms_term(cur);
		}
		return;
	}
	case ARITHMETIC_TERM:
	{
		ArithmeticTerm* at = (ArithmeticTerm*) t;
		const map<Term*, long int>& terms = at->get_elems();
		map<Term*, long int>::const_iterator it = terms.begin();
		for(; it!= terms.end(); it++)
		{
			Term* cur = it->first;
			if(cur->contains_var()){
				top_level_terms.insert(cur);
				init_top_level_terms_term(cur);
			}
		}
		return;
	}
	default:
		assert(false);

	}
}

inline void ClauseSolve::init_top_level_terms_eq(set<EqLeaf*>& eq_leaves)
{
	set<EqLeaf*>::iterator it = eq_leaves.begin();
	for(; it!= eq_leaves.end(); it++)
	{
		EqLeaf* eq = *it;
		Term* rhs = eq->get_rhs();
		Term* lhs = eq->get_lhs();
		if(rhs->contains_var()) {
			top_level_terms.insert(rhs);
			init_top_level_terms_term(rhs);
		}
		if(lhs->contains_var())
		{
			top_level_terms.insert(lhs);
			init_top_level_terms_term(lhs);
		}

	}
}
inline void ClauseSolve::init_top_level_terms_ilp(set<ILPLeaf*>& ilp_leaves)
{
	set<ILPLeaf*>::iterator it = ilp_leaves.begin();
	for(; it!= ilp_leaves.end(); it++)
	{
		ILPLeaf* ilp = *it;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it2 = elems.begin();
		for(; it2!= elems.end(); it2++){
			Term* t = it2->first;
			if(t->contains_var()) {
				top_level_terms.insert(t);
				init_top_level_terms_term(t);
			}
		}
	}
}
inline void ClauseSolve::init_top_level_terms_mod(set<ModLeaf*>& mod_leaves)
{
	set<ModLeaf*>::iterator it = mod_leaves.begin();
	for(; it!= mod_leaves.end(); it++){
		ModLeaf* mod = *it;
		Term* t = mod->get_term();
		if(t->contains_var()) {
			if(t->get_term_type() != ARITHMETIC_TERM)
				top_level_terms.insert(t);
			init_top_level_terms_term(t);
		}
	}
}

void ClauseSolve::init_top_level_terms()
{
	if(assignments == NULL) return;
	init_top_level_terms_eq(cl->pos_eq);
	init_top_level_terms_eq(cl->neg_eq);
	init_top_level_terms_ilp(cl->pos_ilp);
	init_top_level_terms_ilp(cl->neg_ilp);
	init_top_level_terms_mod(cl->pos_mod);
	init_top_level_terms_mod(cl->neg_mod);
}


bool ClauseSolve::is_sat()
{
	return sat;
}

/*
 * Commented out the literal case due to problems with unsigned
 */
bool ClauseSolve::solve(CNode* _node)
{

	assert(_node->is_conjunct());
	if(_node->get_type() == FALSE_NODE) return false;
	/*if(_node->is_literal() && _node->get_type() != UNIVERSAL){
		if(solver!= NULL) solver->literal_count++;
		//Returning here does not generate a valid assignment
		if(assignments==NULL)
			return true;
	}*/
	UniversalInstantiator ui(_node);
	CNode* node = ui.get_constraint();

	assert(node != NULL);
	if(!node->is_conjunct()) {
		CNode* res;
		Solver s(node, UNSAT_SIMPLIFY, assignments);
		res = s.get_result();


		if(res->get_type() == FALSE_NODE) return false;
		return true;
	}
	if(node->get_type() == FALSE_NODE) return false;
	/*if(node->is_literal()){
		if(solver != NULL) solver->literal_count++;
		if(assignments==NULL)
			return true;
	}*/


	CNode* simp_node = _node->get_simplification(UNSAT_SIMPLIFY);
	if(simp_node != NULL && assignments == NULL) {
		return (simp_node->get_type() != FALSE_NODE);
	}


	if(node->get_type() == FALSE_NODE) return false;
	cl = new Clause(node);
	init_top_level_terms();

	if(STATS) start = clock();
	cl->denest(&denestings);
	if(STATS) {
		int end = clock();
		time_denesting = end-start;
	}

	if(DEBUG)
	{
		cout << "============DENESTINGS:===============" << endl;
		map<Term*, Term*>::iterator it = denestings.begin();
		for(; it!= denestings.end(); it++){
			cout << "\t " << it->first->to_string() << ": " << it->second->to_string()
				<< endl;
		}
		cout << "============END DENESTINGS===============" << endl;

		cout << "DENESTED CLAUSE: " << cl->to_string("&") << endl;
	}


	bool res = clause_sat();
	delete cl;
	if(!res) {
		_node->set_simplification(False::make(), UNSAT_SIMPLIFY);
	}
	else {
		_node->set_simplification(_node, UNSAT_SIMPLIFY);
	}

	return res;
}

ClauseSolve::~ClauseSolve() {
	delete m;

}

void ClauseSolve::print_neq_matrix()
{
	set<set< pair<Equation*, bignum> > >::iterator it = neq_constraints.begin();
	for(; it!= neq_constraints.end(); it++) {
		set< pair<Equation*, bignum> >::iterator it2 = it->begin();
		for(; it2!= it->end(); it2++){
			if(it2!= it->begin()) cout << " | ";
			cout << it2->first->to_string() << " != " << it2->second;
		}
		cout << endl;
	}
}

void ClauseSolve::print_congruence_classes()
{
	map<Term*, set<Term*> >::iterator it = eq_members.begin();
	for(; it!=eq_members.end(); it++){
		Term* rep = it->first;
		cout << "EQ CLASS OF: " << rep->to_string() << endl;
		set<Term*>::iterator it2= it->second.begin();
		for(; it2!=it->second.end(); it2++) {
			cout << "\t " << (*it2)->to_string() << endl;
		}
	}
}

// -----------------------------------------------------------------
/*
 * Determines the satisfiability of a single clause containing
 * ILP and function terms. It first runs union-find
 * to infer congruence classes, adds inferred equalities and
 * inequalities to the ILP domain, and queries the
 * ILP solver. If the result is not UNSAT,
 * it then builds a set of queries (via the interaction
 * manager) to ask the ILP solver. If any of these queries
 * is implied in the theory of integers, we then merge
 * the equivalence classes of the terms and again add
 * any inferred equalities and inequalities to the ILP
 * domain. Eventually, either we conclude UNSAT or run
 * out of queries to make, which means the clause is SAT.
 */
bool ClauseSolve::clause_sat()
{


	/*
	 * Function terms and eq_terms are both used for query building.
	 */
	set<int> function_terms;
	set<Term*> eq_terms;
	vector<bignum> ilp_assignments_vec;

	init_congruence_classes(function_terms, eq_terms);

	if(DEBUG) {
		cout << "********INITIAL CONGRUENCE CLASSES********" << endl;
		print_congruence_classes();
		cout << "********************************************" << endl;
	}

	/*
	 * Process all equalities via congruence closure and check for contradictions
	 */
	if(STATS) start = clock();
	bool res_eq = process_equalities();
	if(STATS) {
		int end = clock();
		time_initial_union_find = end-start;
		time_total_union_find += time_initial_union_find;
	}

	// If we already found a contradiction between equalities and inequalities,
	// we are done.
	if(!res_eq)
		return false;

	if(cl->pos_ilp.size() == 0 && cl->neg_ilp.size() == 0 &&
			cl->pos_mod.size() == 0 && cl->neg_mod.size() == 0 ) {
		generate_sat_assignment(&ilp_assignments_vec);
		return true;
	}




	// Replace each shared var in the ilp domain with its eq class represenative.
	// If this results in an eq contradiction, we are done.
	//if(!minimize_shared_variables(function_terms, eq_terms))
	//	return false;

	// compute set of variables in ilp leaves (this includes everything in
	// the congruence class of any variable appearing in an ilp leaf.)
	compute_ilp_var_ids();


	if(DEBUG) {
		cout << "ILP VARIABLES:" << endl;
		set<int>::iterator it = ilp_vars.begin();
		for(; it!= ilp_vars.end(); it++){
			cout << "Var: " << CNode::get_varmap().get_name(*it) << "\t";
		}
		cout << endl;
	}

	/*
	 * Build a mapping from ilp variables to their respective columns in the
	 * matrix and populate the vars set used for giving satisfying assignments
	 * by the ILP solver.
	 */

	build_var_to_col_map();


	// Constructs the initial ILP matrix, populating rows with  ILP constraints
	construct_ilp_matrix();



	/*
	 * Construct the interaction manager class, which figures out the
	 * set of inferred equalities and inequalities between ILP variables,
	 * and builds a set of queries we might later need to ask the ILP domain.
	 */
	if(STATS) start = clock();

	InteractionManager im(this, eq_terms, function_terms);


	/*
	 * Add all inferred equalities and inequalities between ILP vars to the
	 * matrix.
	 */
	im.add_inferred_equalities();
	im.add_inferred_inequalities();

	/*
	 * Figure out the set of queries we need to make.
	 */
	im.build_queries();

	if(STATS) {
		int end = clock();
		time_preparing_queries += end-start;
	}



	/*
	 * Query the ILP solver.
	 */
	if(STATS) start = clock();
	bool ilp_res = ilp_sat(*m, neq_constraints, &ilp_assignments_vec, false);
	if(STATS) {
		int end = clock();
		time_initial_ilp = end-start;
		time_total_ilp += time_initial_ilp;
	}



	if(DEBUG) {
		cout << "Initial ILP eq matrix : \n" << *m << endl;
		cout << "Intial ILP NEQ matrix:\n";
		print_neq_matrix();
	}



	// If ILP says UNSAT, we are done.
	if(!ilp_res)
	{
		return false;
	}


	get_ilp_assignment(ilp_assignments_vec);
	if(check_assignment()) {
		generate_sat_assignment(&ilp_assignments_vec);
		return true;
	}

	if(STATS) start = clock();
	im.refine_queries();
	if(STATS) {
		int end = clock();
		time_preparing_queries += end-start;
	}


	/*
	 * Now get all the queries we need to ask the ILP domain
	 * and keep asking until we either find UNSAT or we exhaust all
	 * the queries, which means we return SAT.
	 */
	set<ILPQuery*> & queries = im.get_queries();
	if(DEBUG) {
		cout << "All Queries: " <<im.queries_to_string() << endl;
	}

	while(queries.size() >0)
	{
		ILPQuery* q = *queries.begin();
		queries.erase(q);
		if(DEBUG) cout << "ILP QUERY: " << q->to_string() << endl;
		if(STATS) num_interaction_queries++;

		/* We need to query if all equalities in this query are implied
		 * by the ILP domain. To do this, we negate each equality (by adding
		 * it to the neq_matrix) and check if the result in UNSAT, which
		 * means the equality is implied.
		 */
		Term* lhs = q->t1;
		Term* rhs = q->t2;
		delete q;

		if(find_representative(lhs)==find_representative(rhs)) continue;
		set<pair<Term*, Term*> > ineq;
		ineq.insert(make_pair(lhs, rhs));
		set<pair<Equation*, bignum> > new_inequality;
		bool added_ineq = add_inequality(ineq, new_inequality);
		if(!added_ineq) continue;


		if(STATS) start = clock();
		bool ilp_res1 = ilp_sat(*m,  neq_constraints,
				&ilp_assignments_vec, false);
		if(STATS) {
			int end = clock();
			time_total_ilp += end-start;
		}

		get_ilp_assignment(ilp_assignments_vec);
		if(check_assignment()) {
			generate_sat_assignment(&ilp_assignments_vec);
			return true;
		}

		if(STATS) start = clock();
		queries = im.refine_queries();
		if(STATS) {
			int end = clock();
			time_preparing_queries += end -start;
		}

		neq_constraints.erase(new_inequality);

		set<pair<Equation*, bignum> >::iterator it = new_inequality.begin();
		for(; it!= new_inequality.end(); it++)
		{
			delete it->first;
		}

		if(ilp_res1) continue;


		if(DEBUG) cout << "Query " << lhs->to_string() <<
		 " = " << rhs->to_string() << "is implied " << endl;

		/*
		 * If the query is implied by the ILP domain, we can union
		 * the equivalence classes that we issued the query for.
		 */
		if(STATS) start = clock();
		bool union_res = perform_union(lhs, rhs);
		if(STATS) {
			int end = clock();
			time_total_union_find += end-start;
		}
		if(!union_res){
			return false;
		}

		if(has_contradiction()){
			return false;
		}

		if(STATS) start = clock();
		/*
		 * After performing union, if we infer any new qualities and
		 * inequalities, add them to the ILP domain.
		 */
		bool new_eq = im.add_inferred_equalities();

		bool new_neq = im.add_inferred_inequalities();

		if(STATS) {
			int end = clock();
			time_preparing_queries += end-start;
		}

		if(!new_eq && !new_neq)
			continue;

		if(STATS) start = clock();
		/*
		 * If we inferred any new equalities or inequalities, we recheck
		 * the ILP domain. If it says UNSAT, we are done; otherwise, we keep
		 * processing the queries.
		 */
		bool ilp_res = ilp_sat(*m, neq_constraints,
				&ilp_assignments_vec,  false);

		if(STATS) {
			int end = clock();
			time_total_ilp += end-start;
		}

		get_ilp_assignment(ilp_assignments_vec);
		if(check_assignment()) {
			generate_sat_assignment(&ilp_assignments_vec);
			return true;
		}

		if(STATS) start = clock();
		queries = im.refine_queries();
		if(STATS) {
			int end = clock();
			time_preparing_queries += end -start;
		}

		if(!ilp_res)
		{
			return false;
		}
	}

	generate_sat_assignment(&ilp_assignments_vec);
	return true;
}

bool ClauseSolve::check_assignment()
{
	return false;
	bool valid_assignment = true;
	/*
	cout << "Checking assignment: " << endl;
	{
		map<Term*, bignum>::iterator it = ilp_assignments.begin();
		for(; it!= ilp_assignments.end(); it++) {
			Term* t = it->first;
			bignum & v = it->second;
			cout << "\t " << t->to_string() <<  ": " << v << endl;
		}
	}

	print_eq_classes();
	*/
	/*
	 * Save old state: eq_members, eq_size, eq_class_const, eq_parents
	 */
	map<Term*, set<Term*> > old_members = eq_members;
	map<Term*, int> old_sizes = eq_size;
	map<Term*, int> old_constants = eq_class_const;
	map<Term*, set<Term*> > old_parents = eq_parents;

	map<Term*, bignum>::iterator it = ilp_assignments.begin();
	set<Term*> new_consts;
	for(; it!= ilp_assignments.end(); it++) {
		Term* t = it->first;
		if(t->representative == NULL) continue; // pure ILP variable
		bignum& assign = it->second;
		if(!assign.fits_long_int()) {
			valid_assignment = false;
			break;
		}
		long int val = assign.to_int();

		Term* ct = ConstantTerm::make(val);
		if(constants.count(ct) == 0 && new_consts.count(ct) == 0){
			new_consts.insert(ct);
			ct->representative = ct;
			eq_members[ct].insert(ct);
			eq_size[ct] = 1;
			eq_class_const[ct] = val;
			eq_parents[ct];
		}


		if(!perform_union(t, ct)) {
			//cout << "PERFORM UNION RETURNED FALSE... (" << t->to_string() << ", " <<
				//val << ")" << endl;
			valid_assignment = false;
			break;
		}
		//print_eq_classes();

	}

	if(valid_assignment) {
		// We verified the assignment -- no reason to restore state.
		if(!has_contradiction()){

			//cout << "**************ASSIGNMENT CHECKED!!!" << endl;
			return true;
		}
		/*else {
			cout << "HAS CONTRADICTION.... "  << endl;
		}*/
	}

	/*
	 * Restore old state
	 */
	eq_members = old_members;
	eq_size = old_sizes;
	eq_class_const = old_constants;
	eq_parents = old_parents;

	{
		map<Term*, set<Term*> >::iterator it = eq_members.begin();
		for(; it!= eq_members.end(); it++)
		{
			Term* rep = it->first;
			set<Term*> & rep_class = it->second;
			set<Term*>::iterator it2 = rep_class.begin();
			for(; it2!= rep_class.end(); it2++) {
				Term* t = *it2;
				t->representative = rep;
			}
		}
	}
	//cout << "ASSIGNMENTS NOT CHECKED... " << endl;
	return false;

}

string ClauseSolve::eq_classes_to_string()
{
	string res;
	res+= "==========INITIAL EQUIAVLENCE CLASSES===========\n";
	map<Term*, set<Term*> >::iterator it = eq_members.begin();
	for(; it!=eq_members.end(); it++)
	{
		if(it->first->representative != it->first)
			continue;
		res+=  "\t {";
		set<Term*>::iterator it2 = it->second.begin();
		int i=0;
		for(; it2!= it->second.end(); it2++) {
			res+= (*it2)->to_string();
			//cout << "[" << *it2 << "]";
			if(i!= (int)it->second.size()-1) res+=  ", ";

		}

		res+=  "}\n";
	}
	res += "==================================================\n";
	return res;

}


void ClauseSolve::print_eq_classes()
{
	cout << eq_classes_to_string() << endl;
}


/*
inline bool ClauseSolve::minimize_shared_ilp_vars(set<ILPLeaf*>& ilp_leaves,
		bool pos, set<int> &function_terms, set<Term*> &eq_terms)
{
	set<ILPLeaf*> new_leaves;
	set<ILPLeaf*>::iterator it = ilp_leaves.begin();
	for(; it!= ilp_leaves.end(); it++)
	{
		ILPLeaf* ilp = *it;
		const map<Term*, long int>& terms = ilp->get_elems();
		map<Term*, long int>::const_iterator it2 = terms.begin();
		bool changed;
		map<Term*, long int> new_elems;
		long int constant = ilp->get_constant();
		for(; it2!= terms.end(); it2++) {
			Term* t = it2->first;
			Term* rep = find_representative(t);
			if(rep == NULL) {
				new_elems[t] += it2->second;
				continue;
			}
			if(eq_class_const.count(rep) > 0) {
				long int class_const = eq_class_const[rep];
				constant -= class_const*it2->second;
				changed = true;
				continue;
			}
			if(rep->get_term_type() != VARIABLE_TERM) rep = t;
			if(t != rep) changed = true;
			new_elems[rep] += it2->second;
		}

		if(!changed) {
			new_leaves.insert(ilp);
			continue;
		}


		CNode* new_node = ILPLeaf::make(ilp->get_operator(), new_elems, constant);
		new_node = new_node->get_canonical();
		cnode_type nt = new_node->get_type();
		if(pos && nt == FALSE_NODE) return false;
		else if(pos && nt == TRUE_NODE) continue;
		else if(!pos && nt == FALSE_NODE) continue;
		else if(!pos && nt == TRUE_NODE) return false;

		if(nt == EQ) {
			EqLeaf* eq = (EqLeaf*) new_node;
			Term* lhs = eq->get_lhs();
			Term* rhs = eq->get_rhs();
			eq_terms.insert(lhs);
			eq_terms.insert(rhs);
			if(lhs->representative == NULL)
			{
				set<Term*> cur_parents;
				init_congruence_classes_term(lhs, NULL,
								cur_parents, function_terms);

			}
			if(rhs->representative == NULL)
			{
				set<Term*> cur_parents;
				init_congruence_classes_term(rhs, NULL,
								cur_parents, function_terms);

			}

			if(!perform_union(eq->get_lhs(), eq->get_rhs()))
				return false;
			continue;

		}
		if(ASSERT_ENABLED) {
			assert(nt == ILP);
		}
		ILPLeaf* new_ilp = (ILPLeaf*) new_node;
		new_leaves.insert(new_ilp);
	}
	ilp_leaves = new_leaves;
	return true;

}

inline bool ClauseSolve::minimize_shared_mod_vars(set<ModLeaf*>& mod_leaves,
		bool pos)
{
	set<ModLeaf*> new_leaves;
	set<ModLeaf*>::iterator it = mod_leaves.begin();
	for(; it!= mod_leaves.end(); it++)
	{
		ModLeaf* mod = *it;
		Term* t = mod->get_term();
		Term* rep = find_representative(t);
		if(rep == NULL) {
			new_leaves.insert(mod);
			continue;
		}
		if(eq_class_const.count(rep) > 0) {
			rep = ConstantTerm::make(eq_class_const[rep]);
		}
		if(rep->get_term_type() != VARIABLE_TERM &&
				rep->get_term_type() != CONSTANT_TERM ) rep = t;
		if(rep == t) {
			new_leaves.insert(mod);
			continue;
		}

		CNode* new_node = ModLeaf::make(rep, mod->get_mod_constant());

		cnode_type nt = new_node->get_type();
		if(pos && nt == FALSE_NODE) return false;
		else if(pos && nt == TRUE_NODE) continue;
		else if(!pos && nt == FALSE_NODE) continue;
		else if(!pos && nt == TRUE_NODE) return false;
		if(ASSERT_ENABLED) {
			assert(nt == MOD);
		}
		ModLeaf* new_mod = (ModLeaf*) new_node;
		new_leaves.insert(new_mod);
	}
	mod_leaves = new_leaves;
	return true;
}

bool ClauseSolve::minimize_shared_variables(set<int> &function_terms,
		set<Term*> &eq_terms)
{
	if(!minimize_shared_ilp_vars(cl->pos_ilp, true, function_terms, eq_terms))
		return false;
	if(!minimize_shared_ilp_vars(cl->neg_ilp, false, function_terms, eq_terms))
		return false;
	if(!minimize_shared_mod_vars(cl->pos_mod, true)) return false;
	if(!minimize_shared_mod_vars(cl->neg_mod, false)) return false;
	return true;

}
*/

Term* ClauseSolve::find_representative(Term* t)
{
	if(t->representative == NULL)
		return NULL;
	while(t!=t->representative)
	{
		t = t->representative;
	}
	return t;
}

bool ClauseSolve::perform_union(Term* t1, Term* t2)
{

	Term* t1_rep = find_representative(t1);
	Term* t2_rep = find_representative(t2);

	if(t1_rep == t2_rep)
		return true;

	if(false && DEBUG){
		cout << "Performing union: " <<
		terms_to_string(eq_members[t1_rep]) << " and "
				<< terms_to_string(eq_members[t2_rep]) << endl;
	}

	if(have_contradictory_constants(t1_rep, t2_rep))
		return false;

	if(eq_size[t1_rep] < eq_size[t2_rep])
	{
		Term* temp = t1;
		t1 = t2;
		t2 = temp;
		temp = t1_rep;
		t1_rep = t2_rep;
		t2_rep = temp;
	}

	set<Term*> p1 = eq_parents[t1_rep];
	set<Term*> p2 = eq_parents[t2_rep];

	set<Term*> t1_members = eq_members[t1_rep];
	set<Term*> t2_members = eq_members[t2_rep];

	t2_rep->representative = t1_rep;

	eq_size[t1_rep]+=eq_size[t2_rep];
	eq_size.erase(t2_rep);

	if(eq_class_const.count(t2_rep) > 0){
		eq_class_const[t1_rep] = eq_class_const[t2_rep];
		eq_class_const.erase(t2_rep);
	}

	eq_parents[t1_rep].insert(p2.begin(), p2.end());
	eq_parents.erase(t2_rep);

	assert(eq_members.count(t1_rep) > 0);
	assert(eq_members.count(t2_rep) > 0);

	/*
	 * Join members of the two congruence classes.
	 */
	set<Term*> & l1 = eq_members[t1_rep];
	set<Term*> & l2 = eq_members[t2_rep];
	l1.insert(l2.begin(), l2.end());


	eq_members.erase(t2_rep);

	/*
	 * Propagate equality to parents if they are congruent.
	 */
	set<Term*>::iterator it1 = p1.begin();
	for(; it1!=p1.end(); it1++)
	{
		set<Term*>::iterator it2 = p2.begin();
		for(;it2!= p2.end(); it2++)
		{
			assert((*it1)->get_term_type() == FUNCTION_TERM);
			assert((*it2)->get_term_type() == FUNCTION_TERM);
			FunctionTerm* f1 = (FunctionTerm*)*it1;
			FunctionTerm* f2 = (FunctionTerm*)*it2;
			if(congruent(f1, f2)){
				if(!perform_union(f1, f2)) return false;
			}
		}
	}

	/*
	 * If the terms being union-ed are invertible function terms,
	 * then we also union their children.
	 */

	it1 = t1_members.begin();
	for(; it1!= t1_members.end(); it1++)
	{
		Term* mem1 = *it1;
		if(mem1->get_term_type() != FUNCTION_TERM) {
			continue;
		}
		FunctionTerm* f1 = (FunctionTerm*) mem1;
		if(!f1->is_invertible()) continue;
		const vector<Term*>& args1 = f1->get_args();

		set<Term*>::iterator it2 = t2_members.begin();
		for(; it2!= t2_members.end(); it2++)
		{
			Term* mem2 = *it2;
			if(mem2->get_term_type() != FUNCTION_TERM) continue;
			FunctionTerm* f2 = (FunctionTerm*) mem2;
			if(f2->get_id() != f1->get_id()) continue;
			const vector<Term*>& args2 = f2->get_args();

			// Now perform union with their respective arguments.
			for(unsigned int i=0; i<args1.size(); i++)
			{
				if(!perform_union(args1[i], args2[i]))
					return false;
			}




		}
	}



	return true;
}

bool ClauseSolve::perform_conditional_union(Term* t1, Term* t2, set<Term*>&
		changed_eq_classes, bool& used_function_axiom)
{
	Term* t1_rep = find_representative(t1);
	Term* t2_rep = find_representative(t2);
	if(t1_rep == t2_rep)
		return true;

	if(have_contradictory_constants(t1_rep, t2_rep))
		return false;

	if(eq_size[t1_rep] < eq_size[t2_rep])
	{
		Term* temp = t1;
		t1 = t2;
		t2 = temp;
		temp = t1_rep;
		t1_rep = t2_rep;
		t2_rep = temp;
	}

	set<Term*> p1 = eq_parents[t1_rep];
	set<Term*> p2 = eq_parents[t2_rep];

	set<Term*> & l1 = eq_members[t1_rep];
	set<Term*> & l2 = eq_members[t2_rep];

	/*
	 * Save state
	 */
	history_elem h(t2_rep, l2);
	h.has_constant = eq_class_const.count(t2_rep) > 0;
	if(h.has_constant) h.constant = eq_class_const[t2_rep];
	undo_buffer.push_back(h);
	changed_eq_classes.insert(t1_rep);

	t2_rep->representative = t1_rep;

	if(eq_class_const.count(t2_rep) > 0){
		eq_class_const[t1_rep] = eq_class_const[t2_rep];
		eq_class_const.erase(t2_rep);
	}

	/*
	 * Join members of the two congruence classes.
	 */
	l1.insert(l2.begin(), l2.end());



	/*
	 * Propagate equality to parents if they are congruent.
	 */
	set<Term*>::iterator it1 = p1.begin();
	for(; it1!=p1.end(); it1++)
	{
		set<Term*>::iterator it2 = p2.begin();
		for(;it2!= p2.end(); it2++)
		{
			assert((*it1)->get_term_type() == FUNCTION_TERM);
			assert((*it2)->get_term_type() == FUNCTION_TERM);
			FunctionTerm* f1 = (FunctionTerm*)*it1;
			FunctionTerm* f2 = (FunctionTerm*)*it2;
			if(f1->get_id() != f2->get_id()) continue;


			//if(congruent(f1, f2)){
				used_function_axiom = true;
				if(!perform_conditional_union(f1, f2, changed_eq_classes,
						used_function_axiom))
					return false;
			//}
		}
	}


	/*
	 * If the terms being union-ed are invertible function terms,
	 * then we also union their children.
	 */

	it1 = l1.begin();
	for(; it1!= l1.end(); it1++)
	{
		Term* mem1 = *it1;
		if(mem1->get_term_type() != FUNCTION_TERM) {
			continue;
		}
		FunctionTerm* f1 = (FunctionTerm*) mem1;
		if(!f1->is_invertible()) continue;
		const vector<Term*>& args1 = f1->get_args();

		set<Term*>::iterator it2 = l2.begin();
		for(; it2!= l2.end(); it2++)
		{
			Term* mem2 = *it2;
			if(mem2->get_term_type() != FUNCTION_TERM) continue;
			FunctionTerm* f2 = (FunctionTerm*) mem2;
			if(f2->get_id() != f1->get_id()) continue;
			const vector<Term*>& args2 = f2->get_args();

			// Now perform union with their respective arguments.
			for(unsigned int i=0; i<args1.size(); i++)
			{
				used_function_axiom = true;
				if(!perform_conditional_union(args1[i], args2[i], changed_eq_classes,
						used_function_axiom))
					return false;
			}




		}
	}


	return true;
}

void ClauseSolve::undo_conditional_union()
{
	for(int i=undo_buffer.size()-1; i>=0; i--)
	{
		history_elem h = undo_buffer[i];
		Term* old_rep = h.old_rep;
		Term* new_rep = old_rep->representative;
		old_rep->representative = old_rep;

		/*
		 * Update eq_members of new_rep.
		 */
		set<Term*>& new_rep_eq_members = eq_members[new_rep];
		set<Term*>::iterator it = h.eq_members->begin();
		for(; it!=h.eq_members->end(); it++)
		{
			Term* t = *it;
			new_rep_eq_members.erase(t);
			assert(new_rep_eq_members.count(t) == 0);
		}

		/*
		 * Update eq_constant
		 */
		if(h.has_constant) {
			int constant = h.constant;
			eq_class_const.erase(new_rep);
			eq_class_const[old_rep] = constant;
		}




	}


	undo_buffer.clear();
}

/*
 * Used to check whether we can propagate equality to parents.
 */
bool ClauseSolve::congruent(FunctionTerm* f1, FunctionTerm* f2)
{
	if(f1->get_id()!=f2->get_id())
		return false;
	for(unsigned int i=0; i < f1->get_args().size(); i++)
	{
		if(find_representative(f1->get_args()[i]) !=
			find_representative(f2->get_args()[i]))
			return false;
	}
	return true;
}

/*
 * Returns true if it did not find a contradiction after processing
 * the initial set of equalities.
 */
bool ClauseSolve::process_equalities()
{
	set<EqLeaf*> & pos_eq = cl->pos_eq;
	set<EqLeaf*>::iterator it = pos_eq.begin();
	for(; it!= pos_eq.end(); it++)
	{
		EqLeaf* l = (EqLeaf*) *it;
		if(!perform_union(l->get_lhs(), l->get_rhs())) return false;
	}
	return !has_contradiction();
}

/*
 * Given the set of congruence classes, checks for contradictions
 * with the != constraints.
 */
bool ClauseSolve::has_contradiction()
{
	set<EqLeaf*> & neg_eq = cl->neg_eq;
	set<EqLeaf*>::iterator it = neg_eq.begin();
	for(; it!= neg_eq.end(); it++)
	{
		EqLeaf* l = (EqLeaf*) *it;
		Term* lhs_rep = find_representative(l->get_lhs());
		Term* rhs_rep = find_representative(l->get_rhs());

		if(lhs_rep == rhs_rep)
			return true;
	}
	return false;
}

void ClauseSolve::init_congruence_classes(set<int> & function_ids,
		set<Term*> & equality_terms)
{

	clear_ilp_representatives(cl->pos_ilp);
	clear_ilp_representatives(cl->neg_ilp);
	clear_mod_representatives(cl->pos_mod);
	clear_mod_representatives(cl->neg_mod);

	set<EqLeaf*>::iterator it = cl->pos_eq.begin();
	for(; it != cl->pos_eq.end(); it++)
	{
		EqLeaf *l = (EqLeaf*)*it;
		set<Term*> cur_parents;
		init_congruence_classes_term(l->get_lhs(), NULL,
				cur_parents, function_ids);
		cur_parents.clear();
		init_congruence_classes_term(l->get_rhs(), NULL,
				cur_parents, function_ids);
		equality_terms.insert(l->get_lhs());
		equality_terms.insert(l->get_rhs());
	}
	it = cl->neg_eq.begin();
	for(; it != cl->neg_eq.end(); it++)
	{
		set<Term*> cur_parents;
		EqLeaf *l = (EqLeaf*)*it;
		init_congruence_classes_term(l->get_lhs(), NULL,
				cur_parents, function_ids);
		cur_parents.clear();
		init_congruence_classes_term(l->get_rhs(), NULL,
				cur_parents, function_ids);
		equality_terms.insert(l->get_lhs());
		equality_terms.insert(l->get_rhs());

	}

}

void  ClauseSolve::init_congruence_classes_term(Term *t, Term* parent,
		 set<Term*> &cur_parents, set<int> & function_ids)
{
	t->representative = t;
	if(eq_parents.count(t)==0)
		eq_parents[t] = cur_parents;
	else{
		set<Term*>& parents = eq_parents[t];
		parents.insert(cur_parents.begin(), cur_parents.end());
	}
	eq_size[t] = 1;
	set<Term*> members;
	members.insert(t);
	eq_members[t] = members;

	if(t->get_term_type() == CONSTANT_TERM){
			eq_class_const[t] = ((ConstantTerm*)t)->get_constant();
			constants.insert(t);
	}

	if(t->get_term_type() != FUNCTION_TERM)
		return;

	cur_parents.insert(t);
	FunctionTerm* ft = (FunctionTerm*)t;
	function_ids.insert(ft->get_id());
	const vector<Term*> & args = ft->get_args();
	for(unsigned int i=0;i<args.size(); i++)
	{
		Term* cur = args[i];
		if(cur->get_term_type() == VARIABLE_TERM){
			VariableTerm* vt = (VariableTerm*) cur;
			function_vars.insert(vt->get_var_id());
		}
		init_congruence_classes_term(cur, ft,  cur_parents, function_ids);


	}
	cur_parents.erase(t);
}

/*
 * Mapping from variable id's to their
 * corresponding column in the ILP matrix.
 */
void ClauseSolve::build_var_to_col_map()
{

	if(!repeated_solve)
	{
		int cur_col = 0;
		set<int>::iterator it = ilp_vars.begin();
		for(;it != ilp_vars.end(); it++)
		{
			var_to_col_map[*it] = cur_col++;
			vars.push_back(CNode::get_varmap().get_name(*it));
		}
		return;
	}

	/*
	 * If we are restarting the solve, reshuffle the columns of the
	 * matrix so that we have better luck solving the ILP problem.
	 */

	int size = ilp_vars.size();
	int indices[size];
	for(int i=0; i<size; i++)
	{
		indices[i] = i;
	}

	set<int>::iterator it = ilp_vars.begin();
	for(;it != ilp_vars.end(); it++)
	{
		int index = rand()%size;
		int cur_col = indices[index];
		for(int i = index; i<size-1; i++)
		{
			indices[i] = indices[i+1];
		}
		size--;
		var_to_col_map[*it] = cur_col;
		vars.push_back(CNode::get_varmap().get_name(*it));
	}

}

/*
 * Computes the set of variables that appear in the ILP domain.
 * Initially, every variable that appears in an ILP leaf will be an
 * ILP variable. In addition, everything that appears in the congruence class
 * of an initial ILP variable is also considered an ILP variable.
 */
void ClauseSolve::compute_ilp_var_ids()
{
	/*
	 * Compute the initial set of ILP variables.
	 */
	set<ILPLeaf*>::iterator it = cl->pos_ilp.begin();
	for(; it!= cl->pos_ilp.end(); it++)
	{
		ILPLeaf *l = (ILPLeaf*) *it;
		const map<Term*, long int > & elems = l->get_elems();
		map<Term*, long int >::const_iterator eit = elems.begin();
		for(; eit!= elems.end(); eit++)
		{
			Term* t = eit->first;
			assert(t->get_term_type() == VARIABLE_TERM);
			VariableTerm* vt = (VariableTerm*) t;
			int var_id= vt->get_var_id();
			ilp_vars.insert(var_id);
		}
	}
	it = cl->neg_ilp.begin();
	for(; it!= cl->neg_ilp.end(); it++)
	{
		ILPLeaf *l = (ILPLeaf*) *it;
		const map<Term*, long int> & elems = l->get_elems();
		map<Term*, long int>::const_iterator eit = elems.begin();
		for(; eit!= elems.end(); eit++)
		{
			Term* t = eit->first;
			assert(t->get_term_type() == VARIABLE_TERM);
			VariableTerm* vt = (VariableTerm*) t;
			int var_id= vt->get_var_id();
			ilp_vars.insert(var_id);
		}
	}


	/*
	 * Anything occurring inside a mod leaf is also an ilp var.
	 */
	set<ModLeaf*>::iterator it3 = cl->pos_mod.begin();
	int counter = 0;
	for(; it3 != cl->pos_mod.end(); it3++, counter++)
	{
		ModLeaf* ml = *it3;
		add_ilp_vars_in_mod_leaf(ml, true, counter);
	}
	counter = 0;
	it3 = cl->neg_mod.begin();
	for(; it3 != cl->neg_mod.end(); it3++, counter++)
	{
		ModLeaf* ml = *it3;
		add_ilp_vars_in_mod_leaf(ml, false, counter);
	}
	/*
	 * Now add everything in the congruence closure of an ILP variable.
	 */
	map<Term*, set<Term*> >::iterator it2 = eq_members.begin();
	for(; it2!= eq_members.end(); it2++)
	{
		set<Term*> & terms = it2->second;
		bool has_ilp_var = false;
		set<Term*> vars_in_eq;
		set<Term*>::iterator s_it = terms.begin();
		for(; s_it != terms.end(); s_it++)
		{
			Term* cur = *s_it;
			if(cur->get_term_type() != VARIABLE_TERM)
				continue;
			VariableTerm* vt = (VariableTerm*)cur;
			vars_in_eq.insert(vt);
			if(ilp_vars.count(vt->get_var_id()) == 0)
				continue;
			has_ilp_var = true;
		}
		if(!has_ilp_var) continue;
		set<Term*>::iterator vars_it = vars_in_eq.begin();
		for(; vars_it != vars_in_eq.end(); vars_it++){
			int var_id= ((VariableTerm*)*vars_it)->get_var_id();
			ilp_vars.insert(var_id);

		}
	}
}

void ClauseSolve::add_ilp_vars_in_mod_leaf(ModLeaf* ml, bool pos, int counter)
{
	Term* lhs = ml->get_term();
	if(lhs->get_term_type() ==  VARIABLE_TERM)
	{
		VariableTerm* lhs_vt = (VariableTerm*) lhs;
		int var_id= lhs_vt->get_var_id();
		ilp_vars.insert(var_id);
	}
	else if(lhs->get_term_type() == ARITHMETIC_TERM) {
		ArithmeticTerm* at = (ArithmeticTerm*) lhs;
		map<Term*, long int>::const_iterator it = at->get_elems().begin();
		for(; it != at->get_elems().end(); it++) {
			Term* t = it->first;
			assert(t->get_term_type() == VARIABLE_TERM);
			VariableTerm* vt = (VariableTerm*) t;
			int var_id= vt->get_var_id();
			ilp_vars.insert(var_id);
		}
	}
	else assert(false);


	//Now, add temporary
	if(pos){
		VariableTerm* vt = (VariableTerm*)
				VariableTerm::make(MOD_PREFIX+int_to_string(counter));
		int var_id = vt->get_var_id();
		ilp_vars.insert(var_id);
	}
	else
	{
		string prefix = MOD_PREFIX+int_to_string(counter);
		VariableTerm* vt1 = (VariableTerm*)
			VariableTerm::make(prefix+"_a");
		int var_id1 = vt1->get_var_id();
		ilp_vars.insert(var_id1);

		VariableTerm* vt2 = (VariableTerm*)
					VariableTerm::make(prefix+"_b");

		int var_id2 = vt2->get_var_id();
		ilp_vars.insert(var_id2);
	}
}

void ClauseSolve::clear_ilp_representatives(set<ILPLeaf*> & leaves)
{
	set<ILPLeaf*>::iterator it = leaves.begin();
	for(; it != leaves.end(); it++)
	{
		ILPLeaf *l = *it;
		const map<Term*,long int> & elems = l->get_elems();
		map<Term*,long int >::const_iterator it3 = elems.begin();
		for(; it3!=elems.end(); it3++)
		{
			Term* t = it3->first;
			t->representative = NULL;
		}
	}
}

void ClauseSolve::clear_mod_representatives(set<ModLeaf*> & leaves)
{
	set<ModLeaf*>::iterator it = leaves.begin();
	for(; it != leaves.end(); it++)
	{
		ModLeaf *l = *it;
		l->get_term()->clear_representatives();
	}
}

/*
 * Populates one row of the ILP matrix.
 */
void ClauseSolve::populate_matrix_row(ILPLeaf* ilp, bool sign)
{

	Equation* eq = new Equation(m->num_vars());
	const map<Term*, long int >& elems = ilp->get_elems();
	map<Term*, long int>::const_iterator it = elems.begin();

	for(; it!= elems.end(); it++)
	{
		Term* t = it->first;
		assert(t->get_term_type() == VARIABLE_TERM);
		int var_id = ((VariableTerm*)t)->get_var_id();
		int coef = sign? it->second : -it->second;
		int col_num = var_to_col_map[var_id];
		eq->set(col_num, coef);
	}

	bignum constant = sign? ilp->get_constant(): -ilp->get_constant();
	m->insert(eq, constant);
}

inline void ClauseSolve::add_ilp_to_matrix(ILPLeaf* ilp)
{
	populate_matrix_row(ilp, true);
	if(ilp->get_operator()==ILP_EQ){
		populate_matrix_row(ilp, false);
	}
}

/*
 * a%c = 0 is translated as a=t*c where t is some fresh temporary
 * a%c!=0 is translated as a = c*t+t2 & 0<t2<c
 */
void ClauseSolve::convert_mod(ModLeaf* ml, bool pos, int counter)
{
	set<ILPLeaf*> ilps;
	ml->to_ilp(ilps, pos, counter);
	set<ILPLeaf*>::iterator it = ilps.begin();
	for(; it!= ilps.end(); it++)
	{
		add_ilp_to_matrix(*it);
	}


}

/*
 * Constructs the initial ilp matrix.
 */
void ClauseSolve::construct_ilp_matrix()
{
	m = new Matrix(vars);
	set<ILPLeaf*>::iterator it = cl->pos_ilp.begin();
	for(; it!=cl->pos_ilp.end(); it++)
	{
		ILPLeaf* ilp = *it;
		populate_matrix_row(ilp, true);
		if(ilp->get_operator() == ILP_EQ){
			populate_matrix_row(ilp, false);
		}
	}

	it = cl->neg_ilp.begin();
	for(; it!=cl->neg_ilp.end(); it++)
	{
		ILPLeaf* ilp = *it;
		if(ilp->get_operator() == ILP_EQ){
			add_inequality(ilp);
		}
	}

	set<ModLeaf*>::iterator it2 = cl->pos_mod.begin();
	int counter = 0;
	for(; it2!=cl->pos_mod.end(); it2++, counter++)
	{
		convert_mod(*it2, true, counter);
	}
	counter = 0;
	for(it2=cl->neg_mod.begin(); it2!=cl->neg_mod.end(); it2++, counter++)
	{
		convert_mod(*it2, false, counter);
	}

}


/*
 * Adds an inferred inequality to the neq_matrix.
 */
bool ClauseSolve::add_inequality(set<pair<Term*, Term*> > disjunctive_ineq,
		set< pair<Equation*, bignum> > & new_inequality)
{
	bool added = false;
	set<pair<Term*, Term*> >::iterator it = disjunctive_ineq.begin();
	for(; it!= disjunctive_ineq.end(); it++)
	{
		Term* t1 = it->first;
		Term* t2 = it->second;
		assert(t1->get_term_type()!=FUNCTION_TERM &&
				t2->get_term_type() != FUNCTION_TERM);
		if(t1->get_term_type() == CONSTANT_TERM &&
				t2->get_term_type() == CONSTANT_TERM) continue;
		added = true;

		if(t2->get_term_type() == CONSTANT_TERM) {
			Term* temp = t2;
			t2 = t1;
			t1 = temp;
		}

		if(t1->get_term_type() == CONSTANT_TERM){
			bignum constant = ((ConstantTerm*)t1)->get_constant();
			if(ASSERT_ENABLED) {
				assert(var_to_col_map.count(((VariableTerm*)t2)->get_var_id()) > 0);
			}
			int col = var_to_col_map[((VariableTerm*)t2)->get_var_id()];
			Equation* eq = new Equation(var_to_col_map.size());
			eq->set(col, 1);
			new_inequality.insert(pair<Equation*, bignum>(eq, constant));



		}
		else {
			if(ASSERT_ENABLED) {
				assert(t1->get_term_type() == VARIABLE_TERM);
				assert(t2->get_term_type() == VARIABLE_TERM);
				assert(ilp_vars.count(((VariableTerm*)t1)->get_var_id()) > 0);
				assert(ilp_vars.count(((VariableTerm*)t2)->get_var_id()) > 0);
				assert(var_to_col_map.count(((VariableTerm*)t1)->get_var_id()) > 0);
				assert(var_to_col_map.count(((VariableTerm*)t2)->get_var_id()) > 0);
			}

			int col1 = var_to_col_map[((VariableTerm*)t1)->get_var_id()];
			int col2 = var_to_col_map[((VariableTerm*)t2)->get_var_id()];
			Equation* eq = new Equation(var_to_col_map.size());
			eq->set(col1, 1);
			eq->set(col2, -1);
			new_inequality.insert(pair<Equation*, bignum>(eq, 0));
		}
	}

	if(new_inequality.size() > 0)
		neq_constraints.insert(new_inequality);


	return added;
}



void ClauseSolve::add_inequality(ILPLeaf* ilp)
{

	Equation* eq = new Equation(var_to_col_map.size());
	const map<Term*, long int >& elems = ilp->get_elems();
	map<Term*, long int >::const_iterator it = elems.begin();

	for(; it!= elems.end(); it++)
	{
		Term* t = it->first;
		assert(t->get_term_type() == VARIABLE_TERM);
		int var_id = ((VariableTerm*)t)->get_var_id();
		int coef = it->second;
		int col_num = var_to_col_map[var_id];
		eq->set(col_num, coef);
	}

	bignum constant = ilp->get_constant();
	set<pair<Equation*, bignum> > cur_ineq;
	cur_ineq.insert(pair<Equation*, bignum>(eq, constant));
	neq_constraints.insert(cur_ineq);
}


/*
 * Adds an inferred equality constraint to the ILP matrix.
 */
void ClauseSolve::add_equality(Term* t1, Term* t2)
{
	assert(t1->get_term_type()!=FUNCTION_TERM &&
			t2->get_term_type() != FUNCTION_TERM);
	if(t1->get_term_type() == CONSTANT_TERM &&
			t2->get_term_type() == CONSTANT_TERM)
		return;

	if(t2->get_term_type() == CONSTANT_TERM) {
		Term* temp = t2;
		t2 = t1;
		t1 = temp;
	}


	if(t1->get_term_type() == CONSTANT_TERM){
		bignum constant = ((ConstantTerm*)t1)->get_constant();
		int col = var_to_col_map[((VariableTerm*)t2)->get_var_id()];
		Equation* eq = new Equation(m->num_vars());
		eq->set(col, 1);
		Equation* eq2 = eq->clone();
		eq2->flip_sign();
		m->insert(eq, constant);
		m->insert(eq2, -constant);
	}

	else {
		int col_1, col_2;
		col_1 = var_to_col_map[((VariableTerm*)t1)->get_var_id()];
		col_2 = var_to_col_map[((VariableTerm*)t2)->get_var_id()];
		Equation* eq = new Equation(m->num_vars());
		eq->set(col_1, 1);
		eq->set(col_2, -1);
		Equation* flip_eq = eq->clone();
		flip_eq->flip_sign();
		m->insert(eq, 0);
		m->insert(flip_eq, 0);

	}

}

string ClauseSolve::terms_to_string(set<Term*>& eq_class)
{
	string res = "{";
	set<Term*>::iterator it = eq_class.begin();
	for(; it!= eq_class.end(); it++)
	{
		res += (*it)->to_string() + " ";
	}
	res += "} ";
	return res;
}

bool ClauseSolve::have_contradictory_constants(Term* rep1, Term* rep2)
{
	if(eq_class_const.count(rep1) == 0 || eq_class_const.count(rep2) ==0)
		return false;
	return(eq_class_const[rep1] != eq_class_const[rep2]);
}


/*
 * Generates satisfying assignments if requested, i.e.
 * sat_assignments is non-null.
 */
void ClauseSolve::generate_sat_assignment(vector<bignum>* ilp_assignments)
{
	if(assignments == NULL)
		return;

	map<Term*, SatValue> initial_assignments;
	set<bignum> used_constants;
	/*
	 * First, process ILP assignments and everything in the
	 * equivalence class of an integer variable assigned
	 * a value by the ILP solver.
	 */

	map<int, int>::iterator it = var_to_col_map.begin();
	for(; it != var_to_col_map.end(); it++)
	{

		int var_id = it->first;
		int col = it->second;
		SatValue v;
		v.integer = true;
		if(ASSERT_ENABLED){
			assert(col < (int)ilp_assignments->size());
		}
		v.value = (*ilp_assignments)[col];
		used_constants.insert(v.value);
		Term* vt = VariableTerm::make(var_id);
		Term* rep = find_representative(vt);
		if(rep == NULL) {
			(initial_assignments)[vt] = v;
			continue;
		}
		set<Term*>::iterator members = eq_members[rep].begin();
		for(; members!=eq_members[rep].end(); members++){
			Term* member = *members;
			member = member->substitute(denestings);
			if(top_level_terms.count(member) == 0) continue;
			(initial_assignments)[member] = v;
		}

	}



	/*
	 * Now, process EQ assignments, respecting ILP choices.
	 */
	map<Term*, int>::iterator const_it = eq_class_const.begin();
	for(; const_it != eq_class_const.end(); const_it++) {
		used_constants.insert(const_it->second);
	}

	map<Term*, set<Term*> >::iterator it2 = eq_members.begin();
	for(; it2 != eq_members.end(); it2++)
	{
		//Check if this class has a constant assigned
		long int c;
		if(eq_class_const.count(it2->first) > 0)
		{
			c = eq_class_const[it2->first];
			SatValue v;
			v.integer = true;
			v.value = c;
			set<Term*>::iterator members_it = it2->second.begin();
			for(; members_it!= it2->second.end();  members_it++){
				Term* member = *members_it;
				member = member->substitute(denestings);
				if(top_level_terms.count(member) == 0) continue;
				(initial_assignments)[member] = v;
			}
			continue;
		}

		SatValue v;
		v.integer = true;
		bignum val = 0;
		while(true){
			if(used_constants.count(val) == 0) {
				used_constants.insert(val);
				break;
			}
			val+=1;
		}
		v.value = val;

		bool used_assignment = false;


		set<Term*>::iterator members_it = it2->second.begin();
		for(; members_it!=it2->second.end(); members_it++)
		{
			Term* member = *members_it;
			member = member->substitute(denestings);
			if(member->get_term_type()==CONSTANT_TERM)
				break;
			if(top_level_terms.count(member) == 0) continue;
			if(initial_assignments.count(member) >0 )
				break;

			used_assignment = true;
			(initial_assignments)[member] = v;
		}
		if(!used_assignment){
			used_constants.erase(val);
		}
	}


	{
		map<Term*, SatValue> temp = initial_assignments;
		map<Term*, SatValue>::iterator it = initial_assignments.begin();
		for(; it!= initial_assignments.end(); it++)
		{
			Term* t = it->first;
			temp.erase(t);
			Term* new_t = t->evalute_term(temp);
			temp[t] = it->second;
			(*assignments)[new_t] = it->second;
		}
	}


}



void ClauseSolve::get_ilp_assignment(vector<bignum>& ilp_assign)
{
	map<int, int>::iterator it = var_to_col_map.begin();
	for(; it!= var_to_col_map.end(); it++)
	{
		int var_id = it->first;
		int index = it->second;
		Term* t = VariableTerm::make(var_id);
		ilp_assignments[t] = ilp_assign[index];
	}
}

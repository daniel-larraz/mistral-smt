/*
 * MSAFinder.cpp
 *
 *  Created on: Aug 22, 2011
 *      Author: isil
 */

#include "MSAFinder.h"
#include "cnode.h"
#include "Solver.h"
#include "ExistentialEliminator.h"
#include "term.h"
#include "MinPrimeImplicant.h"


#define DEBUG false

#define USE_MIN_PRIME_IMPLICANTS true
#define PROPAGATE_DEPENDENCIES true

#define MAX_COST ((~0)&(~(1<<31)))

MSAFinder::MSAFinder(CNode* node, map<VariableTerm*, int>& costs):
	costs(costs)
{
	set<CNode*> bg;
	find_msa(node, bg , costs);
}

MSAFinder::MSAFinder(CNode* node, set<CNode*>& background,
		map<VariableTerm*, int>& costs):
	costs(costs)
{


	find_msa(node, background, costs);

}

void MSAFinder::find_msa(CNode* node, set<CNode*>& background,
		map<VariableTerm*, int>& costs)
{
	num_e_elims = 0;
	e_elim_time = 0;
	num_a_elims = 0;
	a_elim_time = 0;
	a_approximate = 0;
	a_approximate_time = 0;
	num_unsat_universal = 0;
	num_unsat_approx_universal = 0;
	num_dep_success = 0;
	simplify_time = 0;
	mpi_time = 0;
	prune1_solve = 0;
	prune2_solve= 0;

	e_only = 0;
	a_only = 0;
	total = 0;
	cost_pruned = 0;


	if(DEBUG) {
		cout << "FINDING MSA for: " << node->to_string() << endl;
	}

	int start_simp = clock();
	Solver s(node, THEORY_SIMPLIFY);
	node = s.get_result();
	simplify_time = clock() - start_simp;
	if(node->get_type() == FALSE_NODE) {
		min_estimate = MAX_COST;
		return;
	}
	if(node->get_type() == TRUE_NODE) {
		min_estimate = 0;
		return;
	}
	this->node = node;




	int start_d = clock();
	compute_dependencies(node);
	dependence_time = clock() - start_d;

	if(DEBUG) print_dependencies();


	this->fun_counter = 0;

	compute_initial_bound(background);
	set<VariableTerm*> mpi_est_msa = msa;
	msa.clear();


	if(DEBUG) {
		cout << "initial cost: " << min_estimate << endl;
	}


	set<Term*> vars;
	node->get_vars(vars);

	init_var_to_fun_map(vars);


	set<Term*> universals;

	compute_msa(node, background, 0, msa, universals);
	if(msa.size() ==0 && min_estimate == mpi_estimate) {
		msa = mpi_est_msa;
	}

}



/*
 * Initialize var_to_fun_map containing a unique function term for each
 * variable
 */
void MSAFinder::init_var_to_fun_map(set<Term*> vars)
{
	set<Term*>::iterator it = vars.begin();
	for(; it!= vars.end(); it++)
	{
		Term* cur = *it;
		assert(cur->get_term_type() == VARIABLE_TERM);
		VariableTerm* vt = static_cast<VariableTerm*>(cur);
		string function_name = "f" + int_to_string(fun_counter++);
		vector<Term*> args;
		args.push_back(ConstantTerm::make(0));
		var_to_fun_map[vt] = FunctionTerm::make(function_name, args, false);
	}
}

int MSAFinder::get_cost()
{
	return min_estimate;
}

string MSAFinder::res_to_string()
{
	string res = "{";
	set<VariableTerm*>::iterator it = msa.begin();
	for(int i=0; it != msa.end(); it++, i++)
	{
		VariableTerm* vt = *it;
		res += vt->to_string();
		if(i!= msa.size()-1)  res+=", ";

	}
	res += "}";
	return res;
}


bool MSAFinder::is_subset_of(const set<Term*>& s1, const set<Term*>& s2)
{
	set<Term*>::const_iterator it = s1.begin();
	for(; it!= s1.end(); it++)
	{
		Term* t = *it;
		if(s2.count(t) == 0) return false;
	}

	return true;
}

bool MSAFinder::is_subset_of(const set<VariableTerm*>& s1,
		const set<VariableTerm*>& s2)
{
	set<VariableTerm*>::const_iterator it = s1.begin();
	for(; it!= s1.end(); it++)
	{
		VariableTerm* t = *it;
		if(s2.count(t) == 0) return false;
	}

	return true;
}
void MSAFinder::compute_dependencies(CNode* c)
{
	compute_dependencies_rec(True::make(), c);

	for(map<Term*, set<set<Term*> > >::iterator it= dependencies.begin();
			it!= dependencies.end(); it++)
	{
		set<set<Term*> > & old = it->second;
		set<set<Term*> > removed_sets;

		for(set<set<Term*> >::iterator it2 = old.begin(); it2 != old.end(); it2++)
		{
			const set<Term*>& s1 = *it2;
			set<set<Term*> >::iterator it3 = old.begin();
			for(; it3!= old.end(); it3++)
			{
				if(it3 == it2) continue;
				const set<Term*>& s2 = *it3;
				if(is_subset_of(s2, s1)) removed_sets.insert(s1);

			}
		}

		for(set<set<Term*> >::iterator it  = removed_sets.begin();
				it!= removed_sets.end(); it++)
		{
			old.erase(*it);
		}


	}
}

void MSAFinder::compute_dependencies_rec(CNode* context, CNode* c)
{
	//if(c->is_literal()) return;
	if(c->is_literal())
	{
		set<Term*> cur_vars;
		c->get_vars(cur_vars);

		set<Term*> context_vars;
		context->get_vars(context_vars);

		for(set<Term*>::iterator it2 = cur_vars.begin();
				it2 != cur_vars.end(); it2++)
		{
			Term* t = *it2;
			if(context_vars.count(t) >0) continue;
			set<Term*> depends_on;
			depends_on.insert(context_vars.begin(), context_vars.end());
			depends_on.insert(cur_vars.begin(), cur_vars.end());
			depends_on.erase(t);
			dependencies[t].insert(depends_on);


		}

		return;
	}

	if(c->get_type() == AND)
	{
		Connective* and_c = static_cast<Connective*>(c);
		const set<CNode*>& ops = and_c->get_operands();
		for(set<CNode*>::const_iterator it = ops.begin(); it != ops.end(); it++)
		{
			CNode* op = *it;
			compute_dependencies_rec(context, op);
		}

		return;
	}

	assert(c->get_type() == OR);
	Connective* or_c = static_cast<Connective*>(c);
	const set<CNode*>& ops = or_c->get_operands();

	set<CNode*> ops_copy = ops;
	for(set<CNode*>::const_iterator it = ops.begin(); it!= ops.end(); it++)
	{
		CNode* cur = *it;
		ops_copy.erase(cur);

		CNode* siblings = Connective::make_or(ops_copy);
		CNode* neg_siblings = Connective::make_not(siblings);
		CNode* critical = Connective::make(AND, neg_siblings, context);


		ops_copy.insert(cur);

		compute_dependencies_rec(critical,cur);



	}



}


VariableTerm* MSAFinder::pick_next_unassigned_var(
		CNode* c, deque<VariableTerm*>& unassigned_vars)
{


	VariableTerm* vt =  *unassigned_vars.begin();
	return vt;
}

CNode* MSAFinder::propagate_dependencies(CNode* c, set<VariableTerm*>& cur_msa,
		const set<Term*>& cur_universals, int & cur_cost)
{
	deque<VariableTerm*> unassigned_vars;
	get_unassigned_vars(c, unassigned_vars);

	for(deque<VariableTerm*>::iterator it = unassigned_vars.begin();
			it!= unassigned_vars.end(); it++)
	{
		VariableTerm* x = *it;
		const set<set<Term*> >& cur_dependencies = dependencies[x];
		for(set<set<Term*> >::const_iterator it2 = cur_dependencies.begin();
				it2 != cur_dependencies.end(); it2++)
		{
			const set<Term*> & cur = *it2;
			/*
			 * This means x must be in MSA!
			 */
			if(is_subset_of(cur, cur_universals))
			{
				//cout << "**************** DEPENDENCY ALLOWS ELIM OF "
					//	<< x->to_string() << endl;
				num_dep_success++;
				c= existentially_quantify(c, x);
				cur_msa.insert(x);
				cur_cost+=get_cost(x);
			}
		}

	}
	return c;
}

int MSAFinder::compute_msa(CNode* constraint, set<CNode*>& background,
		int cur_cost, set<VariableTerm*>& cur_msa,
		set<Term*>& cur_universal)
{
	if(DEBUG) {
		cout << "-------------------- BEGIN CALL -------------" << endl;
		cout << "*** cur constraint: " << constraint->to_string() << endl;
		cout << "*** cur cost is: " << cur_cost << endl;
	}





	total++;

	/*
	 * prune search
	 */
	if(cur_cost >= min_estimate) {
		cost_pruned++;
		if(DEBUG) {
			cout << "-------------------- END 1 CALL -------------" << endl;
		}
		return MAX_COST;
	}

	/*
	 * If current formula is UNSAT, current assignment is not satisfying.
	 */
	int start = clock();
	Solver s(constraint, UNSAT_SIMPLIFY);
	constraint = s.get_result();
	prune1_solve += clock()-start;
	if(constraint->get_type() == FALSE_NODE) {
		if(DEBUG) {
			cout << "-------------------- END 2 CALL -------------" << endl;
		}
		return MAX_COST;
	}

	/*
	 * Furthermore, if current formula together with background is unsat,
	 * there is no satisfying assignment using the current set of variables
	 * that is consistent with the background.
	 */
	set<CNode*>::iterator it = background.begin();
	for(; it!= background.end(); it++)
	{
		CNode* cur = *it;
		CNode* to_check = Connective::make(AND, constraint, cur);
		int start = clock();
		Solver s2(to_check, UNSAT_SIMPLIFY);
		prune2_solve += clock()-start;
		if(s2.get_result()->get_type() == FALSE_NODE)
		{
			if(DEBUG) {
				cout << "-------------------- END 3 CALL -------------" << endl;
			}
			return MAX_COST;
		}
	}

	if(PROPAGATE_DEPENDENCIES) {
		constraint =
				propagate_dependencies(constraint, cur_msa, cur_universal,
						cur_cost);
	}


	if(cur_cost >= min_estimate) {
		cost_pruned++;
		if(DEBUG) {
			cout << "-------------------- END 4 CALL -------------" << endl;
		}
		return MAX_COST;
	}






	deque<VariableTerm*> unassigned_vars;
	get_unassigned_vars(constraint, unassigned_vars);

	/*
	 * If current formula is satisfiable and there are no variables left,
	 * then we found a better partial satisfying assignment
	 */
	if(unassigned_vars.size() == 0) {
		min_estimate = cur_cost;
		if(DEBUG) {
			cout << "-------------------- END 5 CALL -------------" << endl;
		}
		return cur_cost;
	}




	/*
	 * Pick next variable to consider
	 */
	VariableTerm* x = pick_next_unassigned_var(constraint, unassigned_vars);
	int x_cost = get_cost(x);

	bool exist_only = false;
	bool forall_only = false;

	int x_in_cost = MAX_COST;
	set<VariableTerm*> x_in_msa;

	int x_out_cost = MAX_COST;
	set<VariableTerm*> x_out_msa;


	if(DEBUG) {
		cout << "Considering next variable: " << x->to_string() << endl;
		cout << "Cost of current variable: " <<  x_cost << endl;
	}



	/*
	 * If (Ax. constraint) is UNSAT, we know x is part of MSA
	 */
	CNode* forall_x = universally_quantify(constraint, x);
	if(forall_x->get_type() == FALSE_NODE) {
		exist_only = true;
		e_only++;
	}

	/*
	 * If cost of current variable is greater than sum of all unassigned vars,
	 * we know x should not be part of MSA
	 */
	int max_remaining_cost = get_max_remaining_cost(unassigned_vars);
	if(!exist_only && x_cost > max_remaining_cost) {
		forall_only = true;
		a_only++;
	}



	/*
	 *Compute MSA for (Ax. phi)
	 */
	if(!exist_only)
	{

		if(DEBUG) {
			cout << "CONSIDERING OUT: " << x->to_string() << endl;
			cout << "FORALL X: " << forall_x->to_string() << endl;
		}

		cur_universal.insert(x);
		x_out_cost = compute_msa(forall_x, background, cur_cost,
				x_out_msa, cur_universal);

		if(DEBUG) {
			cout << "COST OF " << x->to_string() << " OUT OF MSA: "<< x_out_cost << endl;
		}
		cur_universal.erase(x);

	}


	/*
	 * Compute MSA for (Ex. phi & x=f_x(0))
	 */
	if(!forall_only)
	{

		CNode* exist_x = existentially_quantify(constraint, x);
		if(DEBUG) {
			cout << "EXIST X: " << exist_x->to_string() << endl;
		}
		set<CNode*> new_bg;
		set<CNode*>::iterator it = background.begin();
		for(; it!= background.end(); it++)
		{
			CNode* cur = *it;
			CNode* new_cur = existentially_quantify(cur, x);
			new_bg.insert(new_cur);
		}

		x_in_cost = compute_msa(exist_x, new_bg, (cur_cost + x_cost),
				x_in_msa, cur_universal);

		if(DEBUG) {
			cout << "COST OF " << x->to_string() << " IN MSA: "<< x_in_cost << endl;
		}


		//if(x_in_cost != MAX_COST)  //we don't want to overflow!
		//	x_in_cost += x_cost;
		x_in_msa.insert(x);




	}


	/*
	 * x is part of MSA
	 */
	if(x_in_cost <= x_out_cost)
	{

		cur_msa.insert(x_in_msa.begin(), x_in_msa.end());

		if(DEBUG) {
			cout << "IN MSA: " << x->to_string() << " COST: " << x_in_cost
					<< endl;
			cout << "-------------------- END 6 CALL -------------" << endl;

		}

		return x_in_cost;

	}

	/*
	 * x is not part of msa
	 */
	else {

		cur_msa.insert(x_out_msa.begin(), x_out_msa.end());

		if(DEBUG) {
			cout << "NOT IN MSA: " << x->to_string() << endl;
			cout << "-------------------- END 7 CALL -------------" << endl;
		}
		return x_out_cost;
	}


}




/*
 * Gives the currently unassigned variables in constraint
 */
void MSAFinder::get_unassigned_vars(CNode* constraint,
		deque<VariableTerm*>& unassigned_vars)
{
	set<Term*> vars;
	constraint->get_vars(vars);

	set<Term*>::iterator it = vars.begin();
	for(; it!= vars.end(); it++) {
		VariableTerm* vt = static_cast<VariableTerm*>(*it);
		if(vars_in_min_pi.count(vt) == 0)
			unassigned_vars.push_back(vt);
		else unassigned_vars.push_front(vt);
	}
}


/*
 * Gives the cost of this variable
 */
int MSAFinder::get_cost(VariableTerm* vt)
{
	if(costs.count(vt) > 0) return costs[vt];
	else return 1;
}

/*
 * Sums up costs of all remaining vars
 */
int MSAFinder::get_max_remaining_cost(deque<VariableTerm*>& unassigned_vars)
{
	int total = 0;
	deque<VariableTerm*>::iterator it = unassigned_vars.begin();
	for(; it!= unassigned_vars.end(); it++){
		VariableTerm* vt = *it;
		int cur = get_cost(vt);
		total += cur;
	}
	return total;
}

void MSAFinder::print_dependencies()
{

	cout << "+++++++++++++++++DEPENDENCIES++++++++++++++++" << endl;
	for(map<Term*, set<set<Term*> > >::iterator it = dependencies.begin();
			it != dependencies.end(); it++)
	{
		Term* t= it->first;
		cout << "=> " << t->to_string() << endl;
		for(set<set<Term*> >::iterator it2= it->second.begin();
				it2 != it->second.end(); it2++)
		{
			const set<Term*>& cur_set = *it2;
			cout << "\t ";
			for(set<Term*>::const_iterator it3= cur_set.begin();
					it3 != cur_set.end(); it3++)
			{
				Term* cur = *it3;
				cout << cur->to_string() << "  ";
			}
			cout << endl;
		}
	}

	cout << "+++++++++++++++++DEPENDENCIES DONE++++++++++++++++" << endl;
}


void MSAFinder::get_constants_to_check(CNode* c, vector<Term*>& constants)
{
	ConstantTerm* min = NULL;
	ConstantTerm* max = NULL;
	set<Term*> terms;
	c->get_nested_terms(terms, true, true);

	for(set<Term*>::iterator it = terms.begin(); it!= terms.end(); it++)
	{
		Term* t = *it;
		if(t->get_term_type() != CONSTANT_TERM) continue;
		ConstantTerm* ct = static_cast<ConstantTerm*>(t);
		long int c = ct->get_constant();
		if(min == NULL || c < min->get_constant()) {
			min = ct;
		}
		if(max == NULL || c > max->get_constant()) {
			max = ct;
		}

	}
	if(min != NULL) {
		Term* below_min = ConstantTerm::make(min->get_constant()-1);
		constants.push_back(below_min);
	}

	if(max != NULL) {
		Term* above_max = ConstantTerm::make(max->get_constant()+1);
		constants.push_back(above_max);
	}
	//constants.push_back(ConstantTerm::make(7));
	//constants.push_back(ConstantTerm::make(-3));

}

bool MSAFinder::quick_test_universal_unsat(CNode* c, VariableTerm* v)
{
	a_approximate++;
	/*
	 * Before doing the expensive quantifier elimination, try some
	 * relevant constants to see if Av. c is unsat.
	 */

	int approx_start = clock();
	vector<Term*> constants;
	get_constants_to_check(c, constants);

	map<Term*, Term*> rep;
	for(vector<Term*>::iterator it = constants.begin();
			it!= constants.end(); it++)
	{
		Term* ct = *it;
		rep[v] = ct;
		CNode* cur_inst = c->substitute(rep);
		Solver s(cur_inst, UNSAT_SIMPLIFY);
		if(s.get_result()->get_type() == FALSE_NODE) {
			a_approximate_time += (clock() - approx_start);
			num_unsat_approx_universal++;
			return true;
		}
	}
	a_approximate_time += (clock() - approx_start);
	return false;
}

/*
 * Result of universally quantifying v in c and performing
 * quantifier elimination
 */
CNode* MSAFinder::universally_quantify(CNode* c, VariableTerm* v)
{

	bool unsat = quick_test_universal_unsat(c, v);
	if(unsat) return False::make();


	num_a_elims++;
	CNode* neg_c = Connective::make_not(c);
	int start = clock();
	ExistentialEliminator elim(neg_c, v, true);
	CNode* res = elim.get_result();
	res = Connective::make_not(res);
	if(res->get_type() == FALSE_NODE) {
		num_unsat_universal++;
	}
	int stop = clock();
	a_elim_time += (stop - start);

	return res;
}

/*
 * Result of existentially quantifying v in c and performing
 * quantifier elimination
 */
CNode* MSAFinder::existentially_quantify(CNode* c, VariableTerm* v)
{

	num_e_elims++;
	assert(var_to_fun_map.count(v) > 0);
	Term* ft = var_to_fun_map[v];
	CNode* v_eq_ft = EqLeaf::make(v, ft);
	set<CNode*> args;
	args.insert(c);
	args.insert(v_eq_ft);
	CNode* new_c = Connective::make_and(args);

	int start = clock();
	ExistentialEliminator elim(new_c, v, false);
	CNode* result = elim.get_result();
	e_elim_time += (clock() - start);

	return result;
}


/*
 * Finds the cost of variable with cheapest cost
 */
int MSAFinder::get_cheapest_cost(const vector<VariableTerm*>& vars)
{
	int min_cost = MAX_COST;
	vector<VariableTerm*>::const_iterator it = vars.begin();
	for(; it!= vars.end(); it++)
	{
		VariableTerm* vt = *it;
		int cur_cost = get_cost(vt);
		if(cur_cost < min_cost) {
			min_cost = cur_cost;
		}
	}
	return min_cost;
}

const set<VariableTerm*>& MSAFinder::get_vars_in_msa()
{
	return msa;
}

void MSAFinder::compute_initial_bound(set<CNode*>& background)
{

	max_cost = 1;
	set<Term*> vars;
	node->get_vars(vars);


	for(set<Term*>::iterator it = vars.begin(); it!= vars.end(); it++) {
		int cost = get_cost(static_cast<VariableTerm*>(*it));
		if(DEBUG) cout << "COST OF: " << (*it)->to_string() << ": " << cost << endl;
		max_cost += cost;
	}

	if(!USE_MIN_PRIME_IMPLICANTS)
	{
		min_estimate = max_cost;
		mpi_estimate = max_cost;
		return;
	}


	int start = clock();
	MinPrimeImplicant mpi(node, background, costs);


	mpi_estimate = mpi.get_cost();
	if(mpi_estimate < max_cost) {
		min_estimate = mpi.get_cost();
	}
	else {
		min_estimate = max_cost;
	}

	mpi_time += clock() - start;


	map<Term*, SatValue>::const_iterator it = mpi.get_min_assignment().begin();
	for(; it != mpi.get_min_assignment().end(); it++) {
		Term* t = it->first;
		if(t->get_term_type() != VARIABLE_TERM) continue;
		vars_in_min_pi.insert(t);
		msa.insert(static_cast<VariableTerm*>(t));

	}


}

string MSAFinder::get_stats()
{
	string res = "Simplification time (s): " +
				float_to_string(((double)simplify_time)/((double)CLOCKS_PER_SEC)) + "\n";

	res += "MPI time (s): " +
					float_to_string(((double)mpi_time)/((double)CLOCKS_PER_SEC)) + "\n";

	res += "Num existential eliminations: " + int_to_string(num_e_elims)
			+ "\n";
	res += "Existential time (s): " +
			float_to_string(((double)e_elim_time)/((double)CLOCKS_PER_SEC)) + "\n";
	res += "Num universal eliminations: " + int_to_string(num_a_elims) + "\n";
	res += "Universal time (s): " +
				float_to_string(((double)a_elim_time)/((double)CLOCKS_PER_SEC));

	res += "\nNum approximate universal eliminations: " + int_to_string(a_approximate) + "\n";
	res += "Approximate universal time (s): " +
			float_to_string(((double)a_approximate_time)/((double)CLOCKS_PER_SEC));

	res += "\n";

	res += "Prune 1 solve time (s): " +
				float_to_string(((double)prune1_solve)/((double)CLOCKS_PER_SEC)) + "\n";
	res += "Prune 2 solve time (s): " +
					float_to_string(((double)prune2_solve)/((double)CLOCKS_PER_SEC)) + "\n";

	double percent_approx_useful =
			((double)num_unsat_approx_universal)/(
					(double)(num_unsat_approx_universal + num_unsat_universal));
	res += "Percentage of successful approximate universal checks: " +
			float_to_string(percent_approx_useful*100.0) + "\n";
	res += "Num dependence successful: " + int_to_string(num_dep_success) + "\n";
	res += "Dependence time (s): " +
				float_to_string(((double)dependence_time)/((double)CLOCKS_PER_SEC)) +"\n";


	res += "Number of branching points " +
					int_to_string(total) + "\n";
	res += "Number of existential only points " +
						int_to_string(e_only) + "\n";
	res += "Number of universal only points " +
						int_to_string(a_only) + "\n";

	return res;



}

MSAFinder::~MSAFinder()
{

}

//------------------------------------------

void MSAFinder::compute_subsets(set<Term*> vars,
		set<set<Term*> >& subsets)
{

	if(vars.size() == 0) return;

	Term* cur = *vars.begin();
	vars.erase(cur);


	// Make recursive call
	compute_subsets(vars, subsets);


	set<set<Term*> > new_subsets;
	set<Term*> cur_alone;
	cur_alone.insert(cur);
	new_subsets.insert(cur_alone);


	set<set<Term*> >::iterator it = subsets.begin();
	for(; it!= subsets.end(); it++)
	{
		const set<Term*>& cur_subset = *it;
		set<Term*> new_subset = cur_subset;
		new_subset.insert(cur);
		new_subsets.insert(new_subset);

	}

	subsets.insert(new_subsets.begin(), new_subsets.end());


}

CNode* MSAFinder::universally_quantify(CNode* c, set<Term*> vars)
{
	CNode* cur = c;

	for(set<Term*>::iterator it = vars.begin(); it!= vars.end(); it++)
	{
		VariableTerm* t = static_cast<VariableTerm*>(*it);
		cur = universally_quantify(cur, t);

	}

	return cur;
}

int MSAFinder::get_cost(const set<Term*>& vars)
{
	int cost = 0;
	set<Term*>::const_iterator it = vars.begin();
	for(; it!= vars.end(); it++)
	{
		VariableTerm* t = static_cast<VariableTerm*>(*it);
		cost += get_cost(t);

	}
	return cost;
}


void MSAFinder::get_candidate_msa(set<Term*>& vars, const set<Term*>& quantified,
		set<Term*>& candidate_msa)
{
	for(set<Term*>::iterator it = vars.begin(); it!= vars.end(); it++)
	{
		Term* t = *it;
		if(quantified.count(t) > 0) continue;
		candidate_msa.insert(t);
	}
}

int MSAFinder::compute_msa_naive(CNode* c, set<VariableTerm*> & msa)
{
	set<Term*> vars;
	c->get_vars(vars);

	set<set<Term*> > subsets;
	compute_subsets(vars, subsets);

	cout << "++++++++++ALL SUBSETS+++++++++++++++" << endl;
	for(set<set<Term*> >::iterator it = subsets.begin(); it!= subsets.end(); it++)
	{
		const set<Term*>& cur_subset = *it;
		for(set<Term*>::const_iterator it2 =
				cur_subset.begin(); it2 != cur_subset.end(); it2++)
		{
			Term* t = *it2;
			cout << t->to_string() << " ";
		}
		cout << endl;

	}

	for(set<set<Term*> >::iterator it = subsets.begin();
			it!= subsets.end(); it++)
	{
		const set<Term*>& cur_subset = *it;
		set<Term*> candidate_msa;
		get_candidate_msa(vars, cur_subset, candidate_msa);

		int cost = get_cost(candidate_msa);
		if(cost >= min_estimate) continue;

		CNode* res = universally_quantify(c, cur_subset);

		Solver s(res, UNSAT_SIMPLIFY);
		if(s.get_result()->get_type() == FALSE_NODE) continue;
		msa.clear();
		set<Term*>::iterator it2 = candidate_msa.begin();
		for(; it2!= candidate_msa.end(); it2++) {
			msa.insert(static_cast<VariableTerm*>(*it2));
		}

		min_estimate = cost;

	}
	return min_estimate;



}


int MSAFinder::compute_msa_using_blocking_clause(CNode* c,
		set<VariableTerm*>& msa)
{
	int best_cost = min_estimate;
	//int best_cost = MAX_COST;
	//cout << "***MSA size: " << msa.size() << " best cost: " << best_cost << endl;
	//compute_msa_bc(c, False::make(), best_cost, msa );
	compute_msa_bc(c, c, best_cost, msa );
	//cout << "MSA size: " << msa.size() << " best cost: " << best_cost << endl;
	//assert(msa.size() == best_cost);
	return best_cost;
}

void MSAFinder::randomize_order(map<Term*, SatValue>& assignment,
		deque<pair<Term*, SatValue> >& new_order)
{
	while(assignment.size()>0){
		Term* t = assignment.begin()->first;
		SatValue sv = assignment.begin()->second;
		assignment.erase(t);

		//cout << "new order:" << endl;
		//cout << "size: " << new_order.size() << endl;
		int index = rand()%(new_order.size()+1);
		//cout << "index: " << index << endl;
		deque<pair<Term*, SatValue> >::iterator it = new_order.begin();
		for(int i=0; i <index; i++){
			it++;
		}
		new_order.insert(it, make_pair(t, sv));

	}
}

void MSAFinder::order_assignments(map<Term*, SatValue>& assignment,
		deque<pair<Term*, SatValue> >& new_order)
{
	for(map<Term*, SatValue>::reverse_iterator it = assignment.rbegin()
					; it!= assignment.rend(); it++)
	{
		Term* cur = it->first;
		SatValue val = it->second;
		if(vars_in_min_pi.count(cur)>0) new_order.push_front(make_pair(cur, val));
		else new_order.push_back(make_pair(cur, val));
	}
}

void MSAFinder::compute_msa_bc(CNode* c, CNode* bc, int& best_cost,
		set<VariableTerm*>& msa)
{

	assert(false);
	bool first = true;

	int i = 0;
	while(true)
	{

		i++;
		//assert(i<10);
		//cout << "c: " << c->to_string() << " bc: " << bc->to_string() <<
		//		" best cost: " << best_cost << endl;

		/*
		 * Get SAT assignment to c & !bc
		 */
		CNode* t = Connective::make(AND, bc, c);

		//cout << "Current constraint: " << t->to_string() << endl;
		map<Term*, SatValue> assignment;
		Solver s(t, UNSAT_SIMPLIFY, &assignment, false);
		if(s.get_result()->get_type() == FALSE_NODE) {
			//cout << "UNSAT " << endl;
			//cout << "------------------ END CALL -----------" << endl;
			break;
		}
		//cout << "Constraint: " << t->to_string() << endl;
		//cout << "Size of assignment: " << assignment.size() << endl;

		map<Term*, SatValue> minimal_assignment = assignment;
		set<VariableTerm*> v_bar;
		set<VariableTerm*> vars_in_msa;
		int cur_cost = 0;
		//cout << "** starting minimal assign " << endl;

		//map<Term*, SatValue> temp = assignment;

		//deque<pair<Term*, SatValue> > randomized_assignment;
		//randomize_order(temp, randomized_assignment);
		/*
		cout << "RAND ASSIGN" << endl;
		for(deque<pair<Term*, SatValue> >::iterator it =
				randomized_assignment.begin();it != randomized_assignment.end();
				it++)
		{
			cout << it->first->to_string() << endl;
		}
		cout << "*********" << endl;
	*/
		//deque<pair<Term*, SatValue> >::iterator it =
		//				randomized_assignment.begin();

		deque<pair<Term*, SatValue> > ordered_assignment;
		order_assignments(assignment, ordered_assignment);

		for(deque< pair<Term*, SatValue> >::iterator it = ordered_assignment.begin()
						; it!= ordered_assignment.end(); it++)
		{
			Term* cur = it->first;

			if(cur->get_term_type() != VARIABLE_TERM) {
				continue;
			}
			VariableTerm* cur_vt = static_cast<VariableTerm*>(cur);


			minimal_assignment.erase(cur);

			if(cur_cost >= best_cost) continue;

			bool must_be_in_msa = false;
			//if(bc_conjunct_redundant(v_bar, cur_vt))
			//	must_be_in_msa = true;

			if(!must_be_in_msa)
			{
				CNode* res = c->evaluate_assignment(minimal_assignment);
				CNode* neg_res = Connective::make_not(res);
				Solver s(neg_res, UNSAT_SIMPLIFY);
				must_be_in_msa = s.get_result()->get_type() != FALSE_NODE;
			}


			if(must_be_in_msa) {
				//cout << "IN min: " << cur_vt->to_string() << endl;
				minimal_assignment[cur] = it->second;
				cur_cost+=get_cost(cur_vt);
				vars_in_msa.insert(cur_vt);
			}
			else {
			//	cout << "OUT min: " << cur_vt->to_string() << endl;
				v_bar.insert(cur_vt);

			}
		}



	   // cout << "** end minimal assign " << endl;

		/*if(msa != vars_in_msa && !first && is_subset_of(msa, vars_in_msa))
		{

			cout << "MSA *******" << endl;
			set<VariableTerm*>::iterator it = msa.begin();
			for(; it != msa.end(); it++) {
				cout << "  -> " << (*it)->to_string() << endl;
			}
			cout << "VARS IN MSA ***********" << endl;
			it = vars_in_msa.begin();
			for(; it != vars_in_msa.end(); it++) {
				cout << "  -> " << (*it)->to_string() << endl;
			}
			cout << "***********" << endl;
			assert(false);
		}*/

		if(cur_cost < best_cost) {
			best_cost = cur_cost;
			msa = vars_in_msa;

		}







		/*
		CNode* new_bc = False::make();
		//cout << "*************** BEGIN " << endl;
		if(rand()%10==0)
		{
			for(set<VariableTerm*>::iterator it = vars_in_msa.begin();
					it != vars_in_msa.end(); it++)
			{
				VariableTerm* v = *it;
				//cout << "--> VT: " << v->to_string() << endl;
				CNode* not_new_bc = Connective::make_not(c);
				//cout << "not new bc: " << not_new_bc->to_string() << endl;
				//cout << "eliminating: " << v->to_string() << endl;
				VariableEliminator elim(not_new_bc, v, THEORY_SIMPLIFY, true);
				CNode* res = elim.get_result();
				res = Connective::make_not(res);
				//cout << "res: " << res->to_string() << endl;
				new_bc = Connective::make(OR, res, new_bc);


			}
		}
		//cout << "*************** END " << endl;

	*/

	//	cout << "******new bc: " << new_bc->to_string() << endl;



		CNode* new_bc2 = c;
		for(set<VariableTerm*>::iterator it = v_bar.begin(); it != v_bar.end(); it++)
		{
			VariableTerm* v = *it;
			CNode* not_new_bc = Connective::make_not(new_bc2);
			ExistentialEliminator elim(not_new_bc, v,  true);
			CNode* res = elim.get_result();
			new_bc2 = Connective::make_not(res);

		}

		/*


		for(map<Term*, SatValue>::iterator it = minimal_assignment.begin();
				it!= minimal_assignment.end(); it++)
		{
			Term* t = it->first;
			if(t->get_term_type() != VARIABLE_TERM) continue;
			VariableTerm* vt =static_cast<VariableTerm*>(t);

			if(false && bc_conjunct_redundant(v_bar, vt)) {
				//cerr << "******************** GOT HERE ********* " << endl;
				continue;
			}

			vector<Term*> elim_set;

			for(set<VariableTerm*>::iterator it = v_bar.begin(); it != v_bar.end(); it++ )
			{
				elim_set.push_back(*it);
			}
			elim_set.push_back(vt);

			CNode* neg_c = Connective::make_not(c);
			ExistentialEliminator elim(neg_c, elim_set, true);
			new_bc2 = Connective::make(AND, new_bc2, elim.get_result());
		}
		new_bc2 = Connective::make_not(new_bc2);

*/



		bc  = Connective::make(AND, bc, new_bc2);
		//if(new_bc->get_type() != FALSE_NODE)
		//	bc = Connective::make(AND, bc, new_bc);

		//bc = new_bc;
		first = false;
		//cout << "cur Iterations: " << i << endl;

	}
	cout << "Iterations: " << i << endl;

}

bool MSAFinder::bc_conjunct_redundant(set<VariableTerm*>& _v_bar,
		VariableTerm* vt)
{

	if(dependencies.count(vt) == 0) return false;

	set<Term*>& v_bar = (set<Term*>&)_v_bar;

	set<set<Term*> >& vt_dependencies = dependencies[vt];
	for(set<set<Term*> >::iterator it = vt_dependencies.begin();
			it!= vt_dependencies.end(); it++)
	{
		const set<Term*>& deps = *it;
		if(is_subset_of(deps, v_bar)) return true;
	}
	return false;
}



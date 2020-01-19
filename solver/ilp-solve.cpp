/*
 * ilp-solve.cpp
 *
 *  Created on: Jan 15, 2009
 *      Author: tdillig
 */

#include "ilp-solve.h"
#include "simplex.h"
#include "matrix.h"
#include "slack_matrix.h"
#include "bigfraction.h"
#include "util.h"
#include "hermite.h"
#include "mistral.h"

#define ASSERT_ENABLED false
#define DEBUG false
#define ENABLE_TIMING false
#define VERIFY_SOLUTION false

#define ALPHA_FACTOR 10

bool ilp_sat_internal(Matrix & m, vector<bigfraction>& assignments, bool verbose,
		unordered_map<Equation*, int, hash<Equation*>, equation_eq> & visited_proofs,
		bignum & alpha);


// -------------TIMING RELATED ------------------------

/*
 * Timing vars
 */
int hnf_ticks = 0;
int lp_ticks = 0;
int preprocessing_ticks = 0;
int num_ilp_sat_internal = 0;


/*
 * State for exponential back-off
 */
#define MAX_BRANCH_INITIAL 50
#define INCREASE_FACTOR 2
#define INCREASE_ABS 100
#define ABS_LEVEL 100

int max_branches = MAX_BRANCH_INITIAL;
int cur_branches = 0;









int temp;

inline void clear_time()
{
	if(!ENABLE_TIMING) return;
	hnf_ticks = 0;
	lp_ticks = 0;
	preprocessing_ticks = 0;
	num_ilp_sat_internal = 0;
}

inline void time_start()
{
	if(!ENABLE_TIMING) return;
	temp = clock();
}

inline void time_end(int &i)
{
	if(!ENABLE_TIMING) return;
	int f = clock();
	int x = f-temp;
	i+=x;
}

inline string time_stats()
{
	double hnf = ((double)hnf_ticks)/((double)CLOCKS_PER_SEC);
	double lp = ((double)lp_ticks)/((double)CLOCKS_PER_SEC);
	double pre = ((double)preprocessing_ticks)/((double)CLOCKS_PER_SEC);

	string res;
	res+= "Preprocessing: " + float_to_string(pre) + "\n";
	res+= "HNF: " + float_to_string(hnf) + "\n";
	res+= "Simplex lp: " + float_to_string(lp) + "\n";
	res+= "Num ilp sat queries: " + int_to_string(num_ilp_sat_internal) + "\n";

	return res;
}


//------------TIMING END------------------




/*
 * Performs conventional branch-and-bound around a fractional component
 * of the solution.
 * f_index is the index of fractional component.
 */
bool branch_on_fraction(Matrix& m, vector<bigfraction>& assignments,
		int f_index, bool verbose,
		unordered_map<Equation*, int, hash<Equation*>, equation_eq>
		& visited_proofs, bignum& alpha)
{

	if(cur_branches > max_branches) {
		throw 0;
	}
	cur_branches++;

	if(ASSERT_ENABLED) assert(m.ignored_set_empty());

	vector<int> fraction_indices;
	for(unsigned int i=0; i < assignments.size(); i++)
	{
		if(!assignments[i].is_integer()){
			fraction_indices.push_back(i);
		}
	}
	int index = rand()%fraction_indices.size();
	f_index = fraction_indices[index];

	if(DEBUG)
	{
		cout << "Branch index " << index << " of " <<
		fraction_indices.size() << endl;

	}


	bigfraction f = assignments[f_index];
	bignum lower = f.round_down();
	Equation* lower_eq = new Equation(m.num_vars());
	lower_eq->set(f_index, 1);
	if(DEBUG) {
		cout << "=========Branching (low): " << m.get_vars()[f_index] << "<=" <<
		lower << endl;
	}

	// Check if the system already contains this equation
	// If not, branch around it.
	bool add_lower =
		(!m.contains(lower_eq) || lower < m.get_constant(lower_eq));

	if(add_lower) m.push_equation(lower_eq, lower);
	bool res1 = ilp_sat_internal(m, assignments, verbose, visited_proofs, alpha);
	if(add_lower) m.pop_equation();

	/*
	 * If this subproblem is SAT, the result is SAT.
	 */
	if(res1){
		if(DEBUG) {
			cout << "=========RESULT (low) : SAT==========" << endl;
		}
		return true;
	}
	if(DEBUG) {
		cout << "=========RESULT (low) : UNSAT==========" << endl;
	}

	bignum upper = f.round_up();


	if(DEBUG) {
		cout << "=========Branching (high): " << m.get_vars()[f_index] << ">=" <<
		upper << endl;
	}
	Equation* upper_eq = new Equation(m.num_vars());
	upper_eq->set(f_index, -1);

	bool add_upper = (
			!m.contains(upper_eq) || upper > -m.get_constant(upper_eq));
	if(add_upper) m.push_equation(upper_eq, -upper);
	bool res2 = ilp_sat_internal(m, assignments, verbose, visited_proofs, alpha);
	if(add_upper) m.pop_equation();
	if(DEBUG) {
		cout << "=========RESULT (high) : " << (res2? "SAT" : "UNSAT")
			<< "==========" << endl;
	}

	return res2;

}

/*
 * Rounds the given equation to the closest parallel planes
 * containing integer points on either side of the original
 * plane.
 */
inline void round_equation(Equation* eq, bignum &c,
		Equation* lower_eq, bignum& lower_const,
		Equation* upper_eq, bignum& upper_const)
{
	bignum gcd = eq->compute_gcd();

	for(int i=0; i < eq->num_entries(); i++) {
		bignum cur_c = eq->get(i)/gcd;
		lower_eq->set(i, cur_c);
		upper_eq->set(i, -cur_c);
	}

	lower_const = c/gcd;
	if(c < 0) lower_const -=1;
	upper_const = -(lower_const+1);
}


/*
 * A trivial solution assigns everything to 0.
 */

void set_trivial_solution(vector<bignum> & fa, int num_vars)
{
	for(int i=0; i < num_vars; i++)
	{
		fa.push_back(0);
	}
}

/*
 * Implements the cuts-from-proofs algorithm.
 */
bool ilp_sat_internal(Matrix & m, vector<bigfraction>& assignments, bool verbose,
		unordered_map<Equation*, int, hash<Equation*>, equation_eq> & visited_proofs,
		bignum& alpha)
{
	/*
	 * Check if LP-relaxation is UNSAT, if so result is UNSAT.
	 * If LP_releaxation is SAT and only contains integers, the result is SAT.
	 */
	slack_matrix sm(m);
	int f_index;
	time_start();
	bool res = lp_sat_internal(sm, &assignments, verbose, &f_index);
	time_end(lp_ticks);
	if(!res) return false;


	if(f_index == -1) return true;

	/*
	 * Compute the set of defining constraints
	 */
	vector<pair<Equation*, bignum> > defining_constraints;
	{
		Matrix::iterator it = m.begin();
		for(; it!= m.end(); it++) {
			Equation* e = it->first;

			bignum& c = it->second;
			bigfraction cc = e->evaluate(assignments);
			if(cc != c) continue;
			defining_constraints.push_back(*it);
		}
		if(ASSERT_ENABLED) assert(defining_constraints.size() > 0);

	}

	/*
	 * Compute proofs of UNSAT using HNF.
	 */
	set<pair<Equation*, bignum> > proofs;
	time_start();
	find_proofs(m, defining_constraints, f_index, proofs);
	time_end(hnf_ticks);
	set<pair<Equation*, bignum> >::iterator it6 = proofs.begin();


	/*
	 * Only branch around proofs that we've seen before.
	 */
	for(; it6!= proofs.end(); it6++) {
		Equation* e  = it6->first;
		visited_proofs[e]++;
		if(visited_proofs[e]<=1) continue;

		cur_branches++;

		bignum c = it6->second;

		if(DEBUG) cout << "Repeated proof: " << *e << " = " << c << endl;
		bignum lower_const, upper_const;
		Equation* upper_eq = new Equation(e->num_entries());
		Equation* lower_eq = new Equation(e->num_entries());
		round_equation(e, c, lower_eq, lower_const, upper_eq, upper_const);

		// Check if the max coefficient exceeds alpha
		bool exceeds_alpha = false;
		bignum max_coef = -1;
		for(int i=0; i<upper_eq->num_entries(); i++) {
			if(upper_eq->get(i) > alpha) {
				max_coef = upper_eq->get(i);
				exceeds_alpha = true;
				break;
			}
		}

		if(exceeds_alpha) {
			//cout << "alpha exceeded: " << max_coef << endl;
			throw 0;
			continue;
		}

		if(m.contains(upper_eq, upper_const)) continue;
		if(m.contains(lower_eq, lower_const)) continue;

		//cout << "******************* " << endl;

		m.mark_current_facets(assignments);

		m.push_equation(lower_eq->clone(), lower_const);
		slack_matrix sm1(m);
		time_start();
		bool res1 = lp_sat_internal(sm1, NULL, verbose, NULL);
		time_end(lp_ticks);
		m.pop_equation();

		m.push_equation(upper_eq->clone(), upper_const);
		slack_matrix sm2(m);
		time_start();
		bool res2 = lp_sat_internal(sm2, NULL, verbose, NULL);
		time_end(lp_ticks);
		m.pop_equation();

		m.clear_current_facets();

		if(!res1 && !res2) {
			return false;
		}
		if(res1 && res2) {
			if(DEBUG) cout << "Proof not added " << endl;
			continue;
		}

		if(res1){
			lower_eq->set_proof();
			m.insert(lower_eq, lower_const);
		}
		else{
			upper_eq->set_proof();
			m.insert(upper_eq, upper_const);
		}

	}


	bool final_res =  branch_on_fraction(m, assignments, f_index, verbose,
			visited_proofs, alpha);

	return final_res;
}

inline bignum compute_alpha(Matrix& m)
{
	bignum max = 1;
	Matrix::iterator it = m.begin();
	for(; it!= m.end(); it++)
	{
		Equation* eq = it->first;
		for(int i=0; i< eq->num_entries(); i++)
		{
			if(eq->get(i).abs() > max ) {
				max = eq->get(i).abs();
			}
		}
	}

	return max * (ALPHA_FACTOR * m.num_vars());
}


bool ilp_sat(Matrix & m, vector<bignum>* fa, bool verbose)
{

	clear_time();

	time_start();
	m.simplify();
	m.propagate_equalities();
	m.make_diophantine();
	time_end(preprocessing_ticks);

	if(is_trivially_sat(m)){
		if(fa!=NULL) set_trivial_solution(*fa, m.num_vars());
		return true;
	}

	bignum alpha = compute_alpha(m);

	vector<bigfraction> assignments;
	unordered_map<Equation*, int, hash<Equation*>, equation_eq>  visited_constraints;
	bool res = ilp_sat_internal(m, assignments, verbose, visited_constraints,
			alpha);

	if(ENABLE_TIMING) {
		cout << time_stats() << endl;
	}

	if(!res) {
		if(DEBUG) {
			cout << "FINAL RESULT: UNSAT" << endl;
		}
		return false;
	}

	if(DEBUG) {
		cout << "FINAL RESULT: SAT" << endl;
	}


	if(VERIFY_SOLUTION){
		assert(verify_solution(m, assignments));
	}
	if(fa == NULL) return res;
	m.adjust_assignments(assignments, *fa);
	return res;
}






bool ilp_sat_internal(Matrix & m, set< set<pair<Equation*, bignum> > >& neq,
		map<Equation*, set<bignum>, equation_lt >& terms_to_neq_constants,
		vector<bigfraction>& assignments,
		bool verbose)
{
	num_ilp_sat_internal++;

	bool sat = true;
	if(is_trivially_sat(m)){
		set_trivial_solution(assignments, m.num_vars());
	}
	else
	{
		bignum alpha = compute_alpha(m);
		unordered_map<Equation*, int, hash<Equation*>, equation_eq> visited_proofs;
		sat = ilp_sat_internal(m, assignments, verbose, visited_proofs, alpha);
	}
	if(!sat) return false;
	set< set<pair<Equation*, bignum> > >::iterator it = neq.begin();
	for(; it!= neq.end(); it++)
	{
		bool violated = true;
		if(ASSERT_ENABLED) assert(it->size() > 0);
		bool not_a_disjunct = (it->size() == 1);
		set<pair<Equation*, bignum> >::iterator it2 = it->begin();
		for(; it2!= it->end(); it2++)
		{
			Equation* e = it2->first;
			bignum c = it2->second;
			bigfraction res = e->evaluate(assignments);
			if(res != c) {
				violated = false;
				break;
			}
		}

		if(!violated) continue;

		/*
		 * We are not dealing with a disjunct but a single disequality.
		 * Important optimization: If a given term cannot be equal to multiple
		 * constants, i.e., T!= c_1 & T!=c_2 & ... & T!=c_k,
		 * generate k subproblems
		 * T<c_1 | ... | c_i <T < c_{i+1} ... | T >c_k
		 * This generates at most k subproblems instead of 2^k.
		 * Furthermore, the query c_i <T < c_{i+1} is avoided if
		 * c_{i+1} = c_i+1
		 */


		if(not_a_disjunct)
		{
			const set<pair<Equation*, bignum> >& cur_neqs = *it;
			assert(cur_neqs.size() == 1);
			Equation* term = cur_neqs.begin()->first;
			assert(terms_to_neq_constants.count(term) > 0);
			set<bignum> & neq_consts = terms_to_neq_constants[term];
			assert(neq_consts.size() > 0);

			// This optimization only applies if term  cannot  be
			// equal to more than one constant.
			if(neq_consts.size() > 1) {
				set<bignum>::iterator it = neq_consts.begin();
				int last = neq_consts.size()-1;
				for(int i=0; it!= neq_consts.end(); it++,i++) {
					bignum cur_const= *it;


					// Three cases: First, middle, and last
					// If first, make subproblem T < c_1
					bool check_middle = true;
					if(i == 0) {
						Equation* term_c = term->clone();
						// redundant query
						assert(!m.is_redundant(term_c, cur_const-1));
						m.push_equation(term_c, cur_const-1);

						bool res = ilp_sat_internal(m, neq,
								terms_to_neq_constants, assignments, verbose);
						m.pop_equation();
						if(res) return true;

					}
					// Last: T > c_k
					if(i == last) {
						Equation* term_c = term->clone();
						check_middle = false;
						term_c->flip_sign();
						assert(!m.is_redundant(term_c, -cur_const-1));

						m.push_equation(term_c, -cur_const-1);
						bool res = ilp_sat_internal(m, neq,
								terms_to_neq_constants, assignments, verbose);
						m.pop_equation();
						if(res) return true;
					}
					// In the middle: c_i < T < c_{i+1}
					if(check_middle) {
						Equation* term_c = term->clone();
						it++;
						bignum next = *it;
						it--;
						// If c_{i+1}=c_i+1, then the result is guaranteed UNSAT.
						if(next == cur_const+1) continue;
						Equation* gt_term = term_c;
						Equation* lt_term = term_c->clone();
						gt_term->flip_sign();
						int num_added = 0;

						if(!m.is_redundant(gt_term, -cur_const-1)) {
							m.push_equation(gt_term, -cur_const-1);
							num_added++;
						}
						if(!m.is_redundant(lt_term, next-1)) {
							m.push_equation(lt_term, next-1);
							num_added++;
						}
						if(num_added == 0)
						{
							assert(false);
						}
						bool res = ilp_sat_internal(m, neq,
							terms_to_neq_constants, assignments, verbose);
						if(res) return true;
						m.pop_equation();
						if(num_added == 2) m.pop_equation();
					}

				}
				return false;
			}

		}




		// All of the disjunctive disequalities were violated by the assignment.
		it2 = it->begin();
		for(; it2!= it->end(); it2++)
		{
			Equation* e = it2->first;
			bignum c = it2->second;
			Equation* lower = e->clone();
			Equation* upper = e->clone();
			upper->flip_sign();
			m.push_equation(upper, -c-1);
			bool res = ilp_sat_internal(m, neq, terms_to_neq_constants,
					assignments, verbose);
			m.pop_equation();
			if(res) {
				/*if(not_a_disjunct && other_res == 0)
				{
					cout << "MATRIX1: " << m.to_string() << endl;;
					cout << "Violated neq: " << e->to_string() << " != " << c << endl;
					map<Equation*, set<bignum> >::iterator it = terms_to_neq_constants.begin();
					cout << "Terms to neq constants: " << endl;
					for(; it!= terms_to_neq_constants.end(); it++) {
						cout << "\t" << it->first->to_string() << endl;
						set<bignum>::iterator it2 = it->second.begin();
						for(; it2!=it->second.end(); it2++ ) {
							cout << "\t " << *it2 << endl;
						}
					}
					assert(false);
				}*/
				return true;
			}
			m.push_equation(lower, c-1);
			res = ilp_sat_internal(m, neq,terms_to_neq_constants,
					assignments, verbose);
			m.pop_equation();
			if(res) {
				/*if(not_a_disjunct && other_res ==0) {

					cout << "MATRIX2: " << m.to_string() << endl;;
					cout << "Violated neq: " << e->to_string() << " != " << c << endl;
					map<Equation*, set<bignum> >::iterator it = terms_to_neq_constants.begin();
					cout << "Terms to neq constants: " << endl;
					for(; it!= terms_to_neq_constants.end(); it++) {
						cout << "\t" << it->first->to_string() << endl;
						set<bignum>::iterator it2 = it->second.begin();
						for(; it2!=it->second.end(); it2++ ) {
							cout << "\t " << *it2 << endl;
						}
					}
					assert(false);
				}*/
				return true;
			}

		}
		//if(not_a_disjunct) assert(other_res == 0);
		return false;

	}
	return true;

}

void reset_branch_counters()
{
	cur_branches = 0;
	max_branches = MAX_BRANCH_INITIAL;
}


bool ilp_sat(Matrix & m, set<set<pair<Equation*, bignum> > >& neq,
		vector<bignum>* fa, bool verbose)
{
	if(ASSERT_ENABLED) {
		if(neq.size() > 0){
			 set<set<pair<Equation*, bignum> > >::iterator it1 = neq.begin();
			 for(; it1!= neq.end(); it1++)
			 {
				 const set<pair<Equation*, bignum> > & s2 = *it1;
				 set<pair<Equation*, bignum> >::const_iterator it2 = s2.begin();
				 for(; it2 != s2.end(); it2++)
				 {
					 assert((int)m.get_vars().size() == it2->first->get_cols());
				 }

			 }

		}
	}

	clear_time();
	srand(time(NULL));



	/*
	 * A mapping from terms to the set of constants they cannot be
	 * equal to.
	 */
	map<Equation*, set<bignum>, equation_lt > terms_to_neq_constants;

	time_start();
	Matrix copy_m(m);
	copy_m.simplify();
	set<set<pair<Equation*, bignum> > > copy_neq;
	set<set<pair<Equation*, bignum> > >::iterator it = neq.begin();
	for(; it != neq.end(); it++) {
		set<pair<Equation*, bignum> > cur;
		set<pair<Equation*, bignum> >::iterator it2 = it->begin();
		for(; it2 != it->end(); it2++)
		{

			Equation* cur_term = it2->first->clone();
			cur.insert(pair<Equation*, bignum>(cur_term, it2->second));

		}
		copy_neq.insert(cur);

	}

	copy_m.propagate_equalities(&copy_neq);
	copy_m.make_diophantine();
	time_end(preprocessing_ticks);

	it = copy_neq.begin();
	for(; it != copy_neq.end(); it++) {
		set<pair<Equation*, bignum> > cur;
		if(it->size() != 1)
			continue;
		const pair<Equation*, bignum>  & neq = *it->begin();
		Equation* term = neq.first->clone();
		terms_to_neq_constants[term].insert(neq.second);
		//cout << "Inserting: " << term->to_string() << " != " << neq.second << endl;
	}

	vector<bigfraction> assignments;
	bool res;
	try {
		res = ilp_sat_internal(copy_m, copy_neq, terms_to_neq_constants,
				assignments, verbose);
	} catch(...)
	{
		cur_branches = 0;
		if(max_branches<ABS_LEVEL)
			max_branches*= INCREASE_FACTOR;
		else max_branches+=INCREASE_ABS;
		throw 0;
	}

	if(ENABLE_TIMING) {
		display(time_stats());
		cout << time_stats() << endl;
	}
	if(!res) {
		if(DEBUG) {
			cout << "FINAL RESULT: UNSAT" << endl;
		}
		return false;
	}

	if(DEBUG) {
		cout << "FINAL RESULT: SAT" << endl;
	}

	if(fa == NULL) return res;
	copy_m.adjust_assignments(assignments, *fa);
	return res;
}





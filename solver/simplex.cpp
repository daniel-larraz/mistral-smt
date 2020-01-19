/*
 * simplex.cpp
 *
 *  Created on: Aug 26, 2008
 *      Author: isil
 */

#include "mistral.h"
#include <iostream>
#include <sstream>
#include <math.h>

#include <stdio.h>
#include <assert.h>
#include <list>
#include "simplex.h"

using namespace std;
#include "matrix.h"
#include "slack_matrix.h"
#include "bigfraction.h"
#include "util.h"


#define ASSERT_ENABLED false
#define DEBUG false
#define VERIFY_SOLUTION false


// -------------- Prototypes ----------------
bool lp_sat_internal(slack_matrix & sm, vector<bigfraction>* fa, bool verbose,
		int *fraction_result_index);

inline void make_basic_sol_feasible(slack_matrix& sm);
inline int get_sat_assignments(slack_matrix& sm,
		vector<bigfraction> & assignments);

inline bool is_sat(slack_matrix& sm);
inline int get_pivot_row(slack_matrix & sm, int new_pivot);



//-----------------------------------------------------------------


/*
 * Given a variable index chosen as the new pivot, this function determines
 * the most constraining constraint and returns its row index.
 *
 * Note: In normal Simplex, it's possible that there is no constraint
 * which constraints a given variable. In such cases, the objective
 * function can be increased indefinitely. However, since we are only
 * interested in satisfiability, it is not possible that the optimal
 * value is unbounded; hence the assertion.
 */
inline int get_pivot_row(slack_matrix & sm, int new_pivot)
{
	bigfraction limit_increase = 0;
	int most_constraining_row = -1;


	for(int i= 0; i<sm.num_constraints(); i++) {
		bignum coefficient = sm.get(i, new_pivot);
		if(coefficient <= 0) {
			continue;
		}
		bignum constant = sm.get_constant(i);
		bigfraction cur_limit_increase(-constant, coefficient);
		if(most_constraining_row == -1 || cur_limit_increase<limit_increase){
			limit_increase = cur_limit_increase;
			most_constraining_row = i;
		}

		// Bland's rule to prevent cycles
		if(cur_limit_increase == limit_increase)
		{
			int old_pivot = sm.get_pivot(most_constraining_row);
			int cur_pivot = sm.get_pivot(i);
			if(cur_pivot < old_pivot)
			{
				most_constraining_row = i;
			}
		}

	}
	// In determining satisfiability, we should never hit the unbounded case.
	if(ASSERT_ENABLED) assert(most_constraining_row != -1);
	return most_constraining_row;
}


/*
 * A system Ax <= b is trivially SAT, if all b values are non-negative
 * and 0 is a satisfying assignment.
 */
bool is_trivially_sat(Matrix & m)
{
	if(m.size() == 0) return true;
	Matrix::iterator it = m.begin();
	for(; it!= m.end(); it++) {
		bignum constant = it->second;
		if(constant < 0) return false;
	}
	return true;

}


/*
 * Given the slack form matrix when Simplex terminates, we can determine
 * if the linear system is SAT by checking whether the basic solution
 * assigns 0 to x0.
 */
inline bool is_sat(slack_matrix& sm)
{
	// Check if basic solution assigns 0 to x0.
	int x0_pivot_row = -1;
	for(int r=0; r<sm.num_constraints(); ++r){
		int cur_pivot = sm.get_pivot(r);
		if(cur_pivot == 0){
			x0_pivot_row = r;
			break;
		}
	}
	if(x0_pivot_row == -1) return true;
	bignum constant = sm.get_constant(x0_pivot_row);
	return(constant==0);
}


/* Populates assignments with a satisfying assignment to the
 * original set of variables. A satisfying assignment assigns 0 to all
 * free variables and assigns (constant/coefficient of pivot var)
 * to the pivot variable in each row. Returns the index of the first
 * fractional solution in assignments.
 */
inline int get_sat_assignments(slack_matrix& sm,
		vector<bigfraction> & assignments)
{
	assignments.clear();
	int fraction_index = -1;
	for(int i=0; i<sm.num_actual_vars(); i++)
	{
		assignments.push_back(0);
	}

	for(int r=0; r<sm.num_constraints(); r++)
	{
		int _pivot_index = sm.get_pivot(r);
		int pivot_index = sm.get_principal_var(_pivot_index);
		if(pivot_index == -1) continue;

		bignum constant = -sm.get_constant(r);
		bignum coef = sm.get(r, _pivot_index);
		bigfraction val(constant, coef);

		int actual_index = sm.get_actual_index(pivot_index);
		if(sm.is_actual_var(_pivot_index)) assignments[actual_index] += val;
		else  assignments[actual_index] -= val;

		if(fraction_index == -1 && !val.is_integer()) {
			fraction_index = actual_index;
		}
	}
	return fraction_index;
}



/*
 * Performs the first step in Simplex by pivoting the constraint
 * with smallest coefficient.
 */
inline void make_basic_sol_feasible(slack_matrix& sm)
{
	/*
	 * Index of the row with minimum b in the original Ax <= b
	 * (maximum b in slack form.)
	 */
	int min_const_index = 0;
	bignum min_const_value = -sm.get_constant(0);
	for(int r=0; r<sm.num_constraints(); r++)
	{
		bignum constant = -sm.get_constant(r);
		if(constant < min_const_value) {
				min_const_value = constant;
				min_const_index = r;
		}
	}
	sm.pivot(min_const_index, 0);
}

/*
 * Check that the computed solution actually satisfies the constraints.
 */
bool verify_solution(Matrix& m, vector<bigfraction>& assignments)
{
	cout << "here" << endl;
	Matrix::iterator it = m.begin();
	for(; it!= m.end(); it++)
	{
		Equation* eq = it->first;
		bignum constant = it->second;
		bigfraction lhs = eq->evaluate(assignments);
		if(lhs > constant) return false;
	}
	return true;
}

/*
 * A trivial solution assigns everything to 0.
 */

void set_trivial_solution(vector<bigfraction> & fa, int num_vars)
{
	for(int i=0; i < num_vars; i++)
	{
		fa.push_back(0);
	}
}

/*
 * Determines satisfiability of the system Ax <= b over the reals
 * and if fa is non-null, yields a satisfying assignment.
 */
bool lp_sat(Matrix & m, vector<bigfraction>* fa, bool verbose)
{

	if(is_trivially_sat(m)){
		set_trivial_solution(*fa, m.num_vars());
		return true;
	}
	slack_matrix sm(m);

	bool delete_fa = false;
	if(VERIFY_SOLUTION && fa == NULL)
	{
		delete_fa = true;
		fa = new vector<bigfraction>();
	}
	bool res = lp_sat_internal(sm, fa, verbose, NULL);
	if(VERIFY_SOLUTION){
		assert(verify_solution(m, *fa));
	}
	if(VERIFY_SOLUTION && delete_fa) {
		delete fa;
	}
	return res;
}


/*
 * Actual Simplex implementation
 */
bool lp_sat_internal(slack_matrix & sm, vector<bigfraction>* fa, bool verbose,
		int *fraction_result_index)
{
	if(fraction_result_index) *fraction_result_index = -1;

	if(verbose) {
		display("Initial Matrix:\n"+sm.to_string() + "\n");
	}
	make_basic_sol_feasible(sm);

	/*
	 * The main Simplex algorithm
	 * Run simplex until all coefficients of the objective function
	 * are <= 0.
	 */
	while(true)
	{
		int new_pivot = sm.get_first_positive_index_obj_fun_row();
		if(new_pivot < 0) break;
		int pivot_row = get_pivot_row(sm, new_pivot);
		sm.pivot(pivot_row, new_pivot);

		if(verbose) {
			display("Pivot var: " + int_to_string(new_pivot) + " Pivot row" +
					int_to_string(pivot_row) + "\n" + sm.to_string() + "\n");
		}
	}

	bool res = is_sat(sm);
	if(!res) return false;
	if(fa == NULL) return true;


	int findex = get_sat_assignments(sm, *fa);
	if(fraction_result_index) *fraction_result_index = findex;
	return true;
}


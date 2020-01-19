/*
 * slack_matrix.h
 *
 *  Created on: Dec 8, 2008
 *      Author: isil
 *
 *  Implements a slack matrix used in the Simplex algorithm.
 */

#ifndef SLACK_MATRIX_H_
#define SLACK_MATRIX_H_

#include "matrix.h"
#include <set>
#include <map>
#include <unordered_set>
using namespace std;
#include "Equation.h"
#include "Matrix.h"

typedef unordered_set<Equation*, hash<Equation*>, equation_eq> eq_set;

class slack_matrix {
private:
	matrix* sm;

	vector<string> & orig_vars;

	/*
	 * Total number of variables
	 */
	int num_vars;

	/*
	 * Number of slack variables
	 */
	int num_slack_vars;

	/*
	 * Mapping from variable indices in the original matrix
	 * to their indices in the slack matrix
	 */
	int *index_mapping;

	/*
	 * Number of rows, including objective function
	 */
	int num_rows;

	/*
	 * Mapping from indices in the slack matrix to their index
	 * in the original matrix
	 */
	int* reverse_index_mapping;

	/*
	 * Variable indices (in the original matrix) that have greater
	 * than or equal to zero constraints.
	 */
	bool* geqz_constraints;




public:
	slack_matrix(Matrix & m);
	slack_matrix(slack_matrix & m);

	inline bignum get(int r, int c)
	{
		return sm->get(r, c);
	}

	inline bignum get_objective_coefficient(int c)
	{
		return sm->get(num_rows-1, c);
	}

	inline bignum get_objective_constant()
	{
		return sm->get(num_rows-1, num_vars);
	}

	inline void set_objective_coefficient(int c, bignum val)
	{
		sm->set(num_rows-1, c, val);
	}

	inline vector<string>& get_orig_vars()
	{
		return orig_vars;
	}


	inline void set(int r, int c, bignum e)
	{
		sm->set(r, c, e);
	}

	inline int num_constraints()
	{
		return num_rows-1;
	}

	inline int num_variables()
	{
		return num_vars;
	}

	inline int num_actual_vars()
	{
		return orig_vars.size();
	}

	inline int get_actual_index(int slack_index)
	{
		return reverse_index_mapping[slack_index];
	}
	inline int get_slack_index(int actual_index)
	{
		return index_mapping[actual_index];
	}

	inline bool is_actual_var(int index)
	{
		return reverse_index_mapping[index]!=-1;
	}

	inline bool is_slack_var(int index)
	{
		return index<num_slack_vars;
	}
	inline bool is_primed_var(int index)
	{
		return !is_slack_var(index) && !is_actual_var(index);
	}
	inline int get_principal_var(int index)
	{
		if(is_slack_var(index)) return -1;
		if(is_actual_var(index)) return index;
		return  index-1;

	}

	inline bignum get_constant(int r)
	{
		return sm->get_constant(r);
	}
	inline void set_constant(int r, int val)
	{
		sm->set_constant(r, val);
	}

	inline int get_pivot(int r)
	{
		return sm->get_pivot(r);
	}
	inline void set_pivot(int r, int pivot)
	{
		sm->set_pivot(r, pivot);
	}
	inline void multiply_row(int r, bignum factor)
	{
		sm->multiply_row(r, factor);
	}

	inline void pivot(int r, int c)
	{
		sm->pivot(r, c, true);
	}

	string get_name(int c);
	string to_string();


	inline int get_first_positive_index_obj_fun_row()
	{
		return sm->get_first_positive_index(num_rows-1);
	}




	friend ostream& operator <<(ostream &os,const slack_matrix &obj);

	~slack_matrix();




private:
	void populate_slack_matrix(Matrix& m);
	void construct_index_mapping(Matrix& m);
	void init_geqz_constraints(Matrix& m);
	void append(long int i, string & s);
	string int_to_string(long int i);
};

#endif /* SLACK_MATRIX_H_ */

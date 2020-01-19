/*
 * simplex.h
 *
 *  Created on: Aug 26, 2008
 *      Author: isil
 */

#ifndef SIMPLEX_H_
#define SIMPLEX_H_

#include "bigfraction.h"
#include "Matrix.h"
#include "time.h"
#include <vector>
class slack_matrix;

/*
 * lp_sat determines the satisfiability of a system Ax <= b using
 * the Simplex algorithm. If no satisfying assignment is desired,
 * pass NULL for sat_assign.
 */

bool lp_sat(Matrix & m, vector<bigfraction>* sat_assign, bool verbose);
bool verify_solution(Matrix& m, vector<bigfraction>& assignments);

bool lp_sat_internal(slack_matrix & sm, vector<bigfraction>* sat_assign,
		bool verbose, int *fraction_result_index);
bool is_trivially_sat(Matrix & m);
void set_trivial_solution(vector<bigfraction> & fa, int num_vars);




#endif /* SIMPLEX_H_ */

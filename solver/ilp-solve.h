/*
 * ilp-solve.h
 *
 *  Created on: Jan 15, 2009
 *      Author: tdillig
 */

#ifndef ILPSOLVE_H_
#define ILPSOLVE_H_


#include <vector>
#include <set>
#include "bignum.h"

class Matrix;
class Equation;

bool ilp_sat(Matrix & m, vector<bignum>* sat_assign, bool verbose);

bool ilp_sat(Matrix & m, set<set<pair<Equation*, bignum> > >& neq,
		vector<bignum>* sat_assign, bool verbose);

void reset_branch_counters();




#endif /* ILPSOLVE_H_ */

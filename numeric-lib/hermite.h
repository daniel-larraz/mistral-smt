/*
 * hermite.h
 *
 *  Created on: Dec 14, 2008
 *      Author: tdillig
 */

#ifndef HERMITE_H_
#define HERMITE_H_
#include "Equation.h"
#include "Matrix.h"
#include <vector>
using namespace std;

class matrix;


void find_proofs(Matrix& m, vector<pair<Equation*, bignum> > &active,
		int f_index, set<pair<Equation*, bignum> > & ndf);

void hnf(matrix & m);


#endif /* HERMITE_H_ */

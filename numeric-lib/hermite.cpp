/*
 * hermite.cpp
 *
 *  Created on: Dec 14, 2008
 *      Author: isil
 *
 * Implements functions for converting matrices to Hermite normal form and
 * for computing proofs of unsatisfiability for a given set of defining
 * constraints.
 */

#include "hermite.h"
#include <iostream>
using namespace std;
#include <vector>

#include "time.h"
#include "matrix.h"


#include "Equation.h"
#include "Matrix.h"
#include <vector>
#include <sstream>
using namespace std;




void hnf(matrix & m)
{
	int rows = m.num_rows();
	int cols = m.num_cols();
	bignum scratch[rows];


	for(int i=0; i<rows; i++)
	{
		bignum a_ii;
		for(int j=i+1; j<cols; j++)
		{
			bignum a_ij = m.get(i, j);
			a_ii = m.get(i, i);
			if(a_ij == 0) continue;
			bignum r, p, q;
			r = a_ii.compute_xgcd(a_ij, p, q);
			for(int rr=0; rr<rows; rr++){
				scratch[rr]= p*m.get(rr,i) + q*m.get(rr,j);
			}
			for(int rr=0; rr<rows; rr++) {
				m.set(rr,j, a_ii/r*m.get(rr, j) - a_ij/r*m.get(rr, i));
				m.set(rr, i, scratch[rr]);

			}

		}

		a_ii = m.get(i,i);
		if(a_ii < 0) {
			for(int j=0; j<rows; j++) {
				m.set(j, i, -m.get(j, i));
			}
		}
		assert(a_ii != 0);
		for(int j=0; j<i; j++)
		{
			bignum a_ij = m.get(i,j);
			a_ii = m.get(i, i);
			bignum r;
			r =  a_ij % a_ii;
			bignum ceil = a_ij/a_ii;

			if(r!=0){
				ceil+=1;
			}
			for(int r=0; r<rows; r++){
				bignum v1 = m.get(r,j);
				bignum v2 = v1 - ceil*m.get(r,i);
				m.set(r, j, v2);
			}
		}
	}
}






void find_proofs(Matrix& m, vector<pair<Equation*, bignum> >&
		defining_constraints, int f_index,
		set<pair<Equation*, bignum> > & proofs)
{

	int cols = defining_constraints[0].first->get_cols();
	int rows = defining_constraints.size();
	matrix mm(rows, cols);
	for(int r=0; r < rows; r++)
	{
		Equation *e = defining_constraints[r].first;
		for(int c=0; c <cols; c++) {
			mm.set(r,c,e->get(c));
		}
	}

	/*
	 * Compute linearly dependent rows.
	 */
	set<int> redundant;
	mm.compute_redundant_rows(redundant);

	bignum b[rows];

	matrix mat(rows-redundant.size(), cols);
	int cur_r = 0;
	for(int r=0; r < rows; r++)
	{
		if(redundant.count(r) >0) continue;

		bignum &c = defining_constraints[r].second;
		b[cur_r] = c;
		Equation *e = defining_constraints[r].first;
		for(int c=0; c <cols; c++) {
			bignum v = e->get(c);
			mat.set(cur_r,c, v);
		}
		cur_r++;
	}

	matrix orig(mat);

	hnf(mat);
	matrix hermite(mat.num_rows(), mat.num_rows());
	for(int r = 0; r < mat.num_rows(); r++) {
		for(int c = 0; c < mat.num_rows(); c++) {
			hermite.set(r,c,mat.get(r,c));
		}
	}
	matrix inverted(hermite.num_rows(), hermite.num_cols());

	bignum det = hermite.invert(inverted);
	bignum result[hermite.num_rows()];

	inverted.vector_multiply(b, result);

	int f_entry;
	for(f_entry=0; f_entry < inverted.num_rows(); f_entry++){
		bignum cur = result[f_entry];
		if(cur % det == 0) continue;

		bignum u[inverted.num_cols()];
		//cout << "Num cols in u: " << inverted.num_cols() << endl;
		for(int c=0; c<inverted.num_cols(); c++)
		{
			u[c] = inverted.get(f_entry, c);

		}
		// Compute uA
		bignum uA[orig.num_cols()];

		orig.row_vector_multiply(u, uA);


		Equation* eq = new Equation(m.num_vars());
		for(int i=0; i<m.num_vars(); i++)
		{
			bignum & e = uA[i];
			eq->set(i, e);
		}
		bignum & constant = result[f_entry];
		proofs.insert(pair<Equation*, bignum>(eq, constant));

	}
}





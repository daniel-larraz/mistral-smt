/*
 * Cooper.h
 *
 *  Created on: Nov 25, 2011
 *      Author: isil
 */

#ifndef COOPER_H_
#define COOPER_H_

#include <set>
using namespace std;
#include "bignum.h"

class CNode;
class Term;

class Cooper {
private:
	CNode* c;
	Term* elim_t;
	bignum delta;
	set<Term*> a_terms; // x<a
	set<Term*> b_terms; // b<x
	CNode* res;

public:
	Cooper(CNode* c, Term* elim_t);
	CNode* get_result();
	~Cooper();
private:

	/*
	 * Rewrites the formula Ex. F to an equivalent formula Ex. F'
	 * such that no leaf in the formula contains x with coefficients.
	 */
	void remove_coefficients();

	void collect_coefficients(CNode* c, set<bignum>& coefficients);

	bignum get_lcm(set<bignum>& coefs);

	CNode* normalize_coefficients(CNode* c, bignum lcm);

	/*
	 * delta is defined same way as in the Cooper paper, i.e.,
	 * lcm of constants in the mod terms
	 */
	bignum compute_delta();
	bignum compute_delta_rec(bignum delta, CNode* c);

	/*
	 * Compute terms a such that x<a and terms b such that b<x
	 */
	void compute_a_and_b_terms(CNode* c, bool in_neg);


	/*
	 * Computes the left or right infinite projection of c
	 */
	CNode* compute_infinite_projection(CNode* c, bool left,
			Term* rt);




};

#endif /* COOPER_H_ */

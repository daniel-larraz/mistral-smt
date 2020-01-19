/*
 * Equation.h
 *
 *  Created on: Dec 9, 2008
 *      Author: tdillig
 */

#ifndef EQUATION_H_
#define EQUATION_H_
#include "bignum.h"

#include <unordered_map>
#include <unordered_set>
#include <string.h>
using namespace __gnu_cxx;
#include <vector>
using namespace std;

#define EQ_ASSERT true

#include "bigfraction.h"

class Equation {
	friend class slack_matrix;
public:
	data_type* eq;
	int cols;
	bool infinite;
	bool proof;

	/*
	 * Careful! This constructor does NOT finish initializing.
	 */
	inline Equation(int cols, bool infinite)
	{
		this->cols = cols;
		eq = new data_type[cols];
		memset(eq, 0, sizeof(data_type) * cols);
		this->infinite = infinite;
		proof = false;
	}



	inline void set_initial_value(int c, data_type d){
		assert(c>=0 && c<cols);
		if(!infinite){
			eq[c].d = d.d;
			return;
		}
		mpz_init_set(eq[c].i, d.i);
	}

	inline size_t compute_hash_d()
	{
		size_t hash_code = 0;
		for(int i=0; i < cols; i++)
		{
			hash_code+=(eq[i].d<<((5*i)%27));
		}
		return hash_code;
	}

	inline size_t compute_hash_i()
	{
		assert(infinite);
		size_t hash_code = 0;
		for(int i=0; i < cols; i++)
		{
			long int val = mpz_get_si(eq[i].i);
			hash_code+=(val<<((5*i)%27));
		}
		return hash_code;
	}

	inline void make_infinite()
	{
		infinite = true;
		for(int i=0; i < cols; i++){
			long int val = eq[i].d;
			mpz_init_set_si(eq[i].i, val);
		}
	}

public:
	inline Equation* clone()
	{
		Equation* res = new Equation(cols);
		if(!infinite){
			memcpy(res->eq, eq, cols*sizeof(data_type));
			res->infinite = false;
			return res;
		}
		for(int i=0; i < cols; i++) {
			mpz_init_set(res->eq[i].i, eq[i].i);
		}
		res->infinite = true;
		return res;
	}
	inline void divide(bignum b)
	{
		if(!infinite && !b.infinite)
		{
			for(int c=0; c < cols; c++) {
				eq[c].d/= b.data.d;
			}
			return;
		}
		if(infinite && !b.infinite)
		{
			mpz_t temp;
			mpz_init_set_si(temp, b.data.d);
			for(int c=0; c < cols; c++) {
				mpz_tdiv_q(eq[c].i, eq[c].i, temp);
			}
			mpz_clear(temp);
			return;
		}

		if(!infinite && b.infinite)
		{
			make_infinite();
		}
		for(int c=0; c < cols; c++) {
			mpz_tdiv_q(eq[c].i, eq[c].i, b.data.i);
		}

	}

	inline Equation(int cols)
	{
		this->cols = cols;
		eq = new data_type[cols];
		memset(eq, 0, sizeof(data_type) * cols);
		this->infinite = false;
		proof = false;
	}

	inline void set_proof()
	{
		proof = true;
	}

	inline void unset_proof()
	{
		proof = false;
	}

	inline bool is_proof()
	{
		return proof;
	}

	inline bignum compute_gcd(bool skip_last = false)
	{
		if(cols == 0) return bignum(0);
		if(infinite) {
			mpz_t gcd;
			mpz_init_set(gcd, eq[0].i);
			mpz_abs(gcd, gcd);
			int end = skip_last? cols-1:cols;
			for(int i=1; i < end; i++) {
				mpz_gcd(gcd, gcd, eq[i].i);
			}
			bignum b(gcd);
			mpz_clear(gcd);
			return b;
		}
		long int gcd = labs(eq[0].d);
		int end = skip_last? cols-1:cols;
		for(int i=1; i < end; i++) {
			gcd = bignum::compute_int_gcd(gcd, eq[i].d);
		}
		return bignum(gcd);
	}

	inline int get_cols()
	{
		return cols;
	}

	inline bool satisfies(vector<bigfraction> &a)
	{
		assert((int)a.size()==cols-1);
		bigfraction cur;
		for(int i=0; i < cols-1; i++) {
			cur+=a[i]*get(i);
		}
		return cur == get(cols-1);
	}

	inline bigfraction evaluate(vector<bigfraction>& a)
	{
		assert((int)a.size()==cols);
		bigfraction cur;
		for(int i=0; i < cols; i++) {
			cur+=a[i]*get(i);
		}
		return cur;
	}

	inline void set(int c, const bignum b)
	{
		//assert(c>=0 && c < this->cols);

		if(!infinite && !b.infinite) {
			eq[c].d = b.data.d;
			return;
		}
		if(!infinite && b.infinite) {
			make_infinite();
			mpz_set(eq[c].i, b.data.i);
			return;
		}
		if(infinite && !b.infinite) {
			mpz_set_si(eq[c].i, b.data.d);
			return;
		}
		mpz_set(eq[c].i, b.data.i);
	}

	inline void flip_sign(){
		for(int i=0; i < cols; i++){
			flip_sign(i);
		}

	}


	inline void flip_sign(int c){
		if(!infinite){
			eq[c].d = -eq[c].d;
			return;
		}
		mpz_neg(eq[c].i, eq[c].i);
	}

	inline bignum get(int c)
	{
		if(!infinite)
			return bignum(eq[c].d);
		return bignum(eq[c].i);
	}

	inline size_t hash_code()
	{
		if(infinite) return compute_hash_i();
		return compute_hash_d();
	}

	friend ostream& operator <<(ostream &os,const Equation &obj);


	inline int num_entries()
	{
		return cols;
	}

	inline string to_string()
	{
		string res;
		for(int i=0; i < cols; i++) {
			res+=get(i).to_string() +"\t";
		}
		return res;
	}

	inline bool operator==(Equation& other)
	{
		if(!infinite && !other.infinite){
			for(int i=0; i < cols; i++) {
				if(eq[i].d!=other.eq[i].d) return false;
			}
			return true;
		}
		if(!infinite && other.infinite){
			for(int i=0; i < cols; i++) {
				if(mpz_cmp_si(other.eq[i].i, eq[i].d) !=0) return false;
			}
			return true;
		}
		if(infinite && !other.infinite){
			for(int i=0; i < cols; i++) {
				if(mpz_cmp_si(eq[i].i, other.eq[i].d) !=0) return false;
			}
			return true;
		}
		for(int i=0; i < cols; i++) {
			if(mpz_cmp(eq[i].i, other.eq[i].i) !=0) return false;
		}
		return true;
	}
	inline bool operator<(Equation& other)
	{
		if(!infinite && !other.infinite){
			for(int i=0; i < cols; i++) {
				if(eq[i].d<other.eq[i].d) return true;
				if(eq[i].d>other.eq[i].d) return false;
			}
			return false;
		}
		if(!infinite && other.infinite){
			for(int i=0; i < cols; i++) {
				int res = mpz_cmp_si(other.eq[i].i, eq[i].d);
				if(res > 0) return true;
				if(res < 0) return false;
			}
			return false;
		}
		if(infinite && !other.infinite){
			for(int i=0; i < cols; i++) {
				int res = mpz_cmp_si(eq[i].i, other.eq[i].d);
				if(res < 0) return true;
				if(res > 0) return false;
			}
			return false;
		}
		for(int i=0; i < cols; i++) {
			int res = mpz_cmp(eq[i].i, other.eq[i].i);
			if(res < 0) return true;
			if(res > 0) return false;
		}
		return false;
	}



	inline bool operator!=(Equation& other)
	{
		return !(*this==other);
	}

	inline ~Equation()
	{
		if(infinite){
			for(int i=0; i < cols; i++) {
				mpz_clear(eq[i].i);
			}
		}
		delete[] eq;
	}
};

namespace std {
/**
        Explicit template specialization of hash of a string class,
        which just uses the internal char* representation as a wrapper.
 */



template <>
struct hash<Equation*> {
        inline size_t operator() (const Equation*const  & x) const {
        	Equation* xx = (Equation*)x;
				if(EQ_ASSERT) assert(xx != NULL);
                return xx->hash_code();
        }
        };
}


struct equation_eq
{
  inline bool operator()(const Equation*const _e1, const Equation*const _e2) const
  {
	  Equation* e1 = (Equation*)_e1;
	  Equation* e2 = (Equation*)_e2;
	  if(EQ_ASSERT) assert(e1 != NULL);
	  if(EQ_ASSERT) assert(e2 != NULL);
	  return *e1==*e2;
  }
};

struct equation_lt
{
  inline bool operator()(const Equation*const _e1, const Equation*const _e2) const
  {
	  Equation* e1 = (Equation*)_e1;
	  Equation* e2 = (Equation*)_e2;
	  if(EQ_ASSERT) assert(e1 != NULL);
	  if(EQ_ASSERT) assert(e2 != NULL);
	  return *e1<*e2;
  }
};


#endif /* EQUATION_H_ */

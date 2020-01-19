/*
 * bignum.h
 *
 *  Created on: Dec 6, 2008
 *      Author: tdillig
 *
 *  Infinite precision arithmetic library based on GNU MP bignum library.
 *  This library only compiles on 64-bit machines.
 *  It performs computation natively on 64-bit integers until an
 *  overflow is detected and switches to GNU bignums only when necessary.
 */

#ifndef BIGNUM_H_
#define BIGNUM_H_

#include <gmp.h>
#include <iostream>
#include <assert.h>
#include <stdlib.h>
using namespace std;


union data_type
{
  long int d;
  mpz_t i;
};


class bignum
{
	public:
	data_type data;
	bool infinite;

	inline bignum()
	{
 		data.d = 0;
 		infinite = false;
	}

	inline bignum(const bignum & other)
	{
		infinite = other.infinite;
		if(!infinite)
		{
			data.d = other.data.d;
			return;
		}
 		mpz_init_set(data.i, other.data.i);
	}

	inline bignum(long int i)
	{
		data.d = i;
		infinite = false;
	}

	inline bignum(string &s)
	{
		infinite = true;
		mpz_init_set_str(data.i, s.c_str(), 10);
	}

	inline bignum(const mpz_t & i)
	{
		infinite = true;
		mpz_init_set(data.i, i);
	}

	inline ~bignum()
	{
		if(!infinite) return;
		mpz_clear(data.i);
	}

	inline const bignum & operator=(const bignum & other)
	{
		if(!infinite && !other.infinite)
		{
			data.d = other.data.d;
			infinite = false;
			return *this;
		}
		if(!infinite && other.infinite)
		{
			mpz_init_set(data.i, other.data.i);
			infinite = true;
			return *this;
		}
		if(infinite && !other.infinite)
		{
			mpz_set_si(data.i, other.data.d);
			return *this;
		}
		//both infinite
		mpz_set(data.i, other.data.i);
		return *this;

	}

	inline bignum abs()
	{
		if(!infinite) return bignum(labs(data.d));
		bignum res;
		res.set_infinite();
		mpz_abs(res.data.i, data.i);
		return res;
	}

	inline bool fits_long_int()
	{
		if(!infinite) return true;
		return mpz_fits_slong_p(data.i);
	}

	inline long int to_int()
	{
		if(!infinite) return data.d;
		return mpz_get_si(data.i);
	}
	inline double to_double()
	{
		if(!infinite)
			return ((double)data.d);
		return mpz_get_d(data.i);
	}

	inline double divide(bignum & other)
	{
		if(!infinite && !other.infinite){
			return ((double)data.d)/((double)other.data.d);
		}
		if(infinite && !other.infinite){
			double my_d = mpz_get_d(data.i);
			return my_d/((double)other.data.d);
		}
		if(!infinite && other.infinite){
			double other_d = mpz_get_d(other.data.i);
			return ((double)data.d)/other_d;
		}
		double my_d = mpz_get_d(data.i);
		double other_d = mpz_get_d(other.data.i);
		return my_d/other_d;
	}

	inline bool divisible(bignum & other)
	{
		if(!infinite && !other.infinite)
			return data.d % other.data.d == 0;

		if(infinite && !other.infinite){
			return mpz_divisible_ui_p(data.i, (unsigned long int)other.data.d);
		}
		if(!infinite && other.infinite){
			mpz_t me;
			mpz_init_set_si(me, data.d);
			bool res = mpz_divisible_p(me, other.data.i);
			mpz_clear(me);
			return res;
		}
		return mpz_divisible_p(data.i, other.data.i);
	}

	inline bignum compute_gcd(const bignum & other)
	{
		if(!infinite && !other.infinite){
			return compute_int_gcd(data.d, other.data.d);
		}
		if(infinite && !other.infinite){
			mpz_t temp;
			mpz_init_set_si(temp, other.data.d);
			mpz_t gcd;
			mpz_init(gcd);
			mpz_gcd(gcd, temp, data.i);
			bignum b(gcd);
			mpz_clear(gcd);
			mpz_clear(temp);
			return b;
		}
		if(!infinite && other.infinite){
			mpz_t temp;
			mpz_init_set_si(temp, data.d);
			mpz_t gcd;
			mpz_init(gcd);
			mpz_gcd(gcd, temp, other.data.i);
			bignum b(gcd);
			mpz_clear(gcd);
			mpz_clear(temp);
			return b;
		}
		mpz_t gcd;
		mpz_init(gcd);
		mpz_gcd(gcd, data.i, other.data.i);
		bignum b(gcd);
		mpz_clear(gcd);
		return b;


	}
	inline bignum compute_lcm(const bignum & other)
	{
		bignum gcd = this->compute_gcd(other);
		bignum res = *this * other;
		res/=gcd;
		return res;
	}

/*
 * res = gcd(a, b) = p*a+q*b
 */
inline bignum compute_xgcd(bignum & other, bignum & p, bignum & q)
{
	mpz_t a, b;
	if(infinite) mpz_init_set(a, data.i);
	else mpz_init_set_si(a, data.d);

	if(other.infinite) mpz_init_set(b, other.data.i);
	else mpz_init_set_si(b, other.data.d);

	mpz_t _p, _q, gcd;
	mpz_init(_p);
	mpz_init(_q);
	mpz_init(gcd);
	mpz_gcdext (gcd,_p, _q, a, b);
	bignum res_gcd;

	bignum pp(_p);
	bignum qq(_q);

	if(mpz_fits_slong_p(gcd))
		res_gcd = mpz_get_si(gcd);
	else res_gcd = gcd;

	if(mpz_fits_slong_p(_p))
		p = mpz_get_si(_p);
	else p = _p;

	if(mpz_fits_slong_p(_q))
		q = mpz_get_si(_q);
	else q = _q;

	mpz_clear(a);
	mpz_clear(b);
	mpz_clear(_p);
	mpz_clear(_q);
	mpz_clear(gcd);
	return res_gcd;
}

	inline void operator*=(bignum& o1)
	{
		if(is_infinite() || o1.is_infinite())
		{
			make_infinite();
			o1.make_infinite();
			mpz_mul(data.i, data.i, o1.data.i);
			return;
		}

		if(m_overflow(data.d, o1.data.d)) {

			o1.make_infinite();
			make_infinite();
			mpz_mul(data.i, data.i, o1.data.i);
			return;
		}


		data.d*=o1.data.d;
	}


	inline bignum operator*(bignum o1)
	{
		bignum res;
		if(is_infinite() || o1.is_infinite())
		{
			res.set_infinite();
			make_infinite();
			o1.make_infinite();
			mpz_mul(res.data.i, data.i, o1.data.i);
			return res;
		}

		if(m_overflow(data.d, o1.data.d)) {
			res.set_infinite();
			o1.make_infinite();
			make_infinite();
			mpz_mul(res.data.i, data.i, o1.data.i);
			return res;
		}


		res.data.d = data.d*o1.data.d;
		return res;
	}

	inline bignum operator%(bignum o1)
	{
		bignum res;
		if(is_infinite() && o1.is_infinite())
		{
			res.set_infinite();
			mpz_tdiv_r(res.data.i, data.i, o1.data.i);
			if(mpz_fits_slong_p(res.data.i))
			{
				long int val = mpz_get_si(res.data.i);
				mpz_clear(res.data.i);
				res.infinite = false;
				res.data.d = val;
			}
			return res;
		}
		if(is_infinite() && !o1.is_infinite())
		{
			res.set_infinite();
			mpz_t other;
			mpz_init_set_si(other, o1.data.d);
			mpz_tdiv_r(res.data.i, data.i, other);
			mpz_clear(other);
			if(mpz_fits_slong_p(res.data.i))
			{
				long int val = mpz_get_si(res.data.i);
				mpz_clear(res.data.i);
				res.infinite = false;
				res.data.d = val;
			}
			return res;
		}
		if(!is_infinite() && o1.is_infinite())
		{
			res.set_infinite();
			mpz_t me;
			mpz_init_set_si(me, data.d);
			mpz_tdiv_r(res.data.i, me , o1.data.i);
			mpz_clear(me);
			if(mpz_fits_slong_p(res.data.i))
			{
				long int val = mpz_get_si(res.data.i);
				mpz_clear(res.data.i);
				res.infinite = false;
				res.data.d = val;
			}
			return res;
		}
		res.data.d = data.d%o1.data.d;
		return res;
	}

	inline bignum operator/(bignum o1)
	{
		bignum res;
		if(is_infinite() && o1.is_infinite())
		{
			mpz_t temp;
			mpz_init(temp);
			mpz_tdiv_q(temp, data.i, o1.data.i);
			if(mpz_fits_slong_p(temp)){
				res.infinite = false;
				long int val = mpz_get_si(temp);
				mpz_clear(temp);
				res.data.d = val;
				return res;
			}
			res.set_infinite();
			mpz_set(res.data.i, temp);
			mpz_clear(temp);
			return res;
		}
		if(is_infinite() && !o1.is_infinite())
		{
			mpz_t temp;
			mpz_init(temp);
			mpz_t temp2;
			mpz_init_set_si(temp2, o1.data.d);
			mpz_tdiv_q(temp, data.i, temp2);
			if(mpz_fits_slong_p(temp)){
				res.infinite = false;
				long int val = mpz_get_si(temp);
				mpz_clear(temp);
				mpz_clear(temp2);
				res.data.d = val;
				return res;
			}
			res.set_infinite();
			mpz_set(res.data.i, temp);
			mpz_clear(temp);
			mpz_clear(temp2);
			return res;
		}
		if(!is_infinite() && o1.is_infinite())
		{
			mpz_t temp;
			mpz_init(temp);
			mpz_t temp2;
			mpz_init_set_si(temp2, data.d);
			mpz_tdiv_q(temp, temp2, o1.data.i);
			if(mpz_fits_slong_p(temp)){
				res.infinite = false;
				long int val = mpz_get_si(temp);
				mpz_clear(temp);
				mpz_clear(temp2);
				res.data.d = val;
				return res;
			}
			res.set_infinite();
			mpz_set(res.data.i, temp);
			mpz_clear(temp);
			mpz_clear(temp2);
			return res;
		}
		res.data.d = data.d/o1.data.d;
		return res;
	}


	inline bignum divexact(bignum & o1)
		{
			bignum res;
			if(is_infinite() && o1.is_infinite())
			{
				mpz_t temp;
				mpz_init(temp);
				mpz_divexact(temp, data.i, o1.data.i);
				if(mpz_fits_slong_p(temp)){
					res.infinite = false;
					long int val = mpz_get_si(temp);
					mpz_clear(temp);
					res.data.d = val;
					return res;
				}
				res.set_infinite();
				mpz_set(res.data.i, temp);
				mpz_clear(temp);
				return res;
			}
			if(is_infinite() && !o1.is_infinite())
			{
				mpz_t temp;
				mpz_init(temp);
				mpz_t temp2;
				mpz_init_set_si(temp2, o1.data.d);
				mpz_divexact(temp, data.i, temp2);
				if(mpz_fits_slong_p(temp)){
					res.infinite = false;
					long int val = mpz_get_si(temp);
					mpz_clear(temp);
					mpz_clear(temp2);
					res.data.d = val;
					return res;
				}
				res.set_infinite();
				mpz_set(res.data.i, temp);
				mpz_clear(temp);
				mpz_clear(temp2);
				return res;
			}
			if(!is_infinite() && o1.is_infinite())
			{
				mpz_t temp;
				mpz_init(temp);
				mpz_t temp2;
				mpz_init_set_si(temp2, data.d);
				mpz_divexact(temp, temp2, o1.data.i);
				if(mpz_fits_slong_p(temp)){
					res.infinite = false;
					long int val = mpz_get_si(temp);
					mpz_clear(temp);
					mpz_clear(temp2);
					res.data.d = val;
					return res;
				}
				res.set_infinite();
				mpz_set(res.data.i, temp);
				mpz_clear(temp);
				mpz_clear(temp2);
				return res;
			}
			res.data.d = data.d/o1.data.d;
			return res;
		}


	inline void operator/=(bignum& o1)
	{
		if(is_infinite() || o1.is_infinite())
		{
			make_infinite();
			o1.make_infinite();
			mpz_tdiv_q(data.i, data.i, o1.data.i);
			return;
		}


		data.d/=o1.data.d;
	}

	inline void operator+=(bignum o1)
	{

		if(is_infinite() || o1.is_infinite())
		{
			make_infinite();
			o1.make_infinite();
			mpz_add(data.i, data.i, o1.data.i);
			return;
		}
		if(a_overflow(data.d, o1.data.d)) {
			make_infinite();
			o1.make_infinite();
			mpz_add(data.i, data.i, o1.data.i);
			return;
		}


		data.d+=o1.data.d;
	}

	inline bignum operator+(bignum o1)
	{
		bignum res;
		if(is_infinite() || o1.is_infinite())
		{
			res.set_infinite();
			make_infinite();
			o1.make_infinite();
			mpz_add(res.data.i, data.i, o1.data.i);
			return res;
		}

		if(a_overflow(data.d, o1.data.d)) {
			res.set_infinite();
			o1.make_infinite();
			make_infinite();
			mpz_add(res.data.i, data.i, o1.data.i);
			return res;
		}


		res.data.d = data.d+o1.data.d;
		return res;
	}




	inline bignum operator-(bignum o1)
	{
		bignum res;
		if(is_infinite() || o1.is_infinite())
		{
			res.set_infinite();
			make_infinite();
			o1.make_infinite();
			mpz_sub(res.data.i, data.i, o1.data.i);
			return res;

		}

		res.data.d = data.d-o1.data.d;
		return res;
	}


	inline bignum operator-()
	{
		bignum res;
		if(is_infinite())
		{
			res.set_infinite();
			mpz_neg(res.data.i, data.i);
			return res;

		}

		res.data.d = -data.d;
		return res;
	}

	inline void operator-=(bignum o1)
	{
		if(is_infinite() || o1.is_infinite())
		{
			make_infinite();
			o1.make_infinite();
			mpz_sub(data.i, data.i, o1.data.i);
			return;

		}

		data.d-=o1.data.d;
	}

	inline bool operator!=(const bignum other)
	{
		return !(*this == other);
	}

	inline bool operator!=(long int other)
	{
		return !(*this == other);
	}

	inline bool operator==(const bignum& other)
	{
		if(!is_infinite() && !other.is_infinite()) {
			return data.d == other.data.d;
		}
		if(is_infinite() && !other.is_infinite()) {
			return mpz_cmp_si(data.i, other.data.d)==0;
		}
		if(!is_infinite() && other.is_infinite()) {
			return mpz_cmp_si(other.data.i, data.d)==0;
		}
		return mpz_cmp(data.i, other.data.i) == 0;
	}

	inline bool operator==(long int i)
	{
		if(!is_infinite()) {
			return data.d == i;
		}
		return mpz_cmp_si(data.i, i)==0;
	}

	inline bool operator<(const bignum& other) const
	{
		if(!is_infinite() && !other.is_infinite()) {
			return data.d < other.data.d;
		}
		if(is_infinite() && !other.is_infinite()) {
			return mpz_cmp_si(data.i, other.data.d)<0;
		}
		if(!is_infinite() && other.is_infinite()) {
			return mpz_cmp_si(other.data.i, data.d)>0;
		}
		return mpz_cmp(data.i, other.data.i) < 0;
	}

	inline bool operator<(long int i)
	{
		if(!is_infinite()) {
			return data.d < i;
		}
		return mpz_cmp_si(data.i, i)<0;
	}

	inline bool operator<=(const bignum& other)
	{
		if(!is_infinite() && !other.is_infinite()) {
			return data.d <= other.data.d;
		}
		if(is_infinite() && !other.is_infinite()) {
			return mpz_cmp_si(data.i, other.data.d)<=0;
		}
		if(!is_infinite() && other.is_infinite()) {
			return mpz_cmp_si(other.data.i, data.d)>=0;
		}
		return mpz_cmp(data.i, other.data.i) <= 0;
	}
	inline bool operator<=(long int i)
	{
		if(!is_infinite()) {
			return data.d <= i;
		}
		return mpz_cmp_si(data.i, i)<=0;
	}

	inline bool operator>(const bignum& other)
	{
		if(!is_infinite() && !other.is_infinite()) {
			return data.d > other.data.d;
		}
		if(is_infinite() && !other.is_infinite()) {
			return mpz_cmp_si(data.i, other.data.d)>0;
		}
		if(!is_infinite() && other.is_infinite()) {
			return mpz_cmp_si(other.data.i, data.d)<0;
		}
		return mpz_cmp(data.i, other.data.i) > 0;
	}

	inline bool operator>(long int i)
	{
		if(!is_infinite()) {
			return data.d > i;
		}
		return mpz_cmp_si(data.i, i)>0;
	}

	inline bool operator>=(const bignum& other)
	{
		if(!is_infinite() && !other.is_infinite()) {
			return data.d >= other.data.d;
		}
		if(is_infinite() && !other.is_infinite()) {
			return mpz_cmp_si(data.i, other.data.d)>=0;
		}
		if(!is_infinite() && other.is_infinite()) {
			return mpz_cmp_si(other.data.i, data.d)<=0;
		}
		return mpz_cmp(data.i, other.data.i) >= 0;
	}

	inline bool operator>=(long int i)
	{
		if(!is_infinite()) {
			return data.d >= i;
		}
		return mpz_cmp_si(data.i, i)>=0;
	}

	string to_string()
	{
		if(!is_infinite()) {
			char temp[100];
			sprintf(temp, "%ld",  data.d);
			return string(temp);
		}
		char* res = mpz_get_str(NULL, 10, data.i);
		string s(res);
		free(res);
		return s;
	}

	//--------------------------

	friend ostream& operator <<(ostream &os,const bignum &obj);



	static inline bool m_overflow(long int c, long int e)
	{
		int ci = c;
		int ei = e;
		return c != ((long int)ci) || e != ((long int)ei);
	}

	static inline bool a_overflow(long int a, long int b)
	{
		long int res = a + b;
		if(b>=0){
			if(res<a)
				return true;
		}
		else if(res>a)
			return true;
		return false;
	}

	static inline long int compute_int_gcd(long int _a, long int _b)
	{
		long int a = labs(_a);
		long int b = labs(_b);

		long int t;
		while(b!=0){
			t = a;
			a = b;
			b = t % b;
		}
		return a;
	}
	private:

	inline void set_normal()
	{
		infinite = false;
	}
	inline bool is_infinite() const
	{
		return infinite;
	}

	inline void set_infinite()
	{
		if(infinite) return;
		mpz_init(data.i);
		infinite = true;
	}

	inline void make_infinite()
	{
		if(is_infinite()) return;
		long int val = data.d;
		mpz_init_set_si(data.i, val);
		infinite = true;
	}


};

ostream& operator <<(ostream &os,const bignum &_obj);



#endif /* BIGNUM_H_ */

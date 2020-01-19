/*
 * bigfraction.h
 *
 *  Created on: Dec 8, 2008
 *      Author: tdillig
 *
 *  Bigfraction library based on bignum.h.
 */

#ifndef BIGFRACTION_H_
#define BIGFRACTION_H_

#include "bignum.h"

class bigfraction {
private:
	bignum n;
	bignum d;
public:
	inline bigfraction():n(0), d(1)
	{

	}
	inline bigfraction(bignum n):n(n), d(1)
	{

	}
	inline bigfraction(long int n):n(n), d(1)
	{

	}
	inline bigfraction(bignum n, bignum d):n(n), d(d)
	{
		simplify();
	}
	inline const bigfraction& operator=(bigfraction other)
	{
		n =other.n;
		d =other.d;
		simplify();
		return *this;

	}
	inline const bigfraction& operator=(bignum other)
	{
		n =other;
		d =1;
		return *this;

	}

	inline bool is_integer()
	{
		return (d==1 || n==0);
	}

	inline double to_double()
	{
		return n.to_double()/d.to_double();
	}

	inline ~bigfraction()
	{

	}
	inline string to_string()
	{
		string res;
		if(d == 0) return "NaN";
		if(d == 1) return n.to_string();
		if(n == 0) return "0";
		return n.to_string() + "/" + d.to_string();

	}
	friend ostream& operator <<(ostream &os,const bigfraction &obj);

	/*
	 * Arithmetic operator
	 */

	inline void operator*=(bigfraction& other){
		n *=other.n;
		d *=other.d;
		simplify();
	}

	inline void operator*=(bignum other){
		n *=other;
		simplify();
	}


	inline void operator/=(bigfraction& other){
		n *=other.d;
		d *=other.n;
		simplify();
	}

	inline void operator/=(bignum other){
		d *=other;
		simplify();
	}


	inline void operator+=(bigfraction other){
		bignum n1 = n*other.d;
		bignum n2 = other.n * d;
		d = d*other.d;
		n = n1+n2;
		simplify();

	}

	inline void operator+=(bignum other){
		bignum other_n = other * d;
		n += other_n;
		simplify();
	}

	inline void operator-=(bigfraction other){
		bignum n1 = n*other.d;
		bignum n2 = other.n * d;
		d = d*other.d;
		n = n1-n2;
		simplify();

	}

	inline void operator-=(bignum other){
		bignum other_n = other * d;
		n -= other_n;
		simplify();
	}


	inline bigfraction operator*(bigfraction& other)
	{
		bigfraction b(n*other.n, d*other.d);
		return b;
	}

	inline bigfraction operator*(bignum other)
	{
		bigfraction b(n*other, d);
		return b;
	}



	inline bigfraction operator/(bigfraction& other)
	{
		bigfraction b(n*other.d, d*other.n);
		return b;
	}

	inline bigfraction operator/(bignum other)
	{
		bigfraction b(n, d*other);
		return b;
	}



	inline bigfraction operator+(bigfraction& other)
	{
		bignum n1 = n*other.d;
		bignum n2 =other.n*d;
		bignum new_n = n1+n2;
		bignum new_d =  d*other.d;
		bigfraction b(new_n, new_d);
		return b;
	}

	inline bigfraction operator+(bignum other)
	{
		bignum n1 = other*d;
		bignum new_n = n+n1;
		bigfraction b(new_n, d);
		return b;
	}

	inline bigfraction operator-(bigfraction& other)
	{
		bigfraction b((n*other.d)-(other.n*d), d*other.d);
		return b;
	}

	inline bigfraction operator-(bignum other)
	{
		bigfraction b(n-other*d, d);
		return b;
	}

	inline bigfraction operator-()
	{
		bigfraction b(-n, d);
		return b;
	}

	/*
	 * Logical operators
	 */
	inline bool operator==(bigfraction other)
	{
		return n==other.n && d==other.d;
	}

	inline bool operator!=(bigfraction other)
	{
		return n!=other.n || d!=other.d;
	}

	inline bool operator!=(bignum other)
	{
		return d!=1 || n!=other;
	}

	inline bool operator<(bigfraction other)
	{
		bignum n1 = n*other.d;
		bignum n2 = other.n*d;
		return n1<n2;
	}
	inline bool operator<(bignum other)
	{
		bignum n2 = other*d;
		return n<n2;
	}

	inline bool operator<=(bigfraction other)
	{
		bignum n1 = n*other.d;
		bignum n2 = other.n*d;
		return n1<=n2;
	}
	inline bool operator<=(bignum other)
	{
		bignum n2 = other*d;
		return n<=n2;
	}
	inline bool operator>(bigfraction other)
	{
		bignum n1 = n*other.d;
		bignum n2 = other.n*d;
		return n1>n2;
	}
	inline bool operator>(bignum other)
	{
		bignum n2 = other*d;
		return n>n2;
	}
	inline bool operator>=(bigfraction other)
	{
		bignum n1 = n*other.d;
		bignum n2 = other.n*d;
		return n1>=n2;
	}
	inline bool operator>=(bignum other)
	{
		bignum n2 = other*d;
		return n>=n2;
	}

	inline bignum round_down()
	{
		assert(d>=0);
		if(n<0) {
			return (n/d)-1;
		}
		else return n/d;
	}

	inline bignum round_up()
	{
		assert(d>=0);
		if(d==1) return n;
		if(n<0) {
			return n/d;
		}
		else return (n/d+1);
	}


	inline bignum get_numerator()
	{
		return n;
	}
	inline bignum get_denominator()
	{
		return d;
	}

private:
	void simplify()
	{

		if(d<0) {
			d=-d;
			n=-n;
		}
		bignum gcd = n.compute_gcd(d);
		if(gcd == 1 || gcd == 0) return;
		n/=gcd;
		d/=gcd;

	}
};

#endif /* BIGFRACTION_H_ */

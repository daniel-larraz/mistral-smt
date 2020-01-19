/*
 * ArithmeticTerm.h
 *
 *  Created on: Oct 5, 2008
 *      Author: isil
 */

#ifndef ARITHMETICTERM_H_
#define ARITHMETICTERM_H_
#include <boost/serialization/map.hpp>
#include "Term.h"



Term* _make_ap(const map<Term*, long int>& elems, long int c);

class ArithmeticTerm: public Term {
	friend class boost::serialization::access;
private:
	map<Term*, long int > elems;
	long int constant;
	int elem_gcd;
	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<Term>(*this);
		ar & elems;
		ar & constant;
		ar & elem_gcd;
	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<Term>(*this);
		map<Term*, long int > cur_elems;
		ar & cur_elems;
		ar & constant;
		ar & elem_gcd;
		map<Term*, long int >::iterator it = cur_elems.begin();
		for(; it!= cur_elems.end(); it++)
		{
			Term* t = it->first;
			t = get_term_nodelete(t);
			elems[t]+=it->second;
		}
		compute_hash_code();

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
protected:
	ArithmeticTerm(){}
public:
	ArithmeticTerm(const map<Term*, long int>& elems,long int constant);
protected:
	/**
	 * c1*t1 + c2*t2
	 */
	ArithmeticTerm(Term* t1, long int c1, Term* t2, long int c2);

	/**
	 * t * c
	 */
	ArithmeticTerm(Term* t, long int c);
	virtual ~ArithmeticTerm();
public:
	static Term* make(const map<Term*, long int>& elems,long int constant)
	{
		ArithmeticTerm* at;
#ifdef COMPASS
		Term* t = _make_ap(elems, constant);
		if(t->get_term_type() != ARITHMETIC_TERM) return t;
		at = (ArithmeticTerm*) t;
#endif
#ifndef COMPASS
		at = _make(elems, constant);
#endif

		return canonicalize(at);
	}
	static Term* make(const map<Term*, long int>& elems)
	{
		ArithmeticTerm* at;
#ifdef COMPASS
		Term* t = _make_ap(elems, 0);
		if(t->get_term_type() != ARITHMETIC_TERM) return t;
		at = (ArithmeticTerm*) t;
#endif
#ifndef COMPASS
		at = _make(elems, 0);
#endif

		return canonicalize(at);
	}



	static ArithmeticTerm* _make(const map<Term*, long int>& elems,long int constant);
	inline const map<Term*, long int>& get_elems()
	{
		return elems;
	}
	inline long int get_constant()
	{
		return constant;
	}
	virtual bool operator==(const Term& other);
	virtual string to_string();
	virtual Term* substitute(map<Term*, Term*>& subs);
	long int get_gcd(bool include_constant);
	/*
	 * Are the coefficients of all elements negative?
	 */
	bool has_only_negative_coefficients();

	/*
	 * Base of an arithmetic term is the same arithmetic term, but constant is 0.
	 */
	Term* get_base();
private:
	void compute_hash_code();
	void add_elem(Term* t, long int constant);
	static Term* canonicalize(ArithmeticTerm* at);

};


#endif /* ARITHMETICTERM_H_ */

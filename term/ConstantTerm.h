/*
 * ConstantTerm.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef CONSTANTTERM_H_
#define CONSTANTTERM_H_
#include "Term.h"
#include <string>
using namespace std;



Term* _make_ap(long int c);

class ConstantTerm:public Term {
	friend class boost::serialization::access;
private:
	long int c;
	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<Term>(*this);
		ar & c;
	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<Term>(*this);
		ar & c;
		hash_c = c*47;

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
protected:
	ConstantTerm(){}
public:
	ConstantTerm(long int c);

	virtual ~ConstantTerm();
public:
	static Term* make(long int c)
	{
#ifdef COMPASS
		return Term::get_term(_make_ap(c));
#endif
#ifndef COMPASS
		return _make_term(c);
#endif
	}
	virtual bool operator==(const Term& other);
	virtual string to_string();
	virtual Term* substitute(map<Term*, Term*>& subs);
	inline long int get_constant()
	{
		return c;
	}
private:

	static Term* _make_term(long int c);

};





#endif /* CONSTANTTERM_H_ */

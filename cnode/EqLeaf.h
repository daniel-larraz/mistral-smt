/*
 * EqLeaf.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef EQLEAF_H_
#define EQLEAF_H_
#include "CNode.h"
#include "Leaf.h"
#include <string>
#include "term.h"
using namespace std;

class VarMap;
class Term;

class EqLeaf:public Leaf{
	friend class boost::serialization::access;
private:
	Term* lhs;
	Term* rhs;
	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<Leaf>(*this);
		ar & lhs;
		ar & rhs;
	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<Leaf>(*this);
		ar & lhs;
		ar & rhs;

		lhs = Term::get_term_nodelete(lhs);
		rhs = Term::get_term_nodelete(rhs);
		/*if(lhs > rhs)
		{
			Term* t = lhs;
			lhs = rhs;
			rhs = t;
		}*/

		compute_hash_code();

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
	EqLeaf(){}
protected:
	EqLeaf(Term* lhs, Term* rhs);
	virtual ~EqLeaf();

public:
	static CNode* make(Term* lhs, Term* rhs);
	virtual bool operator==(const CNode& other);
	virtual string to_string();
	virtual CNode* substitute(map<Term*, Term*>& subs);
	Term* get_lhs();
	Term* get_rhs();


private:
	void compute_hash_code();
};



#endif /* EQLEAF_H_ */

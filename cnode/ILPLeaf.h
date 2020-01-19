/*
 * ILPLeaf.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef ILPLEAF_H_
#define ILPLEAF_H_
#include "CNode.h"
#include "Leaf.h"
#include <vector>
#include <set>
#include<string>
#include <map>
#include <boost/serialization/map.hpp>
#include "Term.h"
using namespace std;

enum ilp_leaf_type{
	ILP_EQ,
	ILP_LEQ,
	ILP_LT,
	ILP_GEQ,
	ILP_GT
};

class VarMap;
class Term;
class ArithmeticTerm;


class CompareILPLeaf:public binary_function<pair<Term*, int> , pair<Term*, int>, bool> {
public:
	bool operator()(const pair<Term*, int> b1, const pair<Term*, int> b2) const;
};

class ILPLeaf: public Leaf {
	friend class boost::serialization::access;
private:
	/*
	 * We maintain the invariant that the terms nested inside an ILPLeaf
	 * are only Variable or Function terms, but not constants or
	 * arithmetic terms.
	 */
	map<Term*, long int> elems;
	long int constant;
	ilp_leaf_type kind;
	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<Leaf>(*this);
		ar & elems;
		ar & constant;
		ar & kind;
	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		map<Term*, long int> cur_elems;
		ar & boost::serialization::base_object<Leaf>(*this);
		ar & cur_elems;
		ar & constant;
		ar & kind;
		map<Term*, long int>::iterator it = cur_elems.begin();
		for(; it != cur_elems.end(); it++)
		{
			Term* cur = it->first;
			cur = Term::get_term_nodelete(cur);
			elems[cur]+=it->second;
		}
		compute_hash_code();

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
protected:
	ILPLeaf(ilp_leaf_type kind, const map<Term*, long int> & elems,
			long int constant);


public:
	ILPLeaf(){}
	virtual ~ILPLeaf();
	static CNode* make(ilp_leaf_type kind, const map<Term*, long int>& elems,
			long int constant);
	static CNode* make(Term* t1, Term* t2, ilp_leaf_type kind);

	virtual bool operator==(const CNode& other);
	virtual string to_string();
	static string ilp_leaf_type_to_string(ilp_leaf_type t);

	inline ilp_leaf_type get_operator()
	{
		return kind;
	}
	inline const map<Term*, long int >& get_elems()
	{
		return elems;
	}
	inline long int get_constant()
	{
		return constant;
	}
	long get_coefficient(Term* t);
	bool contains_elem(Term* t);
	CNode* remove_elem(Term* t);
	CNode* negate(bool remove_all_negations = false);
	virtual CNode* substitute(map<Term*, Term*>& subs);
	CNode* multiply(long int factor);
	CNode* add(ILPLeaf* other);
	string pretty_print_ilp(bool neg);
	virtual CNode*  divide(long int c, Term* t);
private:
	void compute_hash_code();
	void add_term(Term* t, long int coef);
	static CNode* _make(ilp_leaf_type kind, const map<Term*, long int>& elems,
					long int constant, bool force_canonical);
};



#endif /* ILPLEAF_H_ */

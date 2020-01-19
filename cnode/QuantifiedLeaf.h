/*
 * QuantifiedLeaf.h
 *
 *  Created on: Sep 12, 2008
 *      Author: isil
 */

#ifndef QUANTIFIEDLEAF_H_
#define QUANTIFIEDLEAF_H_

#include "Leaf.h"
#include <set>
#include <vector>
#include <iostream>
#include "VarMap.h"
using namespace std;

/*
 * A quantified leaf must be a universally quantified formula of the
 * following form:
 *
 * Ai,..j. F(i,..j) -> G(i,,j)
 *
 * where we call F the index guard and G the value guard.
 * (Terminology is taken from Aaron Bradley.)
 *
 * The index guard restricts use of universally quantified
 * variables. In particular, if i and j are universally
 * quantified variables, the index guard does not
 * allow anything other than i=j and i<=j; otherwise
 * it becomes undecidable. Function symbols
 * are also not allowed in the index guard.
 */
class QuantifiedLeaf: public Leaf {
	friend class boost::serialization::access;
	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<Leaf>(*this);
		vector<pair<string, int> > qvars;
		set<int>::iterator it = quantified_vars.begin();
		for(; it!= quantified_vars.end(); it++)
		{
			int attrib = CNode::get_varmap().get_attrib(*it);
			string name = CNode::get_varmap().get_name(*it);
			pair<string, int> key(name, attrib);
			qvars.push_back(key);
		}
		ar & qvars;
		ar & index_guard;
		ar & value_guard;

	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<Leaf>(*this);
		vector<pair<string, int> > qvars;
		ar & qvars;
		ar & index_guard;
		ar & value_guard;
		vector<pair<string, int> >::iterator it = qvars.begin();
		for(; it!= qvars.end(); it++)
		{
			string name = it->first;
			int attrib = it->second;
			int id = CNode::get_varmap().get_id(name) | attrib;
			quantified_vars.insert(id);
		}
		hash_c = index_guard->hash_code()*47 + value_guard->hash_code()*7;

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
private:
	set<int> quantified_vars;
	CNode* index_guard;
	CNode* value_guard;

protected:
	QuantifiedLeaf(set<int>& q_vars, CNode* index_guard, CNode* value_guard);
public:
	QuantifiedLeaf(){};
	virtual ~QuantifiedLeaf();
	static CNode* make(set<int>& q_vars, CNode* index_guard, CNode* value_guard);
	set<int>& get_quantified_vars();
	CNode* get_index_guard();
	CNode* get_value_guard();
	virtual bool operator==(const CNode& other);
	virtual string to_string();
	virtual CNode* substitute(map<Term*, Term*>& subs);

};

#endif /* QUANTIFIEDLEAF_H_ */

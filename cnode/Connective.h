/*
 * Connective.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef CONNECTIVE_H_
#define CONNECTIVE_H_
#include "CNode.h"
#include <vector>
#include <string>
#include <set>
#include <boost/serialization/set.hpp>
using namespace std;

class VarMap;

class Connective: public CNode {
	friend class ILPLeaf;
	friend class CNode;
	friend class boost::serialization::access;
	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<CNode>(*this);
		ar & operands;
		ar & size;
	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<CNode>(*this);
		ar & operands;
		ar & size;
		compute_hash_code();
	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
private:

	set<CNode*> operands;
	int size; //for caching result of get_size()



private:
	Connective(){}
	Connective(cnode_type connective_type, const set<CNode*>& ops);
	Connective(CNode* op); // for the not case
	virtual ~Connective();
	static CNode* _make_and(const set<CNode*>& ops, bool simplify = true);

public:
	inline static CNode* make_and(const set<CNode*>& ops, bool simplify = true)
	{
		return _make_and(ops, simplify);
	}

	static CNode* make_or(const set<CNode*>& ops, bool simplify = true);
	static CNode* make_implies(CNode* p, CNode* a); // p=> a
	static CNode* make_not(CNode* op);
	static CNode* make(cnode_type connective_type, const set<CNode*>& ops);
	static CNode* make(cnode_type connective_type, CNode* op1, CNode* op2);
	virtual bool operator==(const CNode& other);
	virtual string to_string();
	const set<CNode*>& get_operands();
	virtual CNode* substitute(map<Term*, Term*>& subs);


private:
	string connective_to_string();
	void compute_hash_code();



};


#endif /* CONNECTIVE_H_ */

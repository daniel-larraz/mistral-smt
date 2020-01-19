/*
 * True.h
 *
 *  Created on: Jan 22, 2009
 *      Author: tdillig
 */

#ifndef TRUE_H_
#define TRUE_H_




#include "CNode.h"

class True: public CNode {
	friend class CNode;
	friend class boost::serialization::access;
	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<CNode>(*this);
	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<CNode>(*this);
		hash_c = ~0;

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
protected:
	True();
	virtual ~True();
public:
	static CNode* make();
	virtual bool operator==(const CNode& other);
	virtual string to_string();
	virtual CNode* substitute(map<Term*, Term*>& subs);
};



#endif /* TRUE_H_ */

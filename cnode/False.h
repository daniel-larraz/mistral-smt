/*
 * False.h
 *
 *  Created on: Jan 22, 2009
 *      Author: tdillig
 */

#ifndef FALSE_H_
#define FALSE_H_

#include "CNode.h"

class False:public CNode {
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
		hash_c = 0;

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
protected:
	friend class CNode;
	False();
	virtual ~False();
public:
	static CNode* make();
	virtual bool operator==(const CNode& other);
	virtual CNode* substitute(map<Term*, Term*>& subs);
	virtual string to_string();

};



#endif /* FALSE_H_ */

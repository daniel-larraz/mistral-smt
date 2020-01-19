/*
 * Leaf.h
 *
 *  Created on: Sep 2, 2008
 *      Author: tdillig
 */

#ifndef LEAF_H_
#define LEAF_H_

#include "CNode.h"

class VarMap;

class Leaf:public CNode {
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
	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
public:
	Leaf();
	virtual string to_string()=0;
	virtual ~Leaf();

};



#endif /* LEAF_H_ */

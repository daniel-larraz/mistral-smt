/*
 * BooleanVar.h
 *
 *  Created on: Jul 25, 2009
 *      Author: tdillig
 */

#ifndef BOOLEANVAR_H_
#define BOOLEANVAR_H_

#include "Leaf.h"

class EqLeaf;

class BooleanVar: public Leaf {
	friend class CNode;
	friend class boost::serialization::access;
private:
	unsigned int id;
	static unsigned int next_id;
	static map<unsigned int, string> names;
	static map<string, unsigned int> names_rev;

	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<CNode>(*this);
		string name = "";
		if(names.count(id) > 0)
			name = names[id];
		ar & name;

	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<CNode>(*this);
		string name;
		ar & name;
		if(name != "")
		{
			if(names_rev.count(name) > 0)
			{
				id = names_rev[name];
				//recompute hash code since id changed
				this->hash_c = 30673 + 7*id;
			}

			else
			{
				names[id] = name;
				names_rev[name] = id;

			}

		}

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
protected:
	BooleanVar();
	BooleanVar(const string & name);
	virtual ~BooleanVar();
	static void clear();
public:
	static BooleanVar* make();
	static BooleanVar* make(const string & name);
	unsigned int get_id() const;
	virtual bool operator==(const CNode& other);
	virtual string to_string();
	string get_name();
	virtual CNode* substitute(map<Term*, Term*>& subs);

	/*
	 * Translates boolean var x to x=1, and !x to x!=1.
	 */
	EqLeaf* to_eqleaf() const;

};

#endif /* BOOLEANVAR_H_ */

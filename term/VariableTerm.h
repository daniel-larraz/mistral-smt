/*
 * VariableTerm.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef VARIABLETERM_H_
#define VARIABLETERM_H_

#include "Term.h"

Term* _make_ap(const string& name);

class VariableTerm: public Term {

	friend class boost::serialization::access;
private:
	int var_id;

	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<Term>(*this);
		const string& name = CNode::get_varmap().get_name(var_id);
		ar & name;
		int attrib = get_id_attribute();
		ar & attrib;
	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<Term>(*this);
		string name;
		ar & name;
		var_id = CNode::get_varmap().get_id(name);
		int attrib;
		ar & attrib;
		var_id |= attrib;
		hash_c = (this->var_id+2)* 65537;

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()

protected:
	VariableTerm()
	{

	}
public:
	VariableTerm(int var_id, int attribute = 0);
	virtual ~VariableTerm();
public:
	static Term* make(int id);
	static Term* make(string name);
	virtual bool operator==(const Term& other);
	virtual string to_string();
	inline int get_id_attribute() const
	{
		int mask = (1 << NUM_BITS_RESERVED)-1;
		int res = var_id & mask;
		return res;
	}
	inline int get_var_id()
	{
		return var_id;
	}
	string get_name();
	virtual Term* substitute(map<Term*, Term*>& subs);
};





#endif /* VARIABLETERM_H_ */

/*
 * FunctionTerm.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef FUNCTIONTERM_H_
#define FUNCTIONTERM_H_

#include "Term.h"
#include <boost/serialization/vector.hpp>
#include <string>
using namespace std;

Term* _make_ap(const string & name, vector<Term*>& args, bool invertible);


class FunctionTerm: public Term {
	friend class Address;
	friend class StringLiteral;
	friend class ProgramFunction;
	friend class TypeConstant;
	friend class boost::serialization::access;
public:
	int fun_id;
	vector<Term*> args;

	// Is this function invertible?
	bool invertible;

	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<Term>(*this);
		const string& name = CNode::get_varmap().get_name(fun_id);
		ar & name;
		int attrib = get_id_attribute();
		ar & attrib;
		ar & args;
		ar & invertible;
	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<Term>(*this);
		string name;
		ar & name;
		int attrib;
		ar & attrib;
		fun_id = CNode::get_varmap().get_id(name);
		fun_id |= attrib;
		ar & args;
		ar & invertible;
		for(unsigned int i=0; i < args.size(); i++)
		{
			args[i] = Term::get_term_nodelete(args[i]);
		}
		compute_hash_code();

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
public:
	FunctionTerm(int id, const vector<Term*>& args, bool invertible,
			int attribute = 0);
protected:
	FunctionTerm(){}

	FunctionTerm(int id, Term* arg, bool invertible, int attribute = 0);
	FunctionTerm(int id, Term* arg1, Term* arg2, bool invertible,
			int attribute = 0);
	virtual ~FunctionTerm();
	void compute_hash_code();
public:
	static Term* make(int id, vector<Term*>& args, bool invertible);
	static Term* make(string name, vector<Term*>& args, bool invertible);
	virtual bool operator==(const Term& other);
	virtual string to_string();
	inline int get_id() const
	{
		return fun_id;
	}
	inline bool is_invertible()
	{
		return invertible;
	}
	string get_name();
	virtual Term* substitute(map<Term*, Term*>& subs);
	inline const vector<Term*>& get_args()
	{
		return args;
	}
	inline int get_id_attribute() const
	{
		int mask = (1 << NUM_BITS_RESERVED)-1;
		int res = fun_id & mask;
		return res;
	}

};


#endif /* FUNCTIONTERM_H_ */

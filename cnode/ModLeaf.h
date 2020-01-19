/*
 * ModLeaf.h
 *
 *  Created on: Feb 12, 2009
 *      Author: tdillig
 */

#ifndef MODLEAF_H_
#define MODLEAF_H_

#include "Leaf.h"
#include "Term.h"

class ILPLeaf;
class VariableTerm;

class ModLeaf:public Leaf {
	friend class boost::serialization::access;
private:
	Term* t;
	long int k;
	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{
		ar & boost::serialization::base_object<Leaf>(*this);
		ar & t;
		ar & k;
	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & boost::serialization::base_object<Leaf>(*this);
		ar & t;
		ar & k;
		t = Term::get_term_nodelete(t);
		hash_c = t->hash_code();
		hash_c = (hash_c*79) + k;

	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()
protected:
	// t%k=0
	ModLeaf(Term* t, long int k);

public:
	ModLeaf(){};
	virtual ~ModLeaf();
	static CNode* make(Term* t, long int k, Term* r);
	static CNode* make(Term* t, long int k, long int r);
	static CNode* make(Term* t, long int k);
	Term* get_term();
	long int get_mod_constant();
	/*
	 * Converts this mod constraint into a set of ILP leaves
	 * First arg: resulting set of ilp leaves
	 * Second arg: Indicates phase of the mod leaf
	 * Third arg: id of the temp variable to introduce
	 */
	void to_ilp(set<ILPLeaf*>& ilp_leaves, bool pos, int temp_id);
	virtual bool operator==(const CNode& other);
	virtual CNode* substitute(map<Term*, Term*>& subs);
	virtual string to_string();
	VariableTerm* get_ilp_temp(int temp_id);
	pair<VariableTerm*, VariableTerm*>
		get_ilp_temps(int temp_id); // for negated leaves
};

#endif /* MODLEAF_H_ */

/*
 * Term.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef TERM_H_
#define TERM_H_

#include <string>
#include "VarMap.h"
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include "Leaf.h"
#include "Term.h"
#include "util.h"
#include "term-shared.h"

#include <boost/serialization/list.hpp>
#include <boost/serialization/string.hpp>
#include <boost/serialization/version.hpp>
#include <boost/serialization/split_member.hpp>
#include <boost/serialization/shared_ptr.hpp>
#include <boost/serialization/base_object.hpp>
#include <boost/serialization/export.hpp>
#include <sstream>

using namespace std;
enum term_type{
	CONSTANT_TERM,
	VARIABLE_TERM,
	FUNCTION_TERM,
	ARITHMETIC_TERM
};

class Term;
class Constraint;

namespace std {

template <>
struct hash<Term*> {
        size_t operator() (const Term* const & x) const;
};

struct term_eq
{
  bool operator()(const Term* l1, const Term* l2) const;
};

}
using namespace __gnu_cxx;

static set<Term*> delete_terms;

enum term_attribute_type
{
	TERM_ATTRIB_NO_ATTRIB,
	TERM_ATTRIB_GEQZ, // >=0
	TERM_ATTRIB_GTZ // >0
};

/*
 * Abstract class that represents constant, variable or
 * function terms. All terms must be shared through the
 * get_term(t) function in LeafMap.h
 */
class Term {
	friend class boost::serialization::access;
	friend class CNode;
protected:
public:
	size_t hash_c;
	term_type type;

	/*
	 * A restriction on the values a term can have.
	 * For instance, for a term t associated with an unsigned program variable,
	 * there would be t >= 0 attribute.
	 */
	term_attribute_type attribute;

	/*
	 * This is zero if this term is not extended by a subclass.
	 */
	int specialization_type;
	static unordered_set<Term*, std::hash<Term*>, term_eq> terms;


	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{

		ar & type;
		ar & specialization_type;
		ar & attribute;


	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		ar & type;
		ar & specialization_type;
		ar & attribute;
		hash_c = 0;


	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()


protected:
	inline Term()
	{
		representative = NULL;
		this->attribute = TERM_ATTRIB_NO_ATTRIB;
		this->specialization_type = 0;

	}
public:
	static Term* get_term(Term* t);
	static set<Term*> to_delete;
	static Term* get_term_nodelete(Term* t);


	static Term* uniquify_term(Term* t);

protected:
	static void clear();
public:

	static void delete_loaded_terms();

	virtual bool operator==(const Term& other) = 0;
	virtual string to_string()=0;
	inline term_type get_term_type()
	{
		return type;
	}
	inline bool is_specialized()
	{
		return this->specialization_type != 0;
	}

	inline int get_specialization()
	{
		return specialization_type;
	}
	inline term_attribute_type get_attribute()
	{
		return attribute;
	}
	inline string get_attribute_string()
	{
		if(attribute == TERM_ATTRIB_NO_ATTRIB) return "";
		else if(attribute == TERM_ATTRIB_GEQZ) return to_string() + ">= 0";
		else if(attribute == TERM_ATTRIB_GTZ) return to_string() + "> 0";
		else assert(false);


	}

	/*
	 * Returns the attributes on this terms as well
	 * as on any nested subterms.
	 */
	void get_attributes(set<CNode*> & attributes);

	void set_attribute(term_attribute_type ta);

	virtual ~Term();
	inline size_t hash_code()
	{
		return hash_c;
	}
	/*
	 * Returns ids of all vars nested inside this term
	 */
	void get_nested_vars(set<int>& vars);
	void get_nested_terms(set<Term*>& terms, bool include_function_subterms = true,
			bool include_constants = true);
	virtual Term* substitute(map<Term*, Term*>& subs) = 0;

	Term* substitute(Term* (*sub_func)(Term* t));

	virtual Term* substitute(Term* (*sub_func)(Term* t, void* data), void* my_data);

	/*
	 * Clears all the (nested) representative fields used for Fast Union Find.
	 */
	void clear_representatives();

	/*
	 * Returns any nested old_terms with new_term.
	 */
	Term* replace_term(Term* old_term, Term* new_term);

	/*
	 * Returns the set of variable names used in this term.
	 */
	void get_vars(set<string>& vars);
	void get_vars(set<int>& vars);
	void get_vars(set<Term*>& vars);

	bool contains_term(Term* t);
	bool contains_term(set<Term*>& terms);
	bool contains_var(int var_id);

	void get_all_fun_ids(set<int> & ids);

	void get_all_arguments(int fun_id, int arg_num, set<Term*> & args);
	void get_all_first_arguments(set<int>& fn_ids, map<int, set<Term*> >&
			fn_id_to_first_arg);

	Term* replace_argument(int fun_id, int arg_num, Term* replacement);

	Term* replace_first_argument(map<int, Term*>&  fun_id_to_replacements);


	/*
	 * Does this term and the other term share any subterms?
	 */
	bool shares_subterms(Term* other);

	/*
	 * Does this term contains any nested variable terms?
	 */
	bool contains_var();

	/*
	 * Returns a term where all occurences of old_var_id are
	 * replaced by new_var_id.
	 */
	Term* rename_variable(int old_var_id, int new_var_id);
	Term* rename_variables(map<int, int>& replacements);

	/*
	 * Flips the sign of this term -> x becomes -x etc.
	 */
	Term* flip_sign();

	/*
	 * Multiplies the term by the specified constant
	 */
	Term* multiply(long int factor);

	Term* add(long int constant);
	Term* add(Term* t);
	Term* subtract(Term* t);

	Term* evalute_term(map<Term*, SatValue>& assignments);

	Term* multiply(Term* t);





public:
	Term* representative;

};



#endif /* TERM_H_ */

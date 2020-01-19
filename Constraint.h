/*
 * Constraint.h
 *
 *  Created on: Sep 16, 2008
 *  Author: isil
 */

#ifndef CONSTRAINT_H_
#define CONSTRAINT_H_

#include "ConstraintSolver.h"
#include "Term.h"

#include <set>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <string>
#include <functional>

using namespace std;

class CNode;

class Constraint {
	friend class boost::serialization::access;
private:
	friend struct std::hash<Constraint>;
	friend class ConstraintSolver;
	friend class Term;
	int id;

	template<class Archive>
	void save(Archive & ar, const unsigned int version) const
	{

		CNode* nc = cs.get_nc((int&)id);
		CNode* sc = cs.get_sc((int&)id);
		ar & nc;
		ar & sc;


	}
	template<class Archive>
	void load(Archive & ar, const unsigned int version)
	{
		CNode* nc;
		CNode* sc;
		ar & nc;
		ar & sc;
		nc = CNode::uniquify_cnode(nc);
		sc = CNode::uniquify_cnode(sc);
		pair<CNode*, CNode*> key(nc, sc);
		id = cs.get_id(key);


	}
	BOOST_SERIALIZATION_SPLIT_MEMBER()

	void get_msa_assignment(set<VariableTerm*>&
			msa_vars, map<Term*, SatValue>& msa);



public:
	static ConstraintSolver cs;
	Constraint();
	/**
	 * Constructs boolean constant true/false
	 */
	Constraint(bool val);
	Constraint(const Constraint& nc, const Constraint& sc);
	Constraint(Term* t1, Term* t2, atom_op_type op);

	Constraint(const Constraint & other);
	Constraint(string s);
	Constraint(const char* s);

	Constraint(CNode* n);

	static void set_geqz_attribute(Term* t);
	static void set_gtz_attribute(Term* t);

	bool sat() const;
	bool unsat() const;
	bool valid() const;
	bool equivalent(Constraint other) const;


	/*
	 * These methods do not simplify.
	 */
	bool sat_discard() const;
	bool unsat_discard() const;
	bool valid_discard() const;


	Constraint nc() const;
	Constraint sc() const;

	int nc_size() const;
	int sc_size() const;

	/*
	 * Checks if the constraint is literally the constant true/false
	 */
	bool is_true() const;
	bool is_false() const;

	static void clear();



	Constraint operator&(const Constraint & other) const;
	Constraint operator|(const Constraint & other) const;

	/*
	 * Find a constraint C such that b&C=>this and C is consistent with everything
	 * in the consistency_constraints set.
	 */
	Constraint abduce(Constraint  b,
			const set<Constraint> & consistency_constraints,
			map<Term*, int>& costs) const;

	Constraint abduce(Constraint  b,
			const set<Constraint> & consistency_constraints) const;

	Constraint abduce(Constraint  b) const;

	void operator&=(const Constraint & other);
	void operator|=(const Constraint & other);


	Constraint operator!() const ;

	void operator=(const Constraint &  other);
	bool operator==(const Constraint &  other) const;
	bool operator!=(const Constraint &  other) const;
	bool implies(const Constraint & other) const;
	bool operator<(const Constraint  & other) const;

	/*
	 * Returns true if NC==SC, i.e. the current constraint has
	 * no imprecision.
	 */
	bool is_precise() const;

	/*
	 * Functions for eliminating existentially quantified variables
	 */
	void eliminate_evar(VariableTerm* var);
	void eliminate_evars(set<VariableTerm*>& vars);

	/*
	 * Functions for eliminating universally quantified variables
	 */
	void eliminate_uvar(VariableTerm* var);
	void eliminate_uvars(set<VariableTerm*>& vars);

	/*
	 * Does this constraint contain a <, <=, >, >=?
	 */
	bool contains_inequality();

	void fresh_id();


	/*
	 * Functions for eliminating free variables
	 */
	void eliminate_free_var(VariableTerm* var);
	void eliminate_free_vars(set<VariableTerm*>& vars);


	/*
	 * Yields the set of all terms used in this constraint
	 */
	void get_terms(set<Term*>& terms, bool include_nested_terms);

	/*
	 * Methods to manage background knowledge, i.e.
	 * assumptions on the left side of the turnstile.
	 */
	static void add_ground_axiom(Constraint key, Constraint c);
	static void add_quantified_axiom(Constraint key, Constraint c);
	static void set_background_knowledge(Constraint c);

	static void replace_term_in_axioms(Term* old_t, Term* new_t);



	static string background_knowledge_to_string();
	static Constraint get_general_background();


	/*
	 * The return value R is a term t' such that (t=t') is
	 * implied by this constraint. Returns NULL if no
	 * such equality is implied by the constraint.
	 */
	Term* find_equality(Term* t) const;

	void find_equalities(Term* t, set<Term*> & eqs) const;


	void replace_term(Term* to_replace, Term* replacement);
	void replace_terms(map<Term*, Term*> & replacements);
	void replace_constraint(Constraint to_replace, Constraint replacement);

	void replace_terms(Term* (*sub_func)(Term* t, void* data), void* my_data)
	{
		c_id old_id = id;
		id = cs.replace_terms(old_id, sub_func, my_data);
	}

	void get_free_variables(set<Term*>& vars);
	bool contains_term(Term* var);
	// Does this constraint contain any of these terms?
	bool contains_term(set<Term*>& terms);



	static void clear_background();

	/*
	 * If this method is called, background knowledge is not
	 * taken into account when determining satisfiability/validity.
	 */
	static void disable_background();

	/*
	 * If this constraint contains artificial variables used to enforce,
	 * for example, existence and uniqueness, this function
	 * eliminates these fake variables and replaces them by
	 * what they stand for.
	 */
	void propagate_background();

	/*
	 * Assume that c holds, i.e. set all leaves from c that occur inside you
	 * to true.
	 */
	void assume(Constraint c);
	/*
	 * Are t1 and t2 related by an equality in this constraint?
	 */
	bool has_equality_relation(Term* t1, Term* t2);


	void get_disjunctive_equalities(Term* var,
			map<Term*, Constraint> & equalities);

	void divide(long int c, Term* t);


	/*
	 * Gives a satisfying assignment to all terms in the constraint.
	 * e.g. <drf(a), 3>,...
	 */
	bool get_assignment(set<pair<string, string> > & assignments);
	bool get_assignment(map<Term*, SatValue> & assignments);


	void replace_terms(Term* (*sub_func)(Term* t));



	string to_string() const;
	string debug_string();

	int msa(map<Term*, SatValue>& msa);
	int  msa(set<VariableTerm*> & msa) const;
	int msa(set<VariableTerm*> & msa, set<Constraint>& bg) const;
	int msa(map<Term*, SatValue> & msa, set<Constraint>& bg);
	int  msa(set<VariableTerm*> & msa,
			map<VariableTerm*, int>& costs) const;
	int  msa(set<VariableTerm*> & msa, set<Constraint>& bg,
			map<VariableTerm*, int>& costs) const;
	int  msa(map<Term*, SatValue> & msa, set<Constraint>& bg,
			map<VariableTerm*, int>& costs);

	pair<CNode*, CNode*> get_cnodes();


	void to_dnf(set<Constraint> & dnf);
	void to_cnf(set<Constraint> & cnf);

};

ostream& operator <<(ostream &os,const Constraint &_obj);

namespace std {
template <>
struct hash<Constraint> {

        size_t operator() (const Constraint & x) const {
        	Constraint & c = (Constraint &)x;
                return hash<int>()(c.id);
        }
};


}


#endif /* CONSTRAINT_H_ */

/*
 * Constraint.cpp
 *
 *  Created on: Sep 16, 2008
 *      Author: isil
 */
#include "ConstraintSolver.h"
#include "Constraint.h"
#include "assert.h"
#include "term.h"

ConstraintSolver Constraint::cs;

Constraint::Constraint()
{
	id = cs.get_true_constraint();
}

void Constraint::set_geqz_attribute(Term* t)
{
	t->set_attribute(TERM_ATTRIB_GEQZ);
}

void Constraint::set_gtz_attribute(Term* t)
{
	t->set_attribute(TERM_ATTRIB_GTZ);
}  
 



/*
 * Checks if the constraint is literally the constant true/false
 */
bool Constraint::is_true() const
{
	return id == cs.get_true_constraint();
}
bool Constraint::is_false() const
{
	return id == cs.get_false_constraint();
}

Constraint::Constraint(bool val)
{
	if(val)
		id = cs.get_true_constraint();
	else id = cs.get_false_constraint();
}

Constraint::Constraint(CNode* n)
{
	id = cs.get_constraint_from_cnode(n);
}


Constraint::Constraint(const Constraint& nc, const Constraint& sc)
{
	id = cs.make_ncsc(nc.id, sc.id);
}

Constraint::Constraint(Term* t1, Term* t2, atom_op_type op)
{
	id = cs.get_atom(t1, t2, op);
}



Constraint::Constraint(const Constraint & other)
{
	id = other.id;
}

Constraint::Constraint(const char* s)
{
	string ss = s;
	id = cs.get_constraint_from_string(ss);
}

Constraint::Constraint(string s)
{
	id = cs.get_constraint_from_string(s);
}


bool Constraint::sat() const
{

	return cs.is_sat((c_id &)id);
}

bool Constraint::unsat() const
{
	return !cs.is_sat((c_id &)id);
}

bool Constraint::valid() const
{
	return cs.is_valid(id);
}

bool Constraint::sat_discard() const
{
	return cs.is_sat_discard((c_id &)id);
}
bool Constraint::unsat_discard() const
{
	return !cs.is_sat_discard((c_id &)id);
}
bool Constraint::valid_discard() const
{
	return cs.is_valid_discard(id);
}

bool Constraint::implies(const Constraint & other) const
{
	return cs.implies(this->id, other.id);
}



Constraint Constraint::operator&(const Constraint & other) const
{
	Constraint new_c;
	new_c.id = cs.and_constraint(this->id, other.id);
	return new_c;
}

Constraint Constraint::operator|(const Constraint & other) const
{
	Constraint new_c;
	new_c.id = cs.or_constraint(this->id, other.id);
	return new_c;
}

Constraint Constraint::abduce(Constraint  b,
		const set<Constraint> & consistency_constraints) const
{
	map<Term*, int> costs;
	return this->abduce(b, consistency_constraints, costs);
}

Constraint Constraint::abduce(Constraint  b) const
{
	map<Term*, int> costs;
	set<Constraint>  empty;
	return this->abduce(b, empty, costs);
}

Constraint Constraint::abduce(Constraint _b,
		const set<Constraint> & consistency_constraints,
		 map<Term*, int>& orig_costs) const
{

	set<Term*> t;
	((Constraint*)this)->get_terms(t, false);
	_b.get_terms(t, false);
	for(set<Constraint>::const_iterator  it = consistency_constraints.begin();
			it != consistency_constraints.end(); it++)
	{
		Constraint c = *it;
		c.get_terms(t, false);
	}

	map<Term*, Term*> sub;
	map<Term*, Term*> rev_sub;
	map<VariableTerm*, int> costs;
	int c = 0;
	for(set<Term*>::iterator it= t.begin(); it != t.end(); it++, c++) {
		Term* t = *it;
		if(t->get_term_type()!= FUNCTION_TERM){
			if(t->get_term_type() == VARIABLE_TERM && orig_costs.count(t) > 0) {
				costs[static_cast<VariableTerm*>(t)] = orig_costs[t];
			}
			continue;
		}
		Term* fresh = VariableTerm::make("__tmp@" + int_to_string(c));
		sub[t] = fresh;
		rev_sub[fresh] = t;
		if(orig_costs.count(t) >0)
			costs[static_cast<VariableTerm*>(fresh)] = orig_costs[t];

	}


	Constraint rhs = this->sc();
	Constraint lhs = _b.nc();



	rhs.replace_terms(sub);
	lhs.replace_terms(sub);
	Constraint imp = (!lhs) | rhs;







	set<Constraint> cc;
	for(set<Constraint>::const_iterator  it = consistency_constraints.begin();
				it != consistency_constraints.end(); it++)
	{
		Constraint c = *it;
		c.replace_terms(sub);
		cc.insert(c);

	}

	cc.insert(lhs);



	//cout << "GETTING MSA FOR: " << imp << endl;

	set<VariableTerm*> msa_set;
	imp.msa(msa_set, cc, costs);

	//cout << "Number of vars in MSA: " << msa_set.size() << endl;

	set<Term*> vars;
	imp.get_free_variables(vars);
	set<Term*>::iterator it = vars.begin();
	for(; it != vars.end(); it++) {
		Term* t = *it;
		assert(t->get_term_type() == VARIABLE_TERM);
		VariableTerm* vt = static_cast<VariableTerm*>(t);
		if(msa_set.count(vt) >0) continue;
		imp.eliminate_uvar(vt);
	}

	Constraint abduct = imp;
	Constraint new_lhs = abduct & lhs;
	//cout << "LHS: " << lhs << endl;
	//cout << "Abductive solution: " << abduct << endl;
	//cout << "new lhs: " << new_lhs << endl;
	//cout << "rhs: " << rhs << endl;

	//cout << "imp: " << imp << endl;

	assert(new_lhs.implies(rhs));


	imp.replace_terms(rev_sub);
	return imp;


}

void Constraint::operator&=(const Constraint & other)
{
	(*this) = (*this) & other;
}
void Constraint::operator|=(const Constraint & other)
{
	(*this) = (*this) | other;
}

Constraint Constraint::operator!() const
{
	Constraint new_c;
	new_c.id = cs.not_constraint(this->id);
	return new_c;
}

string Constraint::to_string() const
{
	//if(valid()) return "true";
	//if(unsat()) return "false";
	return cs.constraint_to_string(id);
}

/*
 * Checks if this <=> other
 */
bool Constraint::equivalent(Constraint other) const
{
	return cs.is_equivalent(id, other.id);
}

string Constraint::debug_string()
{
	return cs.constraint_to_string(id);
}

void Constraint::operator=(const Constraint &  other)
{
	this->id = other.id;
}

void Constraint::fresh_id()
{
	this->id = cs.get_new_id(id);
}

/*
 * Checks if nc == other.nc && sc==other.sc
 */
bool Constraint::operator==(const Constraint &  other)const
{
	return cs.is_equal(this->id, other.id);
}

bool Constraint::operator!=(const Constraint &  other) const
{
	return !((*this) == other);
}


bool Constraint::operator<(const Constraint  & other) const
{
	return this->id<other.id;
}

bool Constraint::contains_inequality()
{
	return cs.contains_inequality(this->id);
}

Constraint Constraint::nc() const
{
	Constraint c;
	c.id = cs.nc(id);
	return c;
}
Constraint Constraint::sc() const
{
	Constraint c;
	c.id = cs.sc(id);
	return c;
}

void Constraint::get_terms(set<Term*>& terms, bool include_nested_terms)
{
	cs.get_terms(id, terms, include_nested_terms);
}

bool Constraint::is_precise() const
{
	return cs.is_precise(id);
}


void Constraint::replace_term(Term* to_replace, Term* replacement)
{
	c_id old_id = id;
	id = cs.replace_term(old_id, to_replace, replacement);
}

void Constraint::replace_terms(map<Term*, Term*> & replacements)
{
	c_id old_id = id;
	id = cs.replace_terms(old_id, replacements);
}


void Constraint::replace_constraint(Constraint to_replace,
		Constraint replacement)
{

	c_id old_id = id;

	id = cs.replace_constraint(old_id, to_replace.id, replacement.id);
}



void Constraint::get_free_variables(set<Term*>& vars)
{
	cs.get_free_vars(id, vars);
}


void Constraint::eliminate_evar(VariableTerm* var)
{
	c_id new_id = cs.eliminate_evar(id, var);
	id = new_id;
}

void Constraint::eliminate_evars(set<VariableTerm*>& vars)
{
	if(vars.size() == 0) return;
	c_id new_id = cs.eliminate_evars(id, vars);
	id = new_id;
}

void Constraint::eliminate_uvar(VariableTerm* var)
{
	c_id new_id = cs.eliminate_uvar(id, var);
	id = new_id;
}

void Constraint::eliminate_uvars(set<VariableTerm*>& vars)
{
	if(vars.size() == 0) return;
	c_id new_id = cs.eliminate_uvars(id, vars);
	id = new_id;
}



bool Constraint::contains_term(Term* var)
{
	return cs.contains_term(id, var);
}

bool Constraint::contains_term(set<Term*>& terms)
{
	return cs.contains_term(id, terms);
}

int Constraint::nc_size() const
{
	return cs.nc_size(id);
}
int Constraint::sc_size() const
{
	return cs.sc_size(id);
}

void Constraint::eliminate_free_var(VariableTerm* var)
{
	sat();

	valid();
	c_id new_id = cs.eliminate_free_var(id, var);
	id = new_id;
}

void Constraint::eliminate_free_vars(set<VariableTerm*>& vars)
{
	if(vars.size() == 0) return;
	sat();
	valid();
	c_id new_id = cs.eliminate_free_vars(id, vars);
	id = new_id;
}

bool Constraint::get_assignment(set<pair<string, string> > & assignments)
{
	bool sat = cs.get_assignment(id, assignments);
	return sat;
}

bool Constraint::get_assignment(map<Term*, SatValue> & assignments)
{
	bool sat = cs.get_assignment(id, assignments);
	return sat;
}


void Constraint::assume(Constraint c)
{
	id = cs.assume(id, c.id);
}


Term* Constraint::find_equality(Term* t) const
{
	return cs.find_equality(id, t);
}

void Constraint::find_equalities(Term* t, set<Term*> & eqs) const
{
	cs.find_equalities(id, t, eqs);
}

bool Constraint::has_equality_relation(Term* t1, Term* t2)
{
	return cs.has_equality_relation(id, t1, t2);
}


void Constraint::get_disjunctive_equalities(Term* var,
		map<Term*, Constraint> & equalities)
{
	cs.get_disjunctive_equalities(id, var, equalities);
}


void Constraint::set_background_knowledge(Constraint c)
{
	Constraint nc = c.nc();
	cs.set_background_knowledge(nc.id);
}

void Constraint::add_ground_axiom(Constraint key, Constraint c)
{
	cs.add_axiom(key.id, c.id, false);
}



void Constraint::add_quantified_axiom(Constraint key, Constraint c)
{
	cs.add_axiom(key.id, c.id, true);
}

void Constraint::replace_term_in_axioms(Term* old_t, Term* new_t)
{
	cs.replace_term_in_axioms(old_t, new_t);
}

void Constraint::propagate_background()
{
	id = cs.propagate_background(id);
}

void Constraint::disable_background()
{
	cs.disable_background();
}

string Constraint::background_knowledge_to_string()
{

	return cs.bg_to_string();
}

Constraint Constraint::get_general_background()
{
	Constraint c;
	c.id = cs.get_general_background();
	return c;
}

void Constraint::clear_background()
{
	cs.clear_bg();
}

ostream& operator <<(ostream &os,const Constraint &obj)
{
	os << obj.to_string();
	return os;
}

void Constraint::clear()
{
	cs = ConstraintSolver();
}

void Constraint::divide(long int c, Term* t)
{
	id = cs.divide(id, c, t);
}

int Constraint::msa(set<VariableTerm*> & msa) const
{
	map<VariableTerm*, int> costs;
	return cs.msa(msa, id, costs);
}

void Constraint::get_msa_assignment(set<VariableTerm*>&
		msa_vars, map<Term*, SatValue>& msa)
{
	cout << "GETTIN MSA ASSIGNMENT!!!  " << endl;
	set<Term*> terms;
	set<VariableTerm*> elim;
	this->get_terms(terms, false);
	for(auto it = terms.begin(); it!= terms.end(); it++) {
		Term* cur = *it;
		cout << "Cur term: " << cur->to_string() << endl;
		if(cur->get_term_type() != VARIABLE_TERM) continue;
		VariableTerm* cur_var = static_cast<VariableTerm*>(cur);
		cout << "Variable term " << endl;
		if(msa_vars.count(cur_var) > 0) continue;
		cout << "Not in msa: " << cur_var->to_string() << endl;
 		elim.insert(cur_var);
	}
	cout << "THIS: " << this->to_string() << endl;
	Constraint new_c(*this);
	cout << "OLD C: " << new_c << endl;
	new_c.eliminate_uvars(elim);
	cout << "AFTER ELIM: " << new_c << endl;
	new_c.get_assignment(msa);
	return;


}

int Constraint::msa(map<Term*, SatValue> & msa)
{
	set<VariableTerm*> msa_vars;
	map<VariableTerm*, int> costs;
	int res= cs.msa(msa_vars, id, costs);
	get_msa_assignment(msa_vars, msa);
	return res;
}



int Constraint::msa(set<VariableTerm*> & msa, set<Constraint>& bg) const
{
	map<VariableTerm*, int> costs;

	set<c_id> bg_ids;
	set<Constraint>::iterator it = bg.begin();
	for(; it != bg.end(); it++) {
		bg_ids.insert(it->id);
	}

	return cs.msa(msa, id, bg_ids, costs);
}


int Constraint::msa(map<Term*, SatValue> & msa, set<Constraint>& bg)
{
	set<VariableTerm*> msa_vars;
	int res= this->msa(msa_vars, bg);
	get_msa_assignment(msa_vars, msa);
	return res;

}




int  Constraint::msa(set<VariableTerm*> & msa, map<VariableTerm*, int>& costs) const
{
	return cs.msa(msa, id, costs);
}
int Constraint::msa(set<VariableTerm*> & msa, set<Constraint>& bg,
		map<VariableTerm*, int>& costs) const
{
	set<c_id> bg_ids;
	set<Constraint>::iterator it = bg.begin();
	for(; it != bg.end(); it++) {
		bg_ids.insert(it->id);
	}
	return cs.msa(msa, id, bg_ids, costs);
}

int  Constraint::msa(map<Term*, SatValue> & msa, set<Constraint>& bg,
		map<VariableTerm*, int>& costs)
{
	set<VariableTerm*> msa_vars;
	int res = this->msa(msa_vars, bg, costs);
	get_msa_assignment(msa_vars, msa);
	return res;
}

pair<CNode*, CNode*> Constraint::get_cnodes()
{
	return cs.get_cnodes(id);
}

void Constraint::to_dnf(set<Constraint> & dnf)
{
	set<c_id> res;
	cs.to_dnf(id, res);
	for(auto it = res.begin(); it != res.end(); it++) {
		Constraint c;
		c.id = *it;
		dnf.insert(c);
	}

}

void Constraint::to_cnf(set<Constraint> & cnf)
{
	Constraint not_c = !(*this);
	set<c_id> res;
	cs.to_dnf(not_c.id, res);
	for(auto it = res.begin(); it != res.end(); it++) {
		Constraint c;
		c.id = *it;
		cnf.insert(!c);
	}

}


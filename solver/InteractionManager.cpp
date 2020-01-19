/*
 * ComparableTerms.cpp
 *
 *  Created on: Sep 6, 2008
 *      Author: tdillig
 */

#include "InteractionManager.h"
#include "Term.h"
#include "ClauseSolve.h"
#include "Clause.h"
#include "FunctionTerm.h"
#include "ConstantTerm.h"
#include "VariableTerm.h"
#include "VarMap.h"
#include "EqLeaf.h"
#include "assert.h"
#include "Matrix.h"
#include <algorithm>


#define DEBUG false
#define ASSERT_ENABLED false

ILPQuery::ILPQuery(Term* t1, Term* t2)
{

	if(t1 < t2) {
		this->t1 = t1;
		this->t2 = t2;
	}
	else {
		this->t1 = t2;
		this->t2 = t1;
	}
}



string ILPQuery::to_string()
{
	string res = t1->to_string();
	res += " = " + t2->to_string();
	res += "\n";
	return res;
}


InteractionManager::InteractionManager(ClauseSolve* s,
		set<Term*> & all_terms,
		set<int>& function_terms):
			 inequalities(s->cl->neg_eq),
			eq_members(s->eq_members),eq_size(s->eq_size),
			eq_constants(s->eq_class_const)
{


	this->s = s;
	if(DEBUG) {
		s->print_eq_classes();
	}

	map<Term*, int>::iterator ii = eq_size.begin();
	for(;ii != eq_size.end(); ii++)
	{
		representatives.insert(ii->first);
	}


}





string InteractionManager::queries_to_string()
{
	string res = "QUERIES \n";
	set<ILPQuery*>::iterator it = queries.begin();
	for(; it!=queries.end(); it++){
		res += (*it)->to_string();
		res += "\t";
	}
	res += "\n";
	return res;
}


/*
 * To determine what queries to issue, we consider pairs of congruence
 * classes that contain shared variables. We then perform a "conditional union"
 * of this pair (C1, C2) of congruence classes. If the conditional union results in
 * either (a) a contradiction, (b) inference of a new equality between ilp
 * variables, or (c) inference of a disequality between congruence classes,
 * we conclude the query x=y is relevant where x and y are shared variables
 * in class C1 and C2 respectively. Note that only a single query per pair
 * of congruence classes is sufficient since known equalities are already
 * propagated to the ilp domain.
 */
void InteractionManager::build_queries()
{

	/*
	 * First, we build a mapping from classes to whether they contain any ilp
	 * variables or not. If a congruence class does not contain an ilp variable,
	 * we do not need to check whether any new equalities or disequalities may
	 * be inferred.
	 */
	set<Term*> classes_with_ilp_vars;


	set<Term*>::iterator it = representatives.begin();
	for(; it!= representatives.end(); it++)
	{
		Term* constant_term = NULL;
		bool found_ilp_var = false;
		Term* rep = *it;
		set<Term*>& eq_members = s->eq_members[rep];
		set<Term*>::iterator it2 = eq_members.begin();
		for(; it2!=eq_members.end(); it2++) {
			Term* t = *it2;
			if(t->get_term_type() == CONSTANT_TERM) constant_term = t;
			else if(t->get_term_type() == VARIABLE_TERM) {
				VariableTerm* vt = (VariableTerm*) t;
				if(s->ilp_vars.count(vt->get_var_id()) > 0) {
					classes_with_ilp_vars.insert(t);
					found_ilp_var = true;
					break;
				}
			}
		}

		if(!found_ilp_var && constant_term!=NULL) {
			classes_with_ilp_vars.insert(constant_term);
		}

	}




	set<Term*>::iterator it1 = classes_with_ilp_vars.begin();
	for(; it1!=classes_with_ilp_vars.end(); it1++){
		Term* t1 = *it1;
		set<Term*>::iterator it2 = it1;
		it2++;
		for(; it2!=classes_with_ilp_vars.end(); it2++){
			Term* t2 = *it2;
			//string before = s->eq_classes_to_string();
			//cout << "Considering: " << t1->to_string() << " and " <<
			//		t2->to_string() << endl;
			//if(!is_relevant_pair(s->find_representative(t1),
				//	s->find_representative(t2))){
			if(!is_relevant_pair(t1, t2)) {
				//string after = s->eq_classes_to_string();
				//assert(before == after);
				//cout << "Not relevant!" << endl;
				continue;
			}
			//string after = s->eq_classes_to_string();
			//if(before != after) {
			//	cout << "Before: " << before << endl;
			//	cout << "After: " << after << endl;
			//	assert(false);
			//}
			add_query(t1, t2);

		}

	}

	if(DEBUG) {
		cout << "========> INITIAL QUERIES (not refined) <====== " << endl;
		cout << queries_to_string() << endl;
		cout << "================================================" << endl;
	}


}



inline void InteractionManager::add_query(Term* t1, Term* t2)
{
	if(ASSERT_ENABLED) assert(t1!=t2);
	if(t1->get_term_type() == CONSTANT_TERM &&
			t2->get_term_type() == CONSTANT_TERM) return;
	queries.insert(new ILPQuery(t1, t2));

}


/*
 * A pair of terms (t1, t2) is relevant to a query if their conditional
 * union results in  (a) a contradiction, (b) inference of a new equality
 * between ilp variables, or (c) inference of a disequality between
 * congruence classes. The conditional union is always undone before this
 * function returns.
 */
inline bool InteractionManager::is_relevant_pair(Term* t1, Term* t2)
{
	set<Term*> changed_eq_classes;
	bool used_function_axiom = false;
	bool contradiction = !s->perform_conditional_union(t1, t2,
			changed_eq_classes, used_function_axiom);

	if(!used_function_axiom){
		s->undo_conditional_union();
		return false;
	}

	if(contradiction) {
		s->undo_conditional_union();
		return true;
	}

	if(s->has_contradiction()) {
		s->undo_conditional_union();
		return true;
	}

	pair<Term*, Term*> eq = make_term_pair(t1, t2);


	/*
	 * Since we want to see if there are any additional equalities between
	 * ilp variables other than the query we are making, temporarily add
	 * t1=t2 to existing equalities, and remove it once
	 * we do the check.
	 */
	if(ASSERT_ENABLED) assert(existing_equalities.count(eq) == 0);
	this->existing_equalities.insert(eq);


	set<pair<Term*, Term*> > inferred_eqs;
	get_inferred_equalities(changed_eq_classes, inferred_eqs);

	this->existing_equalities.erase(eq);


	if(inferred_eqs.size() > 0) {
		s->undo_conditional_union();
		return true;
	}

	set<pair<Term*, Term*> > inferred_dis_eqs;
	get_inferred_inequalities(changed_eq_classes, inferred_dis_eqs);



	if(inferred_dis_eqs.size() > 0) {
		s->undo_conditional_union();
		return true;
	}


	s->undo_conditional_union();
	return false;
}

void InteractionManager::get_inferred_equalities(set<Term*>& relevant_classes,
		set<pair<Term*, Term*> >& inferred_eqs)
{

	//cout << "===========GETTING INFERRED EQUALITIES... " << endl;
	set<Term*>::iterator it = relevant_classes.begin();
	for(; it!= relevant_classes.end(); it++)
	{
		Term* t = *it;

		/*
		 * If the representative is not itself, then during union,
		 * it must have been merged with some other class and we don't
		 * need to consider this one.
		 */
		if(t != t->representative) continue;
		if(ASSERT_ENABLED) assert(eq_members.count(t) > 0);
		set<Term*>& members = eq_members[t];
		set<Term*>::iterator it1 = members.begin();
		for(; it1 != members.end(); it1++)
		{
			Term* t1 = *it1;
			//cout << "Member: " << t1->to_string() << endl;
			if(!is_relevant_term_to_ilp_domain(t1)){
				//cout << "Not relevant: " << t1->to_string() << endl;
				continue;
			}

			set<Term*>::iterator it2 = it1;
			it2++;
			for(; it2 != members.end(); it2++)
			{
				Term* t2 = *it2;
				//cout << "T2: " << t2->to_string() << endl;
				if(!is_relevant_term_to_ilp_domain(t2)) {
					//cout << "Not relevant! " << t2->to_string() << endl;
					continue;
				}
				pair<Term*, Term*> p = make_term_pair(t1, t2);
				if(this->existing_equalities.count(p) > 0){
					//cout << "Existing!" << endl;
					continue;
				}

				//cout << "Inferred eq: " << p.first->to_string() <<
				//		" and " << p.second->to_string() << endl;
				inferred_eqs.insert(p);
			}
		}
	}
}


inline bool InteractionManager::is_relevant_term_to_ilp_domain(Term* t)
{
	if(ASSERT_ENABLED) assert(t!=NULL);
	switch(t->get_term_type())
	{
	case FUNCTION_TERM:
		return false;
	case CONSTANT_TERM:
		return true;
	case VARIABLE_TERM:
	{
		VariableTerm* vt = (VariableTerm*) t;
		return (s->ilp_vars.count(vt->get_var_id()) > 0);
	}
	default:
		assert(false);
	}
}

void InteractionManager::get_inferred_inequalities(set<Term*>& relevant_classes,
		set<pair<Term*, Term*> >& inferred_ineqs)
{
	set<EqLeaf*>::iterator it = this->inequalities.begin();
	for(; it!= this->inequalities.end(); it++)
	{
		EqLeaf* cur_neq = *it;
		Term* t1 = cur_neq->get_rhs();
		Term* t2 = cur_neq->get_lhs();

		Term* t1_rep = s->find_representative(t1);
		Term* t2_rep = s->find_representative(t2);

		if(relevant_classes.count(t1_rep) == 0 &&
				relevant_classes.count(t2_rep) ==0) continue;

		set<Term*>& class1 = eq_members[t1_rep];
		set<Term*>& class2 = eq_members[t2_rep];

		set<pair<Term*, Term*> > cur_inferred;
		bool found_constants = false;
		set<Term*>::iterator it1 = class1.begin();
		for(; it1!=class1.end(); it1++)
		{
			Term* t1 = *it1;
			if(!is_relevant_term_to_ilp_domain(t1)) continue;
			bool t1_constant = t1->get_term_type() == CONSTANT_TERM;

			set<Term*>::iterator it2 = class2.begin();
			for(; it2!= class2.end(); it2++) {
				Term* t2 = *it2;
				if(!is_relevant_term_to_ilp_domain(t2)) continue;
				if(t1_constant && t2->get_term_type() == CONSTANT_TERM) {
					cur_inferred.clear();
					found_constants = true;
					break;
				}
				pair<Term*, Term*> p = make_term_pair(t1, t2);
				set<pair<Term*, Term*> > cur_ineq;
				cur_ineq.insert(p);
				if(existing_inequalities.count(cur_ineq) > 0) continue;
				cur_inferred.insert(p);

			}
			if(found_constants) continue;
			inferred_ineqs.insert(cur_inferred.begin(), cur_inferred.end());

		}



	}
}


/*
 * Makes a canonical pair such that if we call
 * make_term_pair(t1, t2) and make_term_pair(t2, t1),
 * we get the same pair back.
 */
inline pair<Term*, Term*> InteractionManager::make_term_pair(Term* t1, Term* t2)
{
	if(t1<t2) return make_pair(t1, t2);
	else return make_pair(t2, t1);
}

/*
 * Adds equalities inferred by the theory of equality to
 * the ILP domain by populating the matrix.
 * Return value indicates if we added any new equalities.
 */
bool InteractionManager::add_inferred_equalities()
{
	bool res = false;
	map<Term*, set<Term*> >::iterator it = eq_members.begin();
	for(; it!=eq_members.end(); it++)
	{
		set<Term*>& equal = it->second;
		if(equal.size() < 2) continue;
		Term *lhs = NULL;
		set<Term*>::iterator it2 = equal.begin();
		for(; it2!=equal.end(); it2++)
		{
			 if((*it2)->get_term_type()!= VARIABLE_TERM)
				 continue;
			 VariableTerm *vt = (VariableTerm*)*it2;
			 if(s->ilp_vars.count(vt->get_var_id()) > 0){
				 lhs = *it2;
				 break;
			 }
		}
		if(lhs == NULL)
			continue;

		it2 = equal.begin();
		for(; it2!=equal.end(); it2++)
		{

			Term* rhs = *it2;
			if(rhs->get_term_type() == FUNCTION_TERM)
				continue;
			if(rhs->get_term_type() == VARIABLE_TERM) {
				VariableTerm* rhs_v = (VariableTerm*) rhs;
				if(s->ilp_vars.count(rhs_v->get_var_id()) == 0) continue;
			}

			pair<Term*, Term*> p = make_term_pair(lhs, rhs);
			if(rhs == lhs || existing_equalities.count(p)>0) continue;
			s->add_equality(lhs, rhs);
			res = true;
			existing_equalities.insert(p);
		}
	}

	return res;
}

/*
 * Given a variable term (which may or may not be shared), returns a member
 * in its equivalence class that is shared and NULL otherwise.
 * Obviously, constants are considered to be shared.
 */
Term* InteractionManager::get_shared_member(VariableTerm* vt)
{
	Term* rep = s->find_representative(vt);
	set<Term*>& eq_class = eq_members[rep];
	set<Term*>::iterator it = eq_class.begin();
	for(; it!= eq_class.end(); it++) {
		Term* t = *it;
		if(t->get_term_type() == CONSTANT_TERM) {
			return t;
		}
		if(t->get_term_type()==FUNCTION_TERM) continue;
		if(ASSERT_ENABLED) assert(t->get_term_type() == VARIABLE_TERM);
		if(s->ilp_vars.count(((VariableTerm*)t)->get_var_id())>0) return t;
	}
	return NULL;
}


void vector_set_to_set_vector_internal(vector<set<pair<Term*, Term*> > >& vs,
		set<vector<pair<Term*, Term*> > >&
		sv, vector<pair<Term*, Term*> > & cur)
{
	if(cur.size() == vs.size())
	{
		sv.insert(cur);
		return;
	}
	set<pair<Term*, Term*> > & cur_set = vs[cur.size()];
	set<pair<Term*, Term*> >::iterator it = cur_set.begin();
	for(; it != cur_set.end(); it++)
	{
		cur.push_back(*it);
		vector_set_to_set_vector_internal(vs, sv, cur);
		cur.pop_back();
	}
}
void vector_set_to_set_vector(vector<set<pair<Term*, Term*> > >& vs,
		set<vector<pair<Term*, Term*> > >& sv)
{
	vector<pair<Term*, Term*> >  cur;
	vector_set_to_set_vector_internal(vs, sv, cur);
}


/*
 * Given two terms t1 and t2 for which a disequality relation t1!=t2
 * exists, this function returns a set of pairs { ...<t_i, t_j> ...}
 * such that t_i != t_j is also implied. Furthermore, these terms t_i and t_j
 * only contains terms that are shared between theories, and for which
 * "meaningful" disequality implication can be propagated. For example,
 * if <f(a), g(b)> cannot be such a pair because no disequality relations can
 * be propagated. On the other hand, if f(a, g(b)) and f(x, g(y)) is a pair
 * in the set, then a, b, x, and y are all shared.
 */
void InteractionManager::find_disequality_terms(Term* t1, Term* t2,
		set<pair<Term*, Term*> >& terms)
{
	map<pair<Term*, Term*>,set<pair<Term*, Term*> > > visited;
	find_disequality_terms_internal(t1, t2, terms, visited, true);
	return;
	/*set<pair<Term*, Term*> > terms2;
	visited.clear();
	find_disequality_terms_internal(t1, t2, terms2, visited, true);
	if(terms != terms2) {
		cout << "Problem finding disequality terms: " << t1->to_string() <<
				" and " << t2->to_string() << endl;
		cout << "----Without visited check-----: " << endl;
		set<pair<Term*, Term*> >::iterator it = terms.begin();
		for(; it!= terms.end(); it++) {
			cout << " \t " << it->first->to_string() << " != " <<
					it->second->to_string() << endl;
		}
		cout << "---With visited check-----:"<< endl;
		it = terms2.begin();
		for(; it!= terms2.end(); it++) {
			cout << " \t " << it->first->to_string() << " != " <<
					it->second->to_string() << endl;
		}
		assert(false);
	}*/
}

void InteractionManager::find_disequality_terms_internal(Term* t1, Term* t2,
		set<pair<Term*, Term*> >& terms,
		map<pair<Term*, Term*>,set<pair<Term*, Term*> > >& visited,
		bool check_visited)
{




	t1 = s->find_representative(t1);
	t2 = s->find_representative(t2);




	pair<Term*, Term*> p =make_term_pair(t1, t2);

	if(check_visited && visited.count(p) > 0) {
		map<pair<Term*, Term*>,set<pair<Term*, Term*> >  >::iterator it =
				visited.find(p);

		//terms.insert(it->second.begin(), it->second.end());
		return;
	}





	set<Term*>& t1_mems = s->eq_members[t1];
	set<Term*>& t2_mems = s->eq_members[t2];

	set<Term*>::iterator it = t1_mems.begin();
	for(; it!=t1_mems.end(); it++)
	{
		Term* t1 = *it;
		if(t1->get_term_type() == VARIABLE_TERM) {
			VariableTerm* vt = (VariableTerm*) t1;
			if(s->ilp_vars.count(vt->get_var_id()) == 0) continue;

		}
		bool t1_function = (t1->get_term_type() == FUNCTION_TERM);
		set<Term*>::iterator it2 = t2_mems.begin();
		for(; it2 != t2_mems.end(); it2++)
		{
			Term* t2 = *it2;

			if(t2->get_term_type() == VARIABLE_TERM) {
				VariableTerm* vt = (VariableTerm*) t2;
				if(s->ilp_vars.count(vt->get_var_id()) == 0) continue;

			}
			bool t2_function = (t2->get_term_type() == FUNCTION_TERM);

			// Found a pair for which we can add ilp disequalities
			if(!t1_function && !t2_function) {
				terms.insert(make_pair(t1, t2));
				visited[p].insert(make_pair(t1, t2));
				continue;
			}

			// These are incompatible
			if(!t1_function || !t2_function) continue;

			FunctionTerm* ft1 = (FunctionTerm*) t1;
			FunctionTerm* ft2 = (FunctionTerm*) t2;


			// also incompatible
			if(ft1->get_id() != ft2->get_id()) continue;
			if(ft1->get_args().size() != ft2->get_args().size()) continue;

			// ft1 and ft2 have the same function id; for each of their
			// arguments, we must be able to find a compatible pair.
			const vector<Term*>& args1 = ft1->get_args();
			const vector<Term*>& args2 = ft2->get_args();
			vector<set<pair<Term*, Term*> > > new_args;

			bool cont = false;

			for(unsigned int i=0; i< args1.size(); i++)
			{
				Term* arg1 = args1[i];
				Term* arg2 = args2[i];
				set<pair<Term*, Term*> > new_terms;

				if(s->find_representative(arg1) == s->find_representative(arg2))
				{
					new_terms.insert(make_pair(arg1,arg1));
					new_args.push_back(new_terms);

					continue;
				}


				visited[p].insert(make_pair(t1, t2));
				find_disequality_terms_internal(arg1, arg2, new_terms, visited,
						check_visited);
				if(new_terms.size() == 0){
					cont = true;
					break;
				}

				new_args.push_back(new_terms);
			}

			if(cont) continue;
			set<vector<pair<Term*, Term*> > > new_args_set;
			vector_set_to_set_vector(new_args, new_args_set);
			set<vector<pair<Term*, Term*> > >::iterator it = new_args_set.begin();
			for(; it != new_args_set.end(); it++)
			{
				const vector<pair<Term*, Term*> > & cur = *it;
				vector<Term*> args1;
				vector<Term*> args2;

				map<Term*, Term*> subs1;
				map<Term*, Term*> subs2;
				vector<pair<Term*, Term*> >::const_iterator it2 = cur.begin();
				int i = 0;
				bool one_s = true;
				bool two_s = true;
				for(; it2 != cur.end(); it2++, i++)
				{
					args1.push_back(it2->first);
					args2.push_back(it2->second);
					subs1[ft1->get_args()[i]] = it2->first;

					if(!it2->first->is_specialized()) one_s = false;
					subs2[ft2->get_args()[i]] = it2->second;
					if(!it2->second->is_specialized()) two_s = false;
				}

				Term* t1;
				if(one_s)
					t1 = ft1->substitute(subs1);
				else t1 = FunctionTerm::make(ft1->get_id(),
						args1, ft1->is_invertible());

				Term* t2;
				if(two_s)
					t2 = ft2->substitute(subs2);
				else t2 = FunctionTerm::make(ft2->get_id(),
						args2, ft2->is_invertible());

				terms.insert(make_pair(t1, t2));
				visited[p].insert(make_pair(t1, t2));
			}

		}
	}
}

void InteractionManager::add_disequality(Term* t1, Term* t2,
		set<pair<Term*, Term*> >& to_add)
{
	if(t1 > t2)
	{
		Term* temp = t1;
		t1 = t2;
		t2 = temp;
	}

	if(t1->get_term_type() == CONSTANT_TERM &&
			t2->get_term_type() == CONSTANT_TERM) return;

	if(t1->get_term_type() != FUNCTION_TERM) {
		assert(t2->get_term_type() != FUNCTION_TERM);
		to_add.insert(make_pair(t1, t2));
		return;
	}

	assert(t1->get_term_type() == FUNCTION_TERM &&
			t2->get_term_type() == FUNCTION_TERM);

	FunctionTerm* ft1 = (FunctionTerm*) t1;
	FunctionTerm* ft2 = (FunctionTerm*) t2;

	if(ft1->get_id() != ft2->get_id()){
		return;
	}
	const vector<Term*>& args1 = ft1->get_args();
	const vector<Term*>& args2 = ft2->get_args();
	assert(args1.size() == args2.size());

	for(unsigned int i=0; i<args1.size(); i++)
	{
		Term* arg1 = args1[i];
		Term* arg2 = args2[i];
		if(arg1 == arg2) continue;
		if(s->find_representative(arg1) == s->find_representative(arg2))
			continue;

		if(arg1->get_term_type() == CONSTANT_TERM &&
				arg2->get_term_type() == CONSTANT_TERM)
		{
				to_add.clear();
				return;
		}

		add_disequality(arg1, arg2, to_add);
	}


}


bool InteractionManager::add_inequality(Term* lhs, Term* rhs)
{

	if(DEBUG) cout << "Adding inequality from: " << lhs->to_string() <<
			" != " << rhs->to_string() << endl;
	set<pair<Term*, Term*> > terms;
	find_disequality_terms(lhs, rhs, terms);

	if(DEBUG){
		cout << "INEQUALITY SET ======= "<< endl;
		set<pair<Term*, Term*> >::iterator it = terms.begin();
		for(; it != terms.end(); it++)
		{
			cout << "\t" << it->first->to_string() << "    "
					<< it->second->to_string() << endl;
		}
	}

	bool res = false;
	set<pair<Term*, Term*> >::iterator it = terms.begin();
	for(; it!= terms.end(); it++)
	{
		Term* cur1 = it->first;
		Term* cur2 = it->second;
		set<pair<Term*, Term*> > to_add;
		add_disequality(cur1, cur2, to_add);
		if(to_add.size() == 0) continue; // no inequalities found
		if(existing_inequalities.count(to_add) > 0) continue;
		res = true;
		existing_inequalities.insert(to_add);

		if(DEBUG)
		{
			cout << "Found inequality: " << endl;

			{
				set<pair<Term*, Term*> >::iterator it = to_add.begin();
				for(; it!= to_add.end(); it++)
				{
					if(it != to_add.begin()) cout << " | " ;
					cout << it->first->to_string() << "!="<< it->second->to_string();

				}
				cout << endl;
			}
		}

		set<pair<Equation*, bignum> > new_inequality;
		s->add_inequality(to_add, new_inequality);
	}

	return res;
}

/*
 * Adds the inequalities inferred by the theory of equality to
 * the ILP domain by populating the neq_matrix.
 */
bool InteractionManager::add_inferred_inequalities()
{
	bool res = false;
	set<EqLeaf*>::iterator it = inequalities.begin();
	for(; it!= inequalities.end(); it++)
	{
		EqLeaf* cur = *it;
		Term* lhs = cur->get_lhs();
		Term* rhs = cur->get_rhs();
		if(add_inequality(lhs, rhs))
			res = true;
	}

	return res;
}

bool InteractionManager::eq_class_contains_fn_term(Term* t)
{
	Term* rep = s->find_representative(t);
	if(rep->get_term_type() == FUNCTION_TERM) return true;
	set<Term*> eq_class = s->eq_members[rep];
	set<Term*>::iterator it = eq_class.begin();
	for(; it!= eq_class.end(); it++) {
		Term* cur = *it;
		if(cur->get_term_type() == FUNCTION_TERM)
			return true;
	}
	return false;
}


class QueryComparator {
private:
	Term* find_representative(Term* t) const
	{
		while(t!=t->representative)
		{
			t = t->representative;
		}
		return t;
	}

public:
    bool operator()(const ILPQuery* const & _q1, const ILPQuery* const & _q2) const
    {
    	ILPQuery& q1 = *(ILPQuery*&)_q1;
    	ILPQuery& q2 = *(ILPQuery*&)_q2;
    	Term* q1r1 = find_representative(q1.t1);
    	Term* q1r2 = find_representative(q1.t2);

    	if(q1r1>q1r2)
    	{
    		Term *temp = q1r1;
    		q1r1 = q1r2;
    		q1r2 = temp;
    	}

    	Term* q2r1 = find_representative(q2.t1);
    	Term* q2r2 = find_representative(q2.t2);
    	if(q2r1>q2r2)
		{
			Term *temp = q2r1;
			q2r1 = q2r2;
			q2r2 = temp;
		}
    	if(q1r1<q2r1)
    		return true;
    	if(q1r1>q2r1)
    		return false;
    	if(q1r2<q2r2)
    		return true;
    	return false;
    }
};

/*
 * To make sure that we don't issue a query like x=y?
 * if x and y are already in the same equivalence
 * class.
 */
set<ILPQuery*> & InteractionManager::refine_queries()
{
	set<ILPQuery*, QueryComparator> refined_set;
	refined_set.insert(queries.begin(), queries.end());

	set<ILPQuery*> to_delete;
	to_delete.insert(queries.begin(), queries.end());

	set<ILPQuery*, QueryComparator> refined_set2;

	set<ILPQuery*, QueryComparator>::iterator it = refined_set.begin();
	for(; it!=refined_set.end(); it++){
		ILPQuery* cur = *it;
		Term* t1 = cur->t1;
		Term* t2 = cur->t2;

		bignum assign1, assign2;
		if(t1->get_term_type() == VARIABLE_TERM) {
			if(ASSERT_ENABLED) assert(s->ilp_assignments.count(t1) > 0);
			assign1 = s->ilp_assignments[t1];
		}
		else {
			if(ASSERT_ENABLED) assert(t1->get_term_type() == CONSTANT_TERM);
			assign1 = ((ConstantTerm*)t1)->get_constant();
		}

		if(t2->get_term_type() == VARIABLE_TERM) {
			if(ASSERT_ENABLED) assert(s->ilp_assignments.count(t2) > 0);
			assign2 = s->ilp_assignments[t2];
		}
		else {
			if(ASSERT_ENABLED) assert(t2->get_term_type() == CONSTANT_TERM);
			assign2 = ((ConstantTerm*)t2)->get_constant();
		}

		if(assign1 != assign2) {
			continue;
		}
		refined_set2.insert(*it);
		to_delete.erase(*it);
	}
	set<ILPQuery*>::iterator it2 = to_delete.begin();
	for(; it2 != to_delete.end(); it2++) {

		delete *it2;
	}
	queries.clear();
	queries.insert(refined_set2.begin(), refined_set2.end());
	return queries;
}

set<ILPQuery*> & InteractionManager::get_queries()
{
	return queries;
}



InteractionManager::~InteractionManager() {
	set<ILPQuery*>::iterator it = queries.begin();
	for(; it!=queries.end(); it++)
		delete *it;
}

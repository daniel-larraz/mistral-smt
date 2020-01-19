/*
 * Matrix.h
 *
 *  Created on: Dec 10, 2008
 *      Author: tdillig
 */

#include "Equation.h"
#include <unordered_map>
#include <set>
#include <map>
#include <list>


typedef  unordered_map<Equation*, bignum, hash<Equation*>, equation_eq> eq_map;

#ifndef BIG_MATRIX_H_
#define BIG_MATRIX_H_

#define MATRIX_ASSERT false

#define REAL (1)
#define IGNORED (1<<1)



class Matrix {

public:
	class iterator
	{
		friend class Matrix;
	private:
		set<pair<int, Equation*> >::iterator it;
		Matrix & m;
		iterator(set<pair<int, Equation*> >::iterator it, Matrix & m):
			it(it), m(m)
		{

		}
	public:
		pair<Equation* const, bignum> *operator->()
		{
			if(MATRIX_ASSERT) assert(m.equations.count(it->second) > 0);
			return &(*m.equations.find(it->second));
		}
		pair<Equation*, bignum> operator*()
		{
			if(MATRIX_ASSERT) assert(m.equations.count(it->second) > 0);
			return *m.equations.find(it->second);
		}
		const void operator++(int i)
		{
			it++;
			while(it != m.ordered_eqs.end() && m.ignored.count(it->second) >0){
				it++;
			}

		}
		bool operator==(iterator  other)
		{
			return (it == other.it);
		}
		bool operator!=(iterator  other)
		{
			return (it != other.it);
		}

	};



private:
	vector<string> vars;
	vector<string>& original_vars;
	map<int, int> old_to_new_vars;
	map<int, Equation*> index_to_sub;
	vector<int> substitution_order;
	set<Equation*> initial_eq;
	bool initial;
	eq_map equations;
	int eq_count;
	set<pair<int, Equation*> > ordered_eqs;
	map<Equation*, int> eq_to_time;

	/*
	 * Set of equations we want to ignore (to avoid making copies)
	 */
	set<Equation*> ignored;

	list<pair<Equation*, int> > eq_stack;
	map<Equation*, list<bignum> > history;
public:
	inline Matrix(vector<string>& vars):vars(vars), original_vars(vars)
	{
		initial = true;
		eq_count = 0;
	}

	inline Matrix(Matrix & other):vars(other.vars),
	original_vars(other.original_vars)
	{
		eq_count = 0;
		initial = other.initial;
		iterator it = other.begin();
		for(; it!= other.end(); it++) {
			Equation* eq = it->first->clone();
			insert(eq, it->second);
		}

	}

	inline int num_initial_equations()
	{
		return initial_eq.size();
	}



	inline void end_initial()
	{
		initial = false;
	}

	inline int num_vars()
	{
		return vars.size();
	}

	inline bool ignored_set_empty()
	{
		return ignored.size() == 0;
	}

	inline vector<string>& get_vars()
	{
		return vars;
	}

	void check_consistency()
	{
		set<Equation*> old_eqs;
		eq_map::iterator it = equations.begin();
		for(;it != equations.end();it++){
			if(ignored.count(it->first) >0) continue;
			old_eqs.insert(it->first);
		}

		set<Equation*> new_eqs;
		set<pair<int, Equation*> >::iterator i2 = ordered_eqs.begin();
		for(; i2 != ordered_eqs.end(); i2++) {
			if(ignored.count(i2->second) >0) continue;
			new_eqs.insert(i2->second);
		}
		if(old_eqs.size() != new_eqs.size()){
			cout << "Assertion failed: OLD EQ SIZE: " << old_eqs.size() <<
			 " NEW EQ SIZE: " << new_eqs.size() << endl;
			assert(false);
		}
		assert(old_eqs == new_eqs);
	}

	inline iterator begin()
	{

		if(MATRIX_ASSERT) check_consistency();

		set<pair<int, Equation*> >::iterator it = ordered_eqs.begin();
		while(it != ordered_eqs.end() && ignored.count(it->second) >0){
			it++;
		}
		return iterator(it, *this);
	}
	inline iterator end()
	{
		return iterator(ordered_eqs.end(), *this);
	}

	inline int size()
	{
		return equations.size()-ignored.size();

	}

	inline void simplify()
	{
		map<Equation*, bignum> old_equations;
		old_equations.insert(equations.begin(), equations.end());
		equations.clear();
		ordered_eqs.clear();
		eq_to_time.clear();
		std::set<Equation*> to_delete;
		map<Equation*, bignum>::iterator it = old_equations.begin();
		for(; it!= old_equations.end(); it++)
		{
			Equation* eq = it->first;
			bignum constant = it->second;
			bignum gcd = eq->compute_gcd();
			bignum total_gcd = gcd.compute_gcd(constant);
			if(total_gcd == 0) continue;
			if(total_gcd == 1){
				insert(eq, constant);
				continue;
			}
			Equation* new_eq = new Equation(eq->get_cols());
			for(int i=0; i < eq->get_cols(); i++) {
				new_eq->set(i, eq->get(i)/total_gcd);
			}
			insert(new_eq, constant/total_gcd);
			to_delete.insert(eq);
		}
		set<Equation*>::iterator it2 = to_delete.begin();
		for(; it2!= to_delete.end(); it2++) {
			delete *it2;
		}
		if(MATRIX_ASSERT) check_consistency();
	}

	inline void insert(Equation*& eq, bignum constant)
	{
		if(eq_stack.size() >0){
			push_equation_internal(eq, constant, false);
			return;
		}
		insert_internal(eq, constant);
	}

	inline void insert_internal(Equation*& eq, bignum constant)
	{
		if(MATRIX_ASSERT) assert(eq->get_cols() == (int)vars.size());
		if(equations.count(eq) == 0){
			if(MATRIX_ASSERT){
				assert(eq_to_time.count(eq) == 0);
			}
			int time_stamp = eq_count++;
			equations[eq] = constant;
			ordered_eqs.insert(pair<int, Equation*>(time_stamp, eq));
			eq_to_time[eq] = time_stamp;
			if(initial) initial_eq.insert(eq);
		}
		else {
			Equation* old_eq = equations.find(eq)->first;
			if(MATRIX_ASSERT){
				assert(eq_to_time.count(old_eq) > 0);
			}
			bignum old_c = equations[old_eq];
			if(constant<old_c){
				if(MATRIX_ASSERT){
					assert(eq_to_time.count(old_eq) > 0);
				}
				equations[old_eq] = constant;
				if(initial) initial_eq.insert(old_eq);

			}
			delete eq;
		}
		eq = NULL;
	}

	inline bool is_initial(Equation* e)
	{
		return initial_eq.count(e) !=0;
	}



	inline void push_equation(Equation* eq, bignum constant)
	{
		push_equation_internal(eq, constant, true);
	}

	inline void push_equation_internal(Equation* eq, bignum constant, bool real)
	{
		//cout << "Push--> " << (real ? "real" : "not real" ) << endl;
		int attribute = 0;
		if(real) attribute |= REAL;
		Equation* existing = get(eq);
		if(existing == NULL) {
			if(MATRIX_ASSERT){
				assert(eq_to_time.count(eq) == 0);
			}
			int time_stamp = eq_count++;
			eq_to_time[eq] = time_stamp;
			ordered_eqs.insert(pair<int, Equation*>(time_stamp, eq));

			equations[eq] = constant;
			eq_stack.push_front(pair<Equation*, bool>(eq, attribute));
			return;
		}

		if(MATRIX_ASSERT){
			assert(eq_to_time.count(existing) > 0);
		}
		if(ignored.count(existing) > 0){
			attribute |= IGNORED;
			ignored.erase(existing);
		}
		bignum old_c = get_constant(eq);
		delete eq;
		if(old_c <= constant){
			assert(false);
			eq_stack.push_front(pair<Equation*, bool>((Equation*)NULL, attribute));
			return;
		}
		equations[existing] = constant;
		history[existing].push_front(old_c);
		eq_stack.push_front(pair<Equation*, bool>(existing, attribute));
	}

	inline void pop_equation()
	{
		while(true)
		{
			Equation* eq = eq_stack.front().first;
			int attribute = eq_stack.front().second;
			bool real = attribute & REAL;
			bool is_ignored = attribute & IGNORED;
			//cout << "Pop--> " << (real ? "real" : "not real" ) << endl;
			eq_stack.pop_front();
			if(eq == NULL){
				if(real) return;
				continue;
			}

			if(history.count(eq) == 0) {
				if(MATRIX_ASSERT) assert(equations.count(eq));
				if(MATRIX_ASSERT) {
					assert(eq_to_time.count(eq) > 0);
				}
				int old_time_stamp = eq_to_time[eq];
				pair<int, Equation*> p(old_time_stamp, eq);
				if(MATRIX_ASSERT) assert(ordered_eqs.count(p) > 0);
				ordered_eqs.erase(p);
				eq_to_time.erase(eq);
				assert(!is_ignored);
				assert(equations.count(eq) >0);
				equations.erase(eq);
				delete eq;
				if(real) return;
				continue;
			}
			bignum old_c = history[eq].front();
			history[eq].pop_front();
			if(history[eq].size() == 0)
				history.erase(eq);
			equations[eq] = old_c;
			if(is_ignored) ignored.insert(eq);
			if(real) return;
		}
	}

	inline void set_value(Equation* eq, bignum constant)
	{
		if(MATRIX_ASSERT) assert(contains(eq));
		equations[eq] = constant;
	}

	inline bool contains(Equation* eq)
	{
		return equations.count(eq)>0;
	}

	inline bool contains(Equation* eq, bignum constant)
	{
		if(!contains(eq)) return false;
		return equations[eq] == constant;
	}

	inline Equation* get(Equation* eq)
	{
		if(!contains(eq)) return NULL;
		return equations.find(eq)->first;
	}

	inline bool contains_negative(Equation* eq, bignum constant)
	{
		Equation neg_eq(vars.size());
		for(int c=0; c<eq->get_cols(); c++)
		{
			neg_eq.set(c, -eq->get(c));
		}
		if(!contains(&neg_eq)) return false;
		return contains(&neg_eq, -constant);
	}

	inline Equation* get_negative(Equation* eq, bignum constant)
	{
		Equation neg_eq(vars.size());
		for(int c=0; c<eq->get_cols(); c++)
		{
			neg_eq.set(c, -eq->get(c));
		}
		if(!contains(&neg_eq)) return NULL;
		Equation* res = equations.find(&neg_eq)->first;
		bignum c2 = equations.find(&neg_eq)->second;
		if(c2 == -constant) return res;
		return NULL;
	}

	/*
	 * Is adding eq<=constant to the matrix redundant?
	 */
	inline bool is_redundant(Equation* eq, bignum constant)
	{
		if(equations.count(eq) == 0) return false;
		bignum existing_const = equations[eq];
		return (existing_const <= constant);
	}

	inline bignum get_constant(Equation* eq)
	{
		if(MATRIX_ASSERT) assert(equations.count(eq) > 0);
		return equations[eq];
	}

	inline bool remove(Equation* eq)
	{

		if(!contains(eq)) return false;
		Equation* old_eq = equations.find(eq)->first;
		assert(ignored.count(old_eq)==0);
		if(MATRIX_ASSERT) assert(equations.count(old_eq)>0);
		equations.erase(old_eq);
		if(MATRIX_ASSERT){
			assert(eq_to_time[old_eq] > 0);
		}
		int old_time_stamp = eq_to_time[old_eq];
		pair<int, Equation*> p(old_time_stamp, old_eq);
		if(MATRIX_ASSERT) {
			assert(ordered_eqs.count(p) > 0);
		}
		ordered_eqs.erase(p);
		eq_to_time.erase(old_eq);
		delete old_eq;
		return true;
	}

	inline bool remove(Equation* eq, bignum constant)
	{
		if(!contains(eq)) return false;
		Equation* old_eq = equations.find(eq)->first;
		assert(ignored.count(old_eq)==0);
		if(equations.find(eq)->second != constant) return false;
		equations.erase(old_eq);
		if(MATRIX_ASSERT){
			assert(eq_to_time[old_eq] > 0);
		}
		int old_time_stamp = eq_to_time[old_eq];
		pair<int, Equation*> p(old_time_stamp, old_eq);
		if(MATRIX_ASSERT) assert(ordered_eqs.count(p) > 0);
		ordered_eqs.erase(p);
		eq_to_time.erase(old_eq);
		delete old_eq;
		return true;
	}

	string to_string()
	{
		string res;
		for(unsigned int i=0; i < vars.size(); i++) {
			res+= vars[i] + "\t";
		}
		res+= "[c]\n";
		eq_map::iterator it = equations.begin();
		for(; it!= equations.end(); it++) {
			res+=it->first->to_string();
			res+=it->second.to_string();
			res+="\n";
		}
		return res;
	}

	friend ostream& operator <<(ostream &os,const Matrix &obj);


	inline ~Matrix()
	{

		eq_map::iterator it = equations.begin();
		set<Equation*> to_delete;
		for(; it != equations.end(); it++) {
			to_delete.insert(it->first);
		}
		set<Equation*>::iterator it2 = to_delete.begin();
		for(; it2 != to_delete.end(); it2++) {
			delete *it2;
		}

		map<int, Equation*>::iterator it3 = index_to_sub.begin();
		for(; it3!= index_to_sub.end(); it3++) {
			delete it3->second;
		}
	}

	//-------------------------------------------------------------
	inline void make_diophantine()
	{
		Matrix::iterator it = begin();
		for(; it!= end(); it++)
		{
			Equation* eq= it->first;
			bignum constant = it->second;
			bignum coef_gcd = eq->compute_gcd();
			if(coef_gcd == 0 || constant.divisible(coef_gcd)) continue;
			bignum quotient = constant/coef_gcd;
			if(constant<0) quotient-=1;
			bignum new_c = coef_gcd*quotient;
			set_value(eq, new_c);

		}
		simplify();
	}



	/*
	 * If there is an inequality a1x1 + ... + anxn <= b as well as
	 * a1x1 + ... + anxn >= b, propagate this as an equality if there exists
	 * some a_i with coefficient +-1.
	 */
	void propagate_equalities(set< set< pair<Equation*, bignum> > >*
			neq_constraints = NULL)
	{

		set<int> neq_vars;
		if(neq_constraints != NULL) {
			set<set<pair<Equation*, bignum> > >::iterator it = neq_constraints->begin();
			for(; it!= neq_constraints->end(); it++) {
				set<pair<Equation*, bignum> >::iterator it2= it->begin();
				for(; it2!= it->end(); it2++)
				{
					Equation* e = it2->first;


					for(int i=0;i < e->num_entries(); i++) {
						if(e->get(i) != 0) neq_vars.insert(i);
					}
				}


			}
		}

		while(true)
		{
			Equation* eq_old = NULL;
			Equation* neq_old = NULL;
			iterator it = begin();
			int eliminate_index = -1; // index of var to be eliminated
			Equation* sub = NULL;
			bool progress = false;
			for(; it!= end(); it++)
			{
				eq_old = it->first;
				bignum constant = it->second;
				/*
				 * Check if this inequality actually appears as an
				 * equality.
				 */
				neq_old = get_negative(eq_old, constant);
				if(neq_old == NULL) continue;

				/*
				 * Check if any coefficient is +-1.
				 */
				bool remove = false;
				for(int c=0; c<eq_old->num_entries(); c++)
				{
					if((eq_old->get(c) == 1 || eq_old->get(c) == -1) &&
						index_to_sub.count(c) == 0 && neq_vars.count(c) == 0 &&
						var_occurs(c, eq_old, neq_old)){
						remove = true;
						eliminate_index = c;

						/*
						 * Figure out the correct substitution for the
						 * variable to be eliminated.
						 */
						sub = new Equation(eq_old->num_entries()+1);
						if(eq_old->get(c) == 1)
						{
							for(int i=0; i<eq_old->num_entries(); i++){
								if(i == c)
									sub->set(i, 0);
								else
									sub->set(i, -eq_old->get(i));
							}
							sub->set(eq_old->num_entries(), constant);
						}
						else
						{
							for(int i=0; i<eq_old->num_entries(); i++){
							if(i == c)
								sub->set(i, 0);
							else
								sub->set(i, eq_old->get(i));
						}
						sub->set(eq_old->num_entries(), -constant);
						}
						index_to_sub[c] = sub;
						substitution_order.push_back(c);

						break;
					}
				}
				if(!remove) continue;
				progress = true;
				break;
			}
			if(!progress) break;
			remove(eq_old);
			remove(neq_old);
			eliminate_var(eliminate_index, sub);
		}
		//update mappings
		int old_size = num_vars();
		vars.clear();
		int cur = 0;


		for(int i=0; i < old_size; i++) {
			if(index_to_sub.count(i) == 0){
				vars.push_back(original_vars[i]);
				old_to_new_vars[i] = cur++;

			}
			else {
				old_to_new_vars[i] = -1;

			}
		}
		map<Equation*, bignum> temp_map;
		iterator it = begin();
		for(; it!= end(); it++) {
			temp_map[it->first] = it->second;
		}

		equations.clear();
		ordered_eqs.clear();
		eq_to_time.clear();
		int new_eq_size = vars.size();



		map<Equation*, bignum>::iterator it2 = temp_map.begin();
		for(; it2!= temp_map.end(); it2++) {
			Equation* eq = it2->first;
			bignum constant = it2->second;
			Equation* new_eq = new Equation(new_eq_size);
			int cur = 0;


			for(int i=0; i < eq->num_entries(); i++) {
				if(old_to_new_vars[i]==-1){
					continue;
				}

				new_eq->set(cur++, eq->get(i));
			}

			insert(new_eq, constant);
			delete eq;
		}

		if(neq_constraints != NULL) {
			set<int> cols_to_remove;
			cols_to_remove.insert(substitution_order.begin(),
					substitution_order.end());





			set< set< pair<Equation*, bignum> > > result_neq;
			set< set< pair<Equation*, bignum> > >::iterator it =
					neq_constraints->begin();
			for(; it!= neq_constraints->end(); it++) {
				set<pair<Equation*, bignum> >::iterator it2 = it->begin();
				set<pair<Equation*, bignum> > cur_disjunctive_ineq;
				for(; it2!= it->end(); it2++)
				{
					Equation* old_eq =it2->first;
					//assert(old_eq->get_cols() == old_size);
					Equation* new_eq = new Equation(vars.size());

					int cur_index = 0;


					for(int i=0; i<old_eq->num_entries(); i++) {
						if(cols_to_remove.count(i) > 0) continue;
						new_eq->set(cur_index, old_eq->get(i));
						cur_index++;
					}
					cur_disjunctive_ineq.insert(pair<Equation*, bignum>(new_eq,
							it2->second));
					delete old_eq;
				}


				result_neq.insert(cur_disjunctive_ineq);

			}

			*neq_constraints = result_neq;
		}
		if(MATRIX_ASSERT) check_consistency();
	}

	inline void adjust_assignments(vector<bigfraction> & assignments,
			vector<bignum>& final_assignments)
	{
		final_assignments.reserve(old_to_new_vars.size());
		map<int, bigfraction> res_assignments;
		map<int, int>::iterator it = old_to_new_vars.begin();
		for(; it != old_to_new_vars.end(); it++)
		{
			int old_index = it->first;
			int new_index = it->second;
			if(new_index == -1) continue; // was eliminated
			res_assignments[old_index] = assignments[new_index];
		}

		for(int i=substitution_order.size()-1; i>=0; i--)
		{
			int old_index = substitution_order[i];
			Equation* sub = index_to_sub[old_index];
			int num_entries = sub->num_entries();
			bigfraction cur = 0;
			for(int j=0; j<num_entries-1; j++)
			{
				bigfraction coef = sub->get(j);
				if(coef == 0) continue;
				assert(res_assignments.count(j) != 0);
				cur += coef*res_assignments[j];
			}

			cur += sub->get(num_entries-1); // add the constant
			res_assignments[old_index] = cur;

		}

		map<int, bigfraction>::iterator it2 = res_assignments.begin();
		for(; it2!= res_assignments.end(); it2++) {
			bigfraction& f = it2->second;
			bignum n = f.get_numerator();
			bignum d = f.get_denominator();
			if(d!=1) {
				cerr << "n: " << n << " d: " << d << endl;
				assert(false);
			}
			final_assignments.push_back(n);
		}

	}

	inline bool var_occurs(int index, Equation* eq1, Equation* eq2)
	{
		iterator it = begin();
		for(; it!= end(); it++)
		{
			Equation* eq = it->first;
			if(eq == eq1 || eq == eq2) continue;
			if(eq->get(index) != 0) return true;
		}
		return false;
	}


	void eliminate_var(int i, Equation* sub)
	{

		map<Equation*, bignum> temp_map;
		iterator it = begin();
		for(; it!= end(); it++) {
			temp_map[it->first] = it->second;
		}
		equations.clear();
		ordered_eqs.clear();
		eq_to_time.clear();

		map<Equation*, bignum>::iterator it2 = temp_map.begin();
		for(; it2!= temp_map.end(); it2++) {
			Equation* eq = it2->first;
			bignum constant = it2->second;
			bignum factor = eq->get(i);
			if(factor == 0){
				insert(eq, constant);
				continue;
			}
			for(int c=0; c<eq->num_entries(); c++) {
				bignum val = 0;
				if(c != i)
					val = eq->get(c);
				eq->set(c, val+sub->get(c)*factor);
			}
			constant-=sub->get(eq->num_entries())*factor;
			insert(eq, constant);
		}

		if(MATRIX_ASSERT) check_consistency();
	}


	inline void mark_current_facets(vector<bigfraction>& assignments)
	{
		eq_map::iterator it = equations.begin();
		for(; it!= equations.end(); it++)
		{
			Equation* eq = it->first;
			bignum constant = it->second;
			bigfraction lhs = eq->evaluate(assignments);
			if(lhs != constant) ignored.insert(eq);
		}
	}

	inline void clear_current_facets()
	{
		ignored.clear();
	}
};

#endif /* BIG_MATRIX_H_ */

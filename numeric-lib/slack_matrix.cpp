/*
 * slack_matrix.cpp
 *
 *  Created on: Dec 8, 2008
 *      Author: isil
 */

#include "slack_matrix.h"
#include <set>
using namespace std;

slack_matrix::slack_matrix(Matrix & m):
	orig_vars(m.get_vars())
{
	init_geqz_constraints(m);
	num_slack_vars = 1+m.size();
	num_vars = m.num_vars() + num_slack_vars;
	assert(m.size() >= 0);
	num_rows = m.size() +1;
	construct_index_mapping(m);
	sm = new matrix(num_rows, num_vars, NULL);
	populate_slack_matrix(m);
}

slack_matrix::slack_matrix(slack_matrix & m):orig_vars(m.orig_vars)
{
	sm = new matrix(*m.sm);
	num_vars = m.num_vars;
	num_slack_vars = m.num_slack_vars;
	num_rows = m.num_rows;
	index_mapping = new int[orig_vars.size()];
	memcpy(index_mapping, m.index_mapping, orig_vars.size()*sizeof(int));
	reverse_index_mapping = new int[num_vars];
	memcpy(reverse_index_mapping, m.reverse_index_mapping,
			num_vars*sizeof(int));
	geqz_constraints = new bool[orig_vars.size()];
	memcpy(geqz_constraints, m.geqz_constraints, orig_vars.size()*
			sizeof(bool));
}

string slack_matrix::get_name(int c)
{
	if(c<num_slack_vars) return "s"+int_to_string(c);
	int cc = get_principal_var(c);
	string name = orig_vars[reverse_index_mapping[cc]];
	if(is_primed_var(c)) name += "'";
	return name;
}

string slack_matrix::to_string()
{
	string res;
	for(int i=0; i < num_vars; i++)
	{
		if(i<num_slack_vars) {
			res+="s";
			append(i, res);
			res+="\t";
		}
		else {
			res += orig_vars[reverse_index_mapping[i]] + "\t";
			if(geqz_constraints[reverse_index_mapping[i]]) {
				continue;
			}
			res += orig_vars[reverse_index_mapping[i]] + "'" + "\t";
			i++;
		}
	}
	res+="[c]\t[p]\n";
	res+=sm->to_string();
	return res;

}

slack_matrix::~slack_matrix()
{
	delete sm;
	delete [] index_mapping;
	delete [] reverse_index_mapping;
		delete [] geqz_constraints;
}
// -----------Private methods ------------------//
void slack_matrix::populate_slack_matrix(Matrix& m)
{
	/*
	 * If the initial system is Ax <= b,
	 * the slack matrix will contain it in the form
	 * -x0 + y +Ax -b
	 * and the last row is the objective function, initially -x0.
	 */
	Matrix::iterator it = m.begin();
	int last = m.size()-1;

	/*
	vector<int> rows;
	std::set<int> used;
	for(int i=0; i <= last; i++)
	{
		int cur = rand()%(last+1);
		while(used.count(cur) > 0){
			cur++;
			cur = cur%(last+1);
		}
		used.insert(cur);
		rows.push_back(cur);

	}
	*/

	int r = 0;
	int i = 0;
	for(; it!=m.end(); it++, r++, i++)
	{
		r = i;//rows[i];
		// s0 entry is initially -1 for all rows
		sm->set(r, 0, -1);

		// In row r, set the corresponding slack variable to 1.
		sm->set(r, i+1, 1);

		Equation *eq = it->first;
		for(int c=0; c < eq->num_entries(); c++) {
			int start_index = index_mapping[c];
			bignum coef = eq->get(c);
			sm->set(r, start_index, coef);


			/* Figure out whether we needed to split
			 * x as x1-x2 for missing non-negative constraints
			 */
			if(geqz_constraints[c]) continue;
			sm->set(r, start_index+1, -coef);
		}
		//Deal with original constant
		sm->set_constant(r, -it->second);

		//Fill last slot with index of pivot variable for this row
		sm->set_pivot(r, i+1);

	}
	/*
	 *  Populate objective function row: Initially we want
	 *  to maximize -x0
	 */
	sm->set(last+1, 0, -1);
}


void slack_matrix::construct_index_mapping(Matrix& m)
{
	// shift indicates how much we need to add to a variable index
	// in the original matrix to find its position in slack form matrix.
	int shift = num_slack_vars;

	index_mapping = new int[m.num_vars()];
	reverse_index_mapping = new int[2*num_vars];
	memset(reverse_index_mapping, ~0, sizeof(int)*2*num_vars);

	for(int c=0; c<m.num_vars(); c++) {
		index_mapping[c]=c+shift;

		reverse_index_mapping[c+shift] = c;
		if(!geqz_constraints[c]){
			++num_vars;
			++shift;
		}

	}
}


void slack_matrix::init_geqz_constraints(Matrix& m)
{
	geqz_constraints = new bool[m.num_vars()];
	memset(geqz_constraints, 0, m.num_vars()*sizeof(bool));
	Matrix::iterator it = m.begin();
	for(; it!= m.end(); it++)
	{
		bignum constant = it->second;
		if(constant > 0) continue;

		int index = -1;
		Equation* eq = it->first;
		for(int c=0; c<eq->num_entries(); c++)
		{
			bignum e = eq->get(c);
			if(e > 0){
				index = -1;
				break;
			}
			else if(e<0 && index != -1)
			{
				index = -1;
				break;
			}
			else if(e<0)
				index = c;
		}
		// Mark entry as 1 if var has non-negativity constraint
		if(index != -1)
			geqz_constraints[index] = true;

	}

}

void slack_matrix::append(long int i, string & s)
{
	char temp[100];
	sprintf(temp, "%ld",  i);
	s.append(temp);
}

string slack_matrix::int_to_string(long int i)
{
	char temp[100];
	sprintf(temp, "%ld",  i);
	string s;
	s.append(temp);
	return s;
}

ostream& operator <<(ostream &os,const slack_matrix &_obj)
{
	slack_matrix & obj = (slack_matrix&) _obj;
    os << obj.to_string();
    return os;
}

/*
 * UnsatCoreFinder.cpp
 *
 *  Created on: Jun 24, 2009
 *      Author: isil
 */

#include "UnsatCoreFinder.h"
#include "assert.h"
#include "cnode.h"
#include "Solver.h"

#define STATS false


UnsatCoreFinder::UnsatCoreFinder(CNode* c, set<CNode*>& must_assignments):
	must_assignments(must_assignments)
{

	this->orig_node = c;

	/*
	 * Remove must assignments from c.
	 */
	assert(c->get_type() == AND);
	Connective* and_c = (Connective*)c;
	const set<CNode*>& children = and_c->get_operands();
	set<CNode*> new_children;
	set<CNode*>::const_iterator it = children.begin();
	for(; it!= children.end(); it++) {
		CNode* child = *it;
		if(must_assignments.count(child) > 0) continue;
		new_children.insert(child);
	}
	CNode* must_c = Connective::make_and(must_assignments);
	if(new_children.size() == 0)
	{
		unsat_core =  must_c;
		return;
	}

	CNode* simp_c = Connective::make_and(new_children);



	must_c = find_unsat_core(simp_c, must_c);


	num_queries = 0;
	most_difficult_clause = NULL;
	diff_clause_time = 0;
	total_time = 0;

	int start = clock();
	//unsat_core = find_unsat_core(True::make(), orig_node);
	unsat_core = find_unsat_core(must_c, simp_c);
	unsat_core = Connective::make(AND, unsat_core, must_c);
	total_time = clock()-start;

	if(STATS) {
		double total = ((double)total_time)/((double)CLOCKS_PER_SEC);
		if(total > 0.05) {
			cout << "Unsat core finder for: " << c->to_string() << endl;
			cout << "Total time: " <<  total
					<< endl;
			cout << "Number of clauses solved: " << num_queries << endl;
			double most_diff_time = ((double)diff_clause_time)/((double)CLOCKS_PER_SEC);
			if(most_diff_time > 0.01) {
				cout << "Time to solve most difficult clause: " <<
						most_diff_time << endl;
				cout << "Most difficult clause: " << most_difficult_clause->to_string() << endl;
			}

			cout << "Unsat core: " << unsat_core->to_string() << endl;
		}

	}
}

CNode* UnsatCoreFinder::get_unsat_core()
{
	return unsat_core;
}

void UnsatCoreFinder::begin_query()
{
	num_queries++;
	start_time = clock();
}
void UnsatCoreFinder::end_query(CNode* clause)
{
	int cur_time = clock()-start_time;
	if(cur_time > diff_clause_time) {
		diff_clause_time = cur_time;
		most_difficult_clause = clause;
	}
}

CNode* UnsatCoreFinder::find_unsat_core(CNode* assumption, CNode* in_c)
{


	//cout << "FInding unsat core: " << in_c->to_string() << endl;
	if(in_c->is_literal()) return in_c;
	assert(in_c->get_type() == AND);
	Connective* c = (Connective*) in_c;
	const set<CNode*>& children = c->get_operands();
	int num_children = children.size();
	int half = num_children/2;

	/*
	 * Split clause in two equal parts, c1 and c2
	 */
	set<CNode*> half1;
	set<CNode*> half2;

	set<CNode*>::iterator it = children.begin();
	for(int i=0; it!= children.end(); it++, i++)
	{

		if(i<half) half1.insert(*it);
		else half2.insert(*it);

	}

	CNode* c1 = Connective::make_and(half1);
	CNode* c2 = Connective::make_and(half2);

	CNode* assumption1 = assumption;//Solver::get_relevant_background(assumption, c1);

	/*
	 * Invoke clause solve on each part
	 */
	CNode* c1_query = Connective::make(AND, c1, assumption1);

	if(STATS) begin_query();
	ClauseSolve s1(c1_query, NULL);
	if(STATS) end_query(c1_query);

	bool res1 = s1.is_sat();

	// c1 is unsat on its own, so we don't need to
	// do anything with c2.
	if(!res1)
	{
		CNode* c1_core = find_unsat_core(assumption1, c1);
		return c1_core;
	}


	// see if c2 is unsat on its own
	CNode* assumption2 = assumption;//Solver::get_relevant_background(assumption, c2);
	CNode* c2_query = Connective::make(AND, c2, assumption2);

	if(STATS) begin_query();
	ClauseSolve s2(c2_query, NULL);
	if(STATS) end_query(c2_query);
	bool res2 = s2.is_sat();
	if(!res2)
	{
		return find_unsat_core(assumption2, c2);
	}

	/*
	 * Bad case: Both c1 and c2 are SAT on their own,
	 * but UNSAT together. Minimize c1 assuming c2, and
	 * minimize c2 assuming c1, then combine.
	 */
	set<CNode*> c1_set;
	c1_set.insert(assumption1);
	c1_set.insert(c2);
	CNode* c1_assumption = Connective::make_and(c1_set);
	CNode* c1_core = find_unsat_core(c1_assumption, c1);


	set<CNode*> c2_set;
	c2_set.insert(assumption2);
	c2_set.insert(c1_core);
	CNode* c2_assumption = Connective::make_and(c2_set);
	CNode* c2_core = find_unsat_core(c2_assumption, c2);

	set<CNode*> final_set;
	final_set.insert(c1_core);
	final_set.insert(c2_core);

	CNode* final_core = Connective::make_and(final_set);
	assert(final_core->get_type() != FALSE_NODE);
	return final_core;

}

UnsatCoreFinder::~UnsatCoreFinder() {
	// TODO Auto-generated destructor stub
}

/*
 * UnsatCoreFinder.h
 *
 *  Created on: Jun 24, 2009
 *      Author: isil
 */

#ifndef UNSATCOREFINDER_H_
#define UNSATCOREFINDER_H_

class CNode;

#include <set>
using namespace std;

class UnsatCoreFinder {
private:
	CNode* orig_node;
	CNode* unsat_core;

	int num_queries;
	CNode* most_difficult_clause;
	int diff_clause_time;
	int total_time;

	int start_time;

	/*
	 * The set of literals whose truth assignments
	 * are already fixed. We keep track of these because
	 * we don't want to take these into account when minimizing.
	 * For example, suppose we have the clause whose
	 * boolean abstraction is B1 & !B2 & B3
	 * If B1 *must* be assigned to true,
	 * then we want to minimize !B2 & B3, taking B1
	 * into account when making the clause_sat query.
	 */
	const set<CNode*>& must_assignments;

public:
	UnsatCoreFinder(CNode* c, set<CNode*>& must_assignments);
	CNode* get_unsat_core();
	virtual ~UnsatCoreFinder();
private:
	CNode* find_unsat_core(CNode* assumption, CNode* c);
	void begin_query();
	void end_query(CNode* clause);
};

#endif /* UNSATCOREFINDER_H_ */

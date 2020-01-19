/*
 * ConflictDatabase.h
 *
 *  Created on: Jan 26, 2010
 *      Author: isil
 */

#ifndef CONFLICTDATABASE_H_
#define CONFLICTDATABASE_H_
#include <set>
#include <map>
#include <unordered_set>
using namespace std;

class CNode;
class Leaf;
struct DBLeaf;
struct DBClause;

struct DBLeaf
{
	Leaf* l;
	set<DBClause*> conflict_clauses; // the set of all conflict clauses in
									// which this leaf appears

	DBLeaf(Leaf* l, DBClause* cl);
};

struct DBClause
{
	CNode* conflict_clause;
	set<CNode*> leaves; // the set of all leaves in this clause

	DBClause(CNode* cl, set<CNode*>& l);
};

class ConflictDatabase
{
private:
	static map<Leaf*, DBLeaf*> db_leaves;
	static set<CNode*> conflict_clauses;

public:
	ConflictDatabase();
	/*
	 * Adds a conflict clause to the library
	 */
	static void add_conflict_clause(CNode* conflict_clause);

	/*
	 * Gives the set of all conflict clauses relevant to the formula
	 * currently being solved/simplified.
	 */
	static void get_conflict_clauses(CNode* formula,
			set<CNode*>& conflict_clauses);

	static void clear();

	static void print_conflict_clauses();

	~ConflictDatabase();
};


#endif /* CONFLICTDATABASE_H_ */

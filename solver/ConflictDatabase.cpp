/*
 * ConflictDatabase.cpp
 *
 *  Created on: Jan 26, 2010
 *      Author: tdillig
 */

#include "ConflictDatabase.h"
#include "CNode.h"
#include "Leaf.h"

map<Leaf*, DBLeaf*> ConflictDatabase::db_leaves;
set<CNode*> ConflictDatabase::conflict_clauses;


DBLeaf::DBLeaf(Leaf* l, DBClause* cl)
{
	this->l = l;
	this->conflict_clauses.insert(cl);
}

DBClause::DBClause(CNode* clause, set<CNode*>& leaves)
{
	this->conflict_clause = clause;
	this->leaves = leaves;
}


ConflictDatabase::ConflictDatabase()
{


}

/*
 * Adds a conflict clause to the library
 */
void ConflictDatabase::add_conflict_clause(CNode* conflict_clause)
{

	// Check if this is already in the library
	if(conflict_clauses.count(conflict_clause) > 0) return;
	conflict_clauses.insert(conflict_clause);

	set<CNode*> leaves;
	conflict_clause->get_all_leaves(leaves);

	DBClause* new_conflict = new DBClause(conflict_clause, leaves);


	set<CNode*>::iterator it = leaves.begin();
	for(; it!= leaves.end(); it++)
	{
		Leaf* l = (Leaf*) *it;
		if(db_leaves.count(l) == 0)
		{
			DBLeaf* new_leaf = new DBLeaf(l, new_conflict);
			db_leaves[l] = new_leaf;
		}
		else {
			DBLeaf* existing_leaf = db_leaves[l];
			existing_leaf->conflict_clauses.insert(new_conflict);
		}
	}

}


/*
 * Gives the set of all conflict clauses relevant to the formula
 * currently being solved/simplified.
 */
void ConflictDatabase::get_conflict_clauses(CNode* formula,
		set<CNode*>& conflict_clauses)
{
	// First get the set of leaves used in the formula
	set<CNode*> relevant_leaves;
	formula->get_all_leaves(relevant_leaves);

	set<DBClause*> processed;
	set<CNode*>::iterator it = relevant_leaves.begin();
	for(; it!= relevant_leaves.end(); it++)
	{
		Leaf* l = (Leaf*) *it;
		if(db_leaves.count(l) == 0) continue;
		DBLeaf* db_leaf = db_leaves[l];

		// Get the conflict clauses in which this leaf appears
		set<DBClause*>& clauses_with_leaf = db_leaf->conflict_clauses;
		set<DBClause*>::iterator it2 = clauses_with_leaf.begin();
		for(; it2!= clauses_with_leaf.end(); it2++)
		{
			DBClause* cur_clause = *it2;
			if(processed.count(cur_clause) > 0) continue;
			processed.insert(cur_clause);

			set<CNode*>& clause_leaves = cur_clause->leaves;

			// If the set of leaves contained in this clause is a subset of
			// the leaves in the current formula,then include this conflict clause
			bool include_clause = true;
			set<CNode*>::iterator it3 = clause_leaves.begin();
			for(; it3!= clause_leaves.end(); it3++)
			{
				CNode* cur_clause_leaf = *it3;
				if(relevant_leaves.count(cur_clause_leaf) == 0) {
					include_clause = false;
					break;
				}
			}

			if(include_clause) {
				conflict_clauses.insert(cur_clause->conflict_clause);
			}

		}

	}
	/*cout << "Got conflict clauses for: " << formula->to_string() << endl;
	{
		set<CNode*>::iterator it = conflict_clauses.begin();
		for(; it != conflict_clauses.end(); it++)
		{
			cout << "\t" << (*it)->to_string() << endl;
		}
	}*/

}

void ConflictDatabase::clear()
{
	set<DBClause*> to_delete;
	map<Leaf*, DBLeaf*>::iterator it = db_leaves.begin();
	for(; it!= db_leaves.end(); it++)
	{
		DBLeaf* db_leaf = it->second;
		to_delete.insert(db_leaf->conflict_clauses.begin(),
				db_leaf->conflict_clauses.end());
		delete db_leaf;
	}

	set<DBClause*>::iterator it2 = to_delete.begin();
	for(; it2!= to_delete.end(); it2++)
	{
		delete *it2;
	}

	conflict_clauses.clear();
	db_leaves.clear();

}

void ConflictDatabase::print_conflict_clauses()
{
	cout << "====== LEARNED CONFLICTS CLAUSES ==== " << endl;
	set<DBClause*> conflicts;
	map<Leaf*, DBLeaf*>::iterator it = db_leaves.begin();
	for(; it!= db_leaves.end(); it++)
	{
		DBLeaf* db_leaf = it->second;
		conflicts.insert(db_leaf->conflict_clauses.begin(),
						db_leaf->conflict_clauses.end());
	}

	set<DBClause*>::iterator it2 = conflicts.begin();
	for(; it2!= conflicts.end(); it2++)
	{
		DBClause* c = *it2;
		cout << "\t " << c->conflict_clause->to_string() << endl;
	}
	cout << "======================================" << endl;
}

ConflictDatabase::~ConflictDatabase()
{

}

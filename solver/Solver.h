/*
 * Solver.h
 *
 *  Created on: Sep 5, 2008
 *      Author: tdillig
 */

#ifndef SOLVER_H_
#define SOLVER_H_
#include <set>
#include <vector>
#include <map>
using namespace std;
#include "InteractionManager.h"
#include "util.h"


class CNode;
class VarMap;
class NormalForm;
class Clause;
class Term;
class ILPLeaf;
class EqLeaf;
class Leaf;
class FunctionTerm;
class Matrix;
class Equation;
class Connective;

#include "bignum.h"
#include "ClauseSolve.h"
#include "SatSolver.h"
#include "Vec.h"


class Solver {

	 friend class InteractionManager;
	 friend class QueryComparator;
	 friend class ClauseSolve;
	 friend class VariableEliminator;
protected:

	int fresh_var_counter;
	int solve_count;
	int literal_count;
	int clause_cache_hit_count;
	int cache_hits;
	int solve_time;
	int imply_time;
	int num_imply;
	CNode* res;
public:
	Solver(CNode* node, simplification_level level,
			map<Term*, SatValue>* assignments = NULL,
			bool use_dnf = false);

	Solver(CNode* node, CNode* assumptions, simplification_level level,
			map<Term*, SatValue>* assignments = NULL);

	CNode* solve(CNode* node, CNode* assumptions, simplification_level level,
			map<Term*, SatValue>* assignments);

	static bool implies(CNode* node1, CNode* node2);
	static bool equivalent(CNode* node1, CNode* node2);

	/*
	 * Slices out parts of the assumptions that are irrelevant for simplifying
	 * the formula.
	 */
	static CNode* get_relevant_background(CNode* background,
			CNode* formula_to_simplify);


	/*
	 * Node is SAT if and only if the type of the result node is
	 * not FALSE_NODE.
	 */
	CNode* get_result();
	string get_stats();
	virtual ~Solver();



protected:
	Solver();





	/*
	* Preprocesses equalities.
	*/
   CNode* propagate_equalities(CNode* node, CNode*& active_constraint);

   inline void add_to_replacement_map(Term* to_replace, Term* replacement,
		   map<Term*, Term*>& replacement_map);

private:
   bool dnf_solve(CNode* node, map<Term*, SatValue>* assignments = NULL,
   				bool verbose = false, bool ilp_only = false);
	bool sat_solve(CNode* node);



	static CNode* get_relevant_background_internal(CNode* background, set<Term*>&
			relevant_vars);

	static bool get_related_vars(CNode* node, set<Term*>& vars);

	void collect_constraint(CNode* node, bool sat, const string & path);



};

#endif /* SOLVER_H_ */

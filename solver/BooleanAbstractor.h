/*
 * BooleanAbstractor.h
 *
 *  Created on: Jul 25, 2009
 *      Author: tdillig
 */

#ifndef BOOLEANABSTRACTOR_H_
#define BOOLEANABSTRACTOR_H_

#include <map>
using namespace std;


class CNode;
class Leaf;
class BooleanVar;


#include "CNF.h"
#include "SatSolver.h"
#include "Term.h"


/*
 * Constructs the boolean skeleton of the given SMT formula to be fed to
 * the SAT solver.
 */

class BooleanAbstractor {

private:

	CNode* original;

	enum edge_op
	{
		EDGEOP_NOOP = 0,
		EDGEOP_EQ = 1,
		EDGEOP_NEQ = 2,
		EDGEOP_LT = 4,
		EDGEOP_LEQ = 8
	};

	struct edge;
	struct node;

	struct node
	{
		Term* t;
		set<edge*> outgoing_edges;
		set<edge*> incoming_edges;

		node(Term* t)
		{
			this->t = t;
		}

		string to_string()
		{
			return t->to_string();
		}
	};

	struct edge
	{
		node* source;
		node* target;
		edge_op op;

		edge(node* source, node* target, edge_op op)
		{
			this->source = source;
			this->target = target;
			this->op = op;
			source->outgoing_edges.insert(this);
			target->incoming_edges.insert(this);
		}

		string to_string()
		{
			return source->t->to_string() + " -> " + target->t->to_string();

		}

		string to_string(edge_op op)
		{
			string op_string = "";
			if(op == EDGEOP_LT) op_string = "<";
			else if(op == EDGEOP_LEQ) op_string = "<=";
			else if(op == EDGEOP_EQ) op_string = "=";
			else op_string = "!=";
			return source->t->to_string() + op_string + target->t->to_string();

		}

		~edge()
		{
			source->outgoing_edges.erase(this);
			target->incoming_edges.erase(this);
		}

	};

	map<Term*, node*> term_to_node_map;

	/*
	 * A node is a frontier node if either a) it has no outgoing edge
	 * or b) it has no incoming edges or c)it has one incoming and one
	 * outgoing edge from/to the same node.
	 */
	set<node*> frontier_nodes;

	/*
	 * A representation of simple equality and inequality (=, <, <=, !=)
	 * relations between pairs of terms.
	 */
	set<edge*> relation_graph;

	/*edge_op
	 * We collect all used constants in order to add
	 * disequality edges between them.
	 */
	set<Term*> used_constants;
	map<pair<node*, node*>, edge*> edge_matrix;

	/*
	 * The set of all literals used in the formula.
	 */
	set<CNode*> literals;

	/*
	 * The set of relevant implications we should add to the boolean abstraction.
	 */
	set<CNode*> valid_implications;

	/*
	 * All learned implications
	 */
	CNode* learned;


	int max_implications;


public:
	BooleanAbstractor(CNode* node);
	CNode* get_learned_implications();
	~BooleanAbstractor();

private:
	node* get_node_from_term(Term* t);
	void build_relation_graph();
	void add_edge(Term* source, Term* target, edge_op op,
			bool add_used_constant = true);
	void add_edge(node* source, node* target, edge_op op,
			set<edge*>* added_edges = NULL);
	string relation_graph_to_dotty();

	bool is_frontier_node(node* n);
	bool is_frontier_node(node* n, set<edge*> & processed_edges);

	void add_initial_frontier_nodes();

	/*
	 * By basic implications, we mean implications of the form
	 * a > b-> a>=b, a>b->a!=b etc. If L1 and L2 are literals present in
	 * the original formula and there is an implication relation between
	 * them, then we add this implication to the formula.
	 */
	void add_basic_implications();

	/*
	 * Adds constraints of the form
	 * x=1 -> x!=2 & x<= 3 & x<4.... etc.
	 * if these literals exist in the
	 * formula.
	 */
	void add_constant_relations();

	/*
	 * Adds the implication prec -> concl if either the conclusion
	 * or its negation is present in the set of literals present in the
	 * original formula.
	 */
	void add_implication(CNode* prec, CNode* concl);



	/*
	 * Makes the relation graph chordal so the number of cycles we have
	 * to consider is cubic rather than exponential in the number of nodes.
	 */
	void make_chordal();

	/*
	 * Adds an edge between the source of in and the target of out
	 * and adds the new edge to the set of processed edges.
	 */
	void wire_edge(edge* in, edge* out, set<edge*>& processed_edges);

	/*
	 * Given the chordal relation graph, this function adds all
	 * relevant implications.
	 */
	void add_implications();

	/*
	 * Is there any edge between n1 and n2, disregarding direction of the edges?
	 */
	inline bool edge_between(node* n1, node* n2);


	/*
	 * Given a op1 b and b op2 c, can we deduce a < c?
	 */
	bool deduce_lt(edge_op op1, edge_op op2);

	/*
	 * Given a op1 b and b op2 c, can we deduce a <= c?
	 */
	bool deduce_leq(edge_op op1, edge_op op2);

	/*
	 * Given a op1 b and b op2 c, can we deduce a = c?
	 */
	bool deduce_eq(edge_op op1, edge_op op2);

	/*
	 * Given op1 and op2, can we deduce the op called ded_op?
	 * e.g. > and = can deduce > and >=.
	 */
	bool deduce_op(edge_op op1, edge_op op2, edge_op ded_op);

	/*
	 * Is the given deduction relevant?
	 */
	bool is_relevant_deduction(node* source, node* target, edge_op op);

	/*
	 * Adds the implication e1 & e2 -> deduction.
	 */
	void add_implication(edge* e1, edge* e2, CNode* deduction, edge_op op);

	/*
	 * Gives the literal representation of this edge.
	 */
	CNode* edge_to_literal(edge* e, edge_op op);

};

#endif /* BOOLEANABSTRACTOR_H_ */

/*
 * BooleanAbstractor.cpp
 *
 *  Created on: Jul 25, 2009
 *      Author: tdillig
 */

#include "BooleanAbstractor.h"
#include "cnode.h"
#include "term.h"
#include <assert.h>
#include "util.h"
#include "ClauseSolve.h"

/*
 * Should we add != edges between constants?
 * This has the disadvantage of yielding too many pairwise
 * disjointness constraints if there are a large number of constants.
 */
#define ADD_CONSTANT_DISEQUALITIES false

/*
 * Abstraction type specifies how we want to construct the initial
 * boolean skeleton of the original SMT formula.
 * BASIC just constructs a boolean formula, treating each leaf L as a boolean
 * variable b, and !L as !b.
 * EQ_AXIOMS also adds theory of equality axioms, i.e., if a=b, b=c, and a=c
 * appear as leaves, we add the implication ( B(a=b) & B(b=c) -> B(a=c)) etc.
 * EQ_LT_AXIOMS adds all equality axioms and in addition also adds transitivity
 * constraints due to <, <=, >, and >=. For instance, if a < b, b<c, and a<c
 * appear as leaves, we add the implication B(a<b) & B(b<c) -> B(a<c).
 */
enum abstraction_type
{
	BASIC,
	EQ_AXIOMS,
	EQ_LT_AXIOMS
};

#define ABSTRACTION EQ_LT_AXIOMS


#define DEBUG false

BooleanAbstractor::BooleanAbstractor(CNode* node)
{
	int start = clock();
	this->original = node;
	max_implications = node->get_size()/10+5;

	if(ABSTRACTION == BASIC){

		return;
	}
	original->get_all_literals(literals);
	add_basic_implications();
	build_relation_graph();

	if(DEBUG) {
		cout << "*************BEGIN DOTTY**************** " << endl;
		cout << relation_graph_to_dotty() << endl;
		cout << "*************END DOTTY**************** " << endl;
	}


	add_initial_frontier_nodes();
	make_chordal();

	if(DEBUG) {
		cout << "*************BEGIN DOTTY chordal**************** " << endl;
		cout << relation_graph_to_dotty() << endl;
		cout << "*************END DOTTY chordal **************** " << endl;
	}


	add_implications();

	if(!ADD_CONSTANT_DISEQUALITIES)
		add_constant_relations();
	if(DEBUG)
	{
		cout << "*********DEDUCED IMPLICATIONS***********" << endl;
		set<CNode*>::iterator it = valid_implications.begin();
		for(; it != valid_implications.end(); it++)
		{
			CNode* imp = *it;
			cout << "\t " << imp->to_string() << endl;
		}
		cout << "**************END***************" << endl;
	}

	learned = Connective::make_and(valid_implications);

	/*
	 * Just for debugging!
	 */

	/*{
		set<CNode*>::iterator it = valid_implications.begin();
		for(; it!= valid_implications.end(); it++)
		{
			CNode* imp = *it;
			CNode* not_imp = Connective::make_not(imp);
			ClauseSolve cs(not_imp, NULL);
			bool res = cs.is_sat();
			if(res) {
				cout << "Implication not valid: " << imp->to_string() << endl;
				assert(false);
			}

		}
	}*/

	if(DEBUG) {
		int end = clock();
		cout << "Time in Boolean Abstractor: " <<
		((double)(end-start))/((double)CLOCKS_PER_SEC) << endl;
		cout << "Learned implications: " << learned->to_string() << endl;
		cout << "Size of set " << valid_implications.size() << endl;
		cout << "Size of constraint" << node->get_size() << endl;
	}



}

CNode* BooleanAbstractor::get_learned_implications()
{
	return learned;
}

/*
 * Adds constraints of the form
 * x=1 -> x!=2 & x<= 3 & x<4.... etc.
 * if these literals exist in the
 * formula.
 */
void BooleanAbstractor::add_constant_relations()
{
	map<Term*, node*>::iterator it = term_to_node_map.begin();
	for(; it!= term_to_node_map.end(); it++)
	{
		Term* t = it->first;
		if(t->get_term_type() != CONSTANT_TERM) continue;
		long int cur_constant = ((ConstantTerm*) t)->get_constant();
		node* n = it->second;
		set<edge*>::iterator incoming_it = n->incoming_edges.begin();
		for(; incoming_it!=n->incoming_edges.end(); incoming_it++)
		{
			edge* e = *incoming_it;
			if(!e->op & EDGEOP_EQ && !e->op & EDGEOP_NEQ) continue;

			node* source = e->source;
			Term* source_t = source->t;
			set<Term*> constant_targets;

			set<pair<Term*, pair<edge_op, bool> > > implications;

			set<edge*>::iterator outgoing_it = source->outgoing_edges.begin();
			for(; outgoing_it != source->outgoing_edges.end(); outgoing_it++)
			{

				if((int)valid_implications.size() > max_implications) return;
				edge* out_e = *outgoing_it;

				bool diseq_relevant =
						(out_e->op & EDGEOP_EQ || out_e->op & EDGEOP_NEQ);

				bool lt_relevant = (out_e->op & EDGEOP_LT);
				bool leq_relevant = (out_e->op & EDGEOP_LEQ);

				node* target  = out_e->target;
				if(target->t == t) continue;

				if(target->t->get_term_type() != CONSTANT_TERM) continue;

				if(diseq_relevant) {
					implications.insert(make_pair(target->t,
							make_pair(EDGEOP_NEQ, true)));
				}

				ConstantTerm* ct = (ConstantTerm*) target->t;
				long int other_constant = ct->get_constant();

				if(other_constant > cur_constant)
				{
					if(lt_relevant) {
						implications.insert(make_pair(target->t,
								make_pair(EDGEOP_LT, true)));
					}
					else if(leq_relevant) {
						implications.insert(make_pair(target->t,
								make_pair(EDGEOP_LEQ, true)));
					}
				}

				else {
					if(leq_relevant) {
						implications.insert(make_pair(target->t,
								make_pair(EDGEOP_LEQ, false)));
					}
					else if(lt_relevant) {
						implications.insert(make_pair(target->t,
								make_pair(EDGEOP_LT, false)));

					}
				}
			}
			CNode* prec = EqLeaf::make(source_t, t);

			set<CNode*> conclusion_set;
			set<pair<Term*, pair<edge_op, bool> > >::iterator constant_it =
				implications.begin();
			for(; constant_it != implications.end(); constant_it++)
			{
				Term* constant_t = constant_it->first;
				edge_op op = constant_it->second.first;
				bool pos = constant_it->second.second;

				if(op == EDGEOP_NEQ)
				{
					CNode* l = EqLeaf::make(source_t, constant_t);
					l = Connective::make_not(l);
					conclusion_set.insert(l);
					//cout << "Adding implication: " << prec->to_string() <<
						//"->" << l->to_string() << endl;

				}

				else
				{

					CNode* l = ILPLeaf::make(source_t, constant_t,
							(op == EDGEOP_LT ? ILP_LT : ILP_LEQ));
					if(!pos) {
						l = Connective::make_not(l);
					}
					conclusion_set.insert(l);
					//cout << "Adding implication: " << prec->to_string() << "->" <<
						//l->to_string() << endl;
				}




			}

			CNode* not_prec = Connective::make_not(prec);
			CNode* conclusion = Connective::make_and(conclusion_set);
			CNode* disjoint_c = Connective::make(OR, not_prec, conclusion);
			valid_implications.insert(disjoint_c);


		}




	}
}



BooleanAbstractor::~BooleanAbstractor()
{

}

BooleanAbstractor::node* BooleanAbstractor::get_node_from_term(Term* t)
{
	if(term_to_node_map.count(t) > 0) return term_to_node_map[t];
	node* n = new node(t);
	term_to_node_map[t] = n;
	return n;
}

void BooleanAbstractor::add_basic_implications()
{
	set<CNode*>::iterator it = literals.begin();
	for(; it!= literals.end(); it++)
	{
		CNode* lit = *it;
		lit = lit->fold_negated_ilps();
		switch(lit->get_type())
		{
		case EQ:
		{
			// a = b implies a <= b and b<=a
			EqLeaf* eq = (EqLeaf*) lit;
			Term* t1 = eq->get_rhs();
			Term* t2 = eq->get_lhs();
			CNode* ilp1 = ILPLeaf::make(t1, t2, ILP_LEQ);
			add_implication(eq, ilp1);

			CNode* ilp2 = ILPLeaf::make(t2, t1, ILP_LEQ);
			add_implication(eq, ilp2);
			break;

		}
		case ILP:
		{
			ILPLeaf* ilp = (ILPLeaf*) lit;
			if(ilp->get_operator() == ILP_EQ)
			{
				Term* t = ArithmeticTerm::make(ilp->get_elems(), 0);
				CNode* ilp1 = ILPLeaf::make(t,
						ConstantTerm::make(ilp->get_constant()),
						ILP_LEQ);
				add_implication(ilp, ilp1);
				CNode* ilp2 = ILPLeaf::make(
						ConstantTerm::make(ilp->get_constant()),
						t, ILP_LEQ);
				add_implication(ilp, ilp2);

			}
			break;
		}
		default:
		{
			// add nothing
		}
		}

	}
}

void BooleanAbstractor::add_implication(CNode* premise, CNode* conclusion)
{

	if(literals.count(conclusion) > 0) {
		//cout << "Adding imp: " << premise->to_string() << "->" <<
		//conclusion->to_string();
		CNode* imp = Connective::make(OR, Connective::make_not(premise),
				conclusion);
		valid_implications.insert(imp);
	}
	else {
		CNode* neg_conclusion = Connective::make_not(conclusion);
		if(literals.count(neg_conclusion) > 0) {
			//cout << "Adding imp: " << premise->to_string() << "->" <<
			//		conclusion->to_string();
			CNode* imp = Connective::make(OR, Connective::make_not(premise),
					conclusion);
			valid_implications.insert(imp);
		}
	}
}

void BooleanAbstractor::build_relation_graph()
{


	/*
	{
		cout << "Formula: " << original->to_string() << endl;
		cout << "=========ALL LITERALS=========" << endl;
		set<CNode*>::iterator it = literals.begin();
		for(; it!=literals.end(); it++)
		{
			cout << "\t " << (*it)->to_string() << endl;
		}
		cout << "===============================" << endl;
	}*/


	set<CNode*>::iterator it = literals.begin();
	for(; it!= literals.end(); it++)
	{
		if((int)valid_implications.size() > max_implications) return;
		CNode* literal = *it;
		literal = literal->negations_folded;
		//cout << "Processing literal: " << literal->to_string() << endl;
		cnode_type ct = literal->get_type();
		if(ct == EQ)
		{
			EqLeaf* eq = (EqLeaf*) literal;
			Term* t1 = eq->get_lhs();
			Term* t2 = eq->get_rhs();
			add_edge(t1, t2, EDGEOP_EQ);

		}
		else if(ct == ILP)
		{
			ILPLeaf* ilp = (ILPLeaf*) literal;
			const map<Term*, long int>& terms = ilp->get_elems();

			edge_op op = (ilp->get_operator() == ILP_EQ) ? EDGEOP_EQ :
				EDGEOP_LEQ;



			Term* t1 = ArithmeticTerm::make(terms, 0);
			Term* t2 = ConstantTerm::make(ilp->get_constant());
			if(terms.begin()->second < 0)
			{
				t1 = t1->multiply(-1);
				t2 = t2->multiply(-1);
				add_edge(t2, t1, op);
			}
			else add_edge(t1, t2, op);


			if(ilp->get_operator() == ILP_EQ) continue;


			/*
			 * Special cases:
			 *
			 */
			long int constant = ilp->get_constant();
			if(terms.size() == 2 && (0 == constant || constant == 1 ||
					constant == -1))
			{

				map<Term*, long int>::const_iterator it = terms.begin();
				pair<Term*, long int> p1 = *it;
				it++;
				pair<Term*, long int> p2 = *it;

				/*
				 * We make sure if any term has negative coefficient,
				 * it is the second term.
				 */
				if(p1.second < 0) {
					pair<Term*, long int> t = p1;
					p1 = p2;
					p2 = t;
				}

				map<Term*, long int> map1;
				map1[p1.first] = p1.second;
				t1 = ArithmeticTerm::make(map1, 0);
				map<Term*, long int> map2;
				map2[p2.first] = -p2.second;
				t2 = ArithmeticTerm::make(map2, 0);

				/*
				 * Case 1: Inequality of the form x<=y
				 */
				if(constant == 0)
				{
					add_edge(t1, t2, EDGEOP_LEQ);
					continue;
				}

				/*
				 * Case 2: Inequality of the form x < y
				 */
				if(constant == -1)
				{
					if(p1.second < 0 && p2.second > 0)
					{
						t1 = t1->multiply(-1);
						t2 = t2->multiply(-1);
						Term* t = t1;
						t1 = t2;
						t2 = t;

					}
					add_edge(t1, t2, EDGEOP_LT);

					// a < b also implies a <=b and a != b
					CNode* c = ILPLeaf::make(t1, t2, ILP_LT);
					CNode* c1 = ILPLeaf::make(t1, t2, ILP_LEQ);
					add_implication(c, c1);

					CNode* eq = EqLeaf::make(t1, t2);
					CNode* neq = Connective::make_not(eq);
					add_implication(c, neq);
					continue;
				}

			}
		}
		else if(ct == NOT)
		{
			Connective* not_c = (Connective*) literal;
			CNode* lit = *not_c->get_operands().begin();
			if(lit->get_type() == EQ)
			{
				EqLeaf* eq = (EqLeaf*) lit;
				Term* t1 = eq->get_lhs();
				Term* t2 = eq->get_rhs();
				add_edge(t1, t2, EDGEOP_NEQ);
			}
			else if(lit->get_type() == ILP)
			{
				ILPLeaf* ilp = (ILPLeaf*) lit;
				assert(ilp->get_operator() == ILP_EQ);
				const map<Term*, long int>& elems = ilp->get_elems();
				Term* t1 = ArithmeticTerm::make(elems, 0);
				Term* t2 = ConstantTerm::make(ilp->get_constant());
				add_edge(t1, t2, EDGEOP_NEQ);

			}

		}

	}


	if(ADD_CONSTANT_DISEQUALITIES)
	{
		/*
		 * Now, add pairwise disequality edges between all the constants.
		 */

		set<Term*>::iterator it1 = used_constants.begin();
		for(; it1!= used_constants.end(); it1++)
		{
			Term* t1 = *it1;
			set<Term*>::iterator it2 = it1;
			it2++;
			for(; it2!=used_constants.end(); it2++)
			{
				Term* t2 = *it2;
				add_edge(t1, t2, EDGEOP_NEQ, false);
			}
		}
	}


}

void BooleanAbstractor::add_edge(node* source_node, node* target_node, edge_op op,
		set<edge*>* added_edges)
{
	pair<node*, node*> key(source_node, target_node);
	edge *e;
	if(edge_matrix.count(key) > 0)
	{
		e = edge_matrix[key];
		e->op = edge_op(e->op | op);
	}
	else{
		e = new edge(source_node, target_node, op);
		edge_matrix[key] = e;
		if(added_edges != NULL) added_edges->insert(e);
	}
	relation_graph.insert(e);

	if(op == EDGEOP_EQ || op == EDGEOP_NEQ)
	{
		pair<node*, node*> key2(target_node , source_node);
		edge* e2;
		if(edge_matrix.count(key2) > 0)
		{
			e2 = edge_matrix[key2];
			e2->op = edge_op(e2->op | op);
		}else
		{
			e2 = new edge(target_node, source_node, op);
			edge_matrix[key2] = e2;
			if(added_edges != NULL) added_edges->insert(e2);
		}
		relation_graph.insert(e2);
	}
}

void BooleanAbstractor::add_edge(Term* source, Term* target, edge_op op,
		bool add_used_constant)
{

	if(add_used_constant && source->get_term_type() == CONSTANT_TERM)
	{
		used_constants.insert(source);
	}

	if(add_used_constant && target->get_term_type() == CONSTANT_TERM)
	{
		used_constants.insert(target);
	}

	node* source_node = get_node_from_term(source);
	node* target_node = get_node_from_term(target);
	add_edge(source_node, target_node, op);


}

void BooleanAbstractor::make_chordal()
{
	set<node*> processed_nodes;
	set<node*> all_nodes;
	set<edge*> processed_edges;
	map<Term*, node*>::iterator it = term_to_node_map.begin();
	for(; it!= term_to_node_map.end(); it++)
	{
		node* n = it->second;
		all_nodes.insert(n);
	}
	unsigned int num_nodes = all_nodes.size();
	while(true)
	{
		if(processed_nodes.size() == num_nodes) break;
		node* n;
		do {
			if(frontier_nodes.size() > 0) {
				n = *frontier_nodes.begin();
				frontier_nodes.erase(n);
				all_nodes.erase(n);
			}
			else {
				assert(all_nodes.size()>=1);
				n = *all_nodes.begin();
				all_nodes.erase(n);
			}
		} while (processed_nodes.count(n) > 0);
		processed_nodes.insert(n);

		//cout << "processing node: " << n->to_string() << endl;

		set<edge*>::iterator incoming_it = n->incoming_edges.begin();

		//cout << "-----------Processing node: " << n->t->to_string() << endl;

		/*
		 * We only want to consider unprocessed outgoing edges,
		 * so put these in set.
		 */
		set<edge*> outgoing;
		set<edge*>::iterator it = n->outgoing_edges.begin();
		for(; it!= n->outgoing_edges.end(); it++)
		{
			edge* e = *it;
			if(processed_edges.count(e) > 0) continue;
			outgoing.insert(e);
		}



		for(; incoming_it!=n->incoming_edges.end(); incoming_it++)
		{
			edge* in_e = *incoming_it;
			if(processed_edges.count(in_e) > 0) continue;

			processed_edges.insert(in_e);
			//cout << "Removed incoming edge: " << in_e->to_string() << endl;

			set<edge*>::iterator outgoing_it = outgoing.begin();
			for(; outgoing_it != outgoing.end(); outgoing_it++)
			{
				edge* out_e = *outgoing_it;

				wire_edge(in_e, out_e, processed_edges);

			}
		}

		// Mark outgoing edges as processed
		set<edge*>::iterator outgoing_it = outgoing.begin();
		for(; outgoing_it != outgoing.end(); outgoing_it++)
		{
			processed_edges.insert(*outgoing_it);
			//cout << "Removed outgoing edge: " << (*outgoing_it)->to_string() << endl;
		}


		//cout << "-------Done processing node: " << n->to_string() << endl;
	}
}

void BooleanAbstractor::wire_edge(edge* in_e, edge* out_e,
		set<edge*>& processed_edges)
{
	// check for self cycle
	node* source = in_e->source;
	node* target = out_e->target;
	if(source == target) return;

	// check if source and target are already connected
	if(edge_between(source, target)){
		if(is_frontier_node(source, processed_edges))
			frontier_nodes.insert(source);
		if(is_frontier_node(target, processed_edges))
			frontier_nodes.insert(target);
		return;
	}


	//cout << "Adding new edge: " << source->t->to_string() << " -> " <<
	//	target->t->to_string() << endl;

	edge_op new_op = (edge_op) 0;

	/*
	 * If one of the edges has the < and the other has anything other than
	 * just !=, we can deduce < for the wired edge.
	 */
	if( ((in_e->op & EDGEOP_LT) && (out_e->op & ~(EDGEOP_NEQ))) ||
			((out_e->op & EDGEOP_LT) && (in_e->op & ~(EDGEOP_NEQ)))	)
	{
		new_op = (edge_op) (new_op | EDGEOP_LT);
	}

	/*
	 * If one of them has <= and the other has something other than !=,
	 * we can deduce <=.
	 */
	if( ((in_e->op & EDGEOP_LEQ) && ((out_e->op & EDGEOP_EQ) ||
			(out_e->op & EDGEOP_LEQ))) ||
		((out_e->op & EDGEOP_LEQ) && ((out_e->op & EDGEOP_EQ) ||
				(out_e->op & EDGEOP_LEQ)))	)
	{
		new_op = (edge_op) (new_op | EDGEOP_LEQ);
	}

	/*
	 * If both are =, we can deduce =.
	 */
	if((in_e->op & EDGEOP_EQ) && (out_e->op & EDGEOP_EQ))
	{
		new_op = (edge_op) (new_op | EDGEOP_EQ);
	}

	/*
	 * If one has != and the other =, we can deduce !=.
	 */
	if( ((in_e->op & EDGEOP_NEQ) && (out_e->op & EDGEOP_EQ)) ||
		((in_e->op & EDGEOP_EQ) && (out_e->op & EDGEOP_NEQ))	)
	{
		new_op = (edge_op) (new_op | EDGEOP_NEQ);
	}
	if(new_op != 0)
		add_edge(source, target, new_op);
	else
	{
		if(is_frontier_node(source, processed_edges))
			frontier_nodes.insert(source);
		if(is_frontier_node(target, processed_edges))
			frontier_nodes.insert(target);
	}

}

/*
 * For each node, we look at all targets reached after two steps and
 * if there is a triangle, we add all the relevant implications.
 */
void BooleanAbstractor::add_implications()
{
	map<Term*, node*>::iterator it = term_to_node_map.begin();
	for(; it!= term_to_node_map.end(); it++)
	{
		node* n = it->second;
		set<edge*>::iterator it1 = n->outgoing_edges.begin();
		for(; it1!= n->outgoing_edges.end(); it1++)
		{
			edge* e1 = *it1;
			edge_op op1 = e1->op;
			node* succ1 = e1->target;

			set<edge*>::iterator it2 = succ1->outgoing_edges.begin();
			for(; it2!= succ1->outgoing_edges.end(); it2++)
			{
				if((int)valid_implications.size() > max_implications) return;
				edge* e2 = *it2;
				edge_op op2 = e2->op;
				node* succ2 = e2->target;

				/*
				 * If there is no edge between n and succ2, we can't be
				 * in a triangle and the relation between n and succ2 is not
				 * relevant.
				 */
				if(!edge_between(n, succ2)) continue;

				Term* source_t = n->t;
				Term* target_t = succ2->t;


				if(deduce_lt(op1, op2))
				{
					CNode* deduction;
					if(is_relevant_deduction(n, succ2, EDGEOP_LT)) {
						deduction = ILPLeaf::make(source_t, target_t, ILP_LT);
						add_implication(e1, e2, deduction, EDGEOP_LT);
						continue;
					}

					// We can also deduce the weaker <= and !=.
					if(is_relevant_deduction(n, succ2, EDGEOP_LEQ)) {
						deduction = ILPLeaf::make(source_t, target_t, ILP_LEQ);
						add_implication(e1, e2, deduction, EDGEOP_LEQ);
					}

					if(is_relevant_deduction(n, succ2, EDGEOP_NEQ)) {
						deduction = EqLeaf::make(source_t, target_t);
						deduction = Connective::make_not(deduction);
						add_implication(e1, e2, deduction, EDGEOP_NEQ);
					}

				}

				else if(deduce_eq(op1, op2))
				{
					CNode* deduction;
					if(is_relevant_deduction(n, succ2, EDGEOP_EQ)){
						deduction = EqLeaf::make(source_t, target_t);
						add_implication(e1, e2, deduction, EDGEOP_EQ);
						continue;
					}

					if(is_relevant_deduction(n, succ2, EDGEOP_LEQ)) {
						deduction = ILPLeaf::make(source_t, target_t, ILP_LEQ);
						add_implication(e1, e2, deduction, EDGEOP_LEQ);
					}
				}

				else if(deduce_leq(op1, op2))
				{
					if(is_relevant_deduction(n, succ2, EDGEOP_LEQ)) {
						CNode* deduction = ILPLeaf::make(source_t, target_t, ILP_LEQ);
						add_implication(e1, e2, deduction, EDGEOP_LEQ);
					}
				}
			}
		}


	}
}

/*
 * Adds the implication e1 & e2 -> deduction.
 */
void BooleanAbstractor::add_implication(edge* e1, edge* e2, CNode* deduction,
		edge_op op)
{


	edge_op ops1 = e1->op;
	edge_op ops2 = e2->op;

	for(edge_op i = EDGEOP_EQ; i <= EDGEOP_LEQ; i = (edge_op)(i<<1))
	{
		if(!(ops1 & i)) continue;
		for(edge_op j = EDGEOP_EQ; j <= EDGEOP_LEQ; j = (edge_op)(j<<1))
		{
			if(!(ops2 & j)) continue;
			if(deduce_op(i, j, op)) {
				CNode* prec1 = edge_to_literal(e1, i);
				CNode* prec2 = edge_to_literal(e2, j);
				CNode* prec = Connective::make(AND, prec1, prec2);
				CNode* res = Connective::make(OR, Connective::make_not(prec), deduction);
				valid_implications.insert(res);
				//cout << "Adding imp 2: " << prec->to_string() <<
				//"->" << deduction->to_string() << endl;


			}
		}
	}



}

/*
 * Given op1 and op2, can we deduce the op called ded_op?
 * e.g. > and = can deduce > and >=.
 */
bool BooleanAbstractor::deduce_op(edge_op op1, edge_op op2, edge_op ded_op)
{
	bool lt_deduce =  (op1 == EDGEOP_LT && op2!= EDGEOP_NEQ) ||
		(op2 == EDGEOP_LT && op1!= EDGEOP_NEQ);
	bool eq_deduce = op1 == EDGEOP_EQ && op2 == EDGEOP_EQ;

	if(ded_op == EDGEOP_LT) {
		return lt_deduce;
	}

	if(ded_op == EDGEOP_EQ) {
		return eq_deduce;
	}


	if(ded_op == EDGEOP_LEQ) {
		if(lt_deduce) return true;
		if(eq_deduce) return true;
		if(op1 == EDGEOP_LEQ && op2 != EDGEOP_NEQ) return true;
		return (op2 == EDGEOP_LEQ && op1 != EDGEOP_NEQ);
	}

	assert(ded_op == EDGEOP_NEQ);
	if(lt_deduce) return true;
	if(op1 == EDGEOP_EQ && op2 == EDGEOP_NEQ) return true;
	return (op1 == EDGEOP_NEQ && op2 == EDGEOP_EQ);
}

/*
 * Gives the literal representation of this edge.
 */
CNode* BooleanAbstractor::edge_to_literal(edge* e, edge_op op)
{
	Term* t1 = e->source->t;
	Term* t2 = e->target->t;
	if(op == EDGEOP_EQ)
	{
		return EqLeaf::make(t1, t2);
	}

	else if(op == EDGEOP_LT)
	{
		return ILPLeaf::make(t1, t2, ILP_LT);
	}
	else if(op == EDGEOP_LEQ)
	{
		return ILPLeaf::make(t1, t2, ILP_LEQ);
	}
	else if(op == EDGEOP_NEQ)
	{
		return Connective::make_not(EqLeaf::make(t1, t2));
	}
	assert(false);


}

bool BooleanAbstractor::is_relevant_deduction(node* source, node* target,
		edge_op op)
{
	if(source->t->get_term_type() == CONSTANT_TERM &&
			target->t->get_term_type() == CONSTANT_TERM) return true;


	if(!edge_between(source, target)) return false;


	pair<node*, node*> k1(source, target);
	if(edge_matrix.count(k1) > 0) {

		edge* e = edge_matrix[k1];
		if(e->op & op) return true;

		if(op == EDGEOP_NEQ) {
			return (e->op & EDGEOP_EQ);
		}

		if(op == EDGEOP_EQ) {
			return (e->op & EDGEOP_NEQ);
		}

	}

	pair<node*, node*> k2(target, source);
	if(edge_matrix.count(k2) == 0) return false;

	edge* e2 = edge_matrix[k2];
	if(op == EDGEOP_LT) {
		return (e2->op & EDGEOP_LEQ);
	}
	if(op == EDGEOP_LEQ)
		return (e2->op & EDGEOP_LT);
	else return false;

}

/*
 * Given a op1 b and b op2 c, can we deduce a < c?
 */
bool BooleanAbstractor::deduce_lt(edge_op op1, edge_op op2)
{
	if( (op1 & EDGEOP_LT) && (op2 & ~(EDGEOP_NEQ))) return true;
	return( (op2 & EDGEOP_LT) && (op1 & ~(EDGEOP_NEQ)));
}

/*
 * Given a op1 b and b op2 c, can we deduce a <= c?
 */
bool BooleanAbstractor::deduce_leq(edge_op op1, edge_op op2)
{
	if( (op1 & EDGEOP_LEQ) && (op2 & ~(EDGEOP_NEQ))) return true;
	return( (op2 & EDGEOP_LEQ) && (op1 & ~(EDGEOP_NEQ)));
}

/*
 * Given a op1 b and b op2 c, can we deduce a = c?
 */
bool BooleanAbstractor::deduce_eq(edge_op op1, edge_op op2)
{
	return ((op1 & EDGEOP_EQ) && (op2 & EDGEOP_EQ));
}

/*
 * Is there any edge between n1 and n2, disregarding direction of the edges?
 */
inline bool BooleanAbstractor::edge_between(node* n1, node* n2)
{
	pair<node*, node*> k1(n1, n2);
	if(edge_matrix.count(k1) > 0) return true;

	pair<node*, node*> k2(n2, n1);
	if(edge_matrix.count(k2) > 0) return true;

	return false;
}

bool BooleanAbstractor::is_frontier_node(node* n)
{
	if(n->incoming_edges.size() == 0 || n->outgoing_edges.size() == 0)
		return true;
	if(n->incoming_edges.size() > 1 || n->outgoing_edges.size() > 1)
		return false;
	return (*n->incoming_edges.begin())->source ==
		(*n->outgoing_edges.begin())->target;
}

bool BooleanAbstractor::is_frontier_node(node* n, set<edge*> & processed_edges)
{
	set<edge*> in;
	set<edge*> out;
	set<edge*>::iterator it = n->incoming_edges.begin();
	for(; it!= n->incoming_edges.end(); it++){
		edge *e = *it;
		if(processed_edges.count(e) > 0) continue;
		in.insert(e);
	}
	it = n->outgoing_edges.begin();
	for(; it!= n->outgoing_edges.end(); it++){
		edge *e = *it;
		if(processed_edges.count(e) > 0) continue;
		out.insert(e);
	}
	if(in.size() == 0 || out.size() == 0)
		return true;
	if(in.size() > 1 || out.size() > 1)
		return false;
	return (*in.begin())->source ==
		(*out.begin())->target;
}

void BooleanAbstractor::add_initial_frontier_nodes()
{
	map<Term*, node*>::iterator it = term_to_node_map.begin();
	for(; it!= term_to_node_map.end(); it++)
	{
		node* n = it->second;
		if(is_frontier_node(n))
			frontier_nodes.insert(n);
	}
}

string BooleanAbstractor::relation_graph_to_dotty()
{

	string res = "digraph G { \n";
	set<edge*>::iterator it = relation_graph.begin();
	for(; it!= relation_graph.end(); it++){
		edge* e = *it;

		string op_str = "{";
		if(e->op & EDGEOP_EQ) op_str += "=, ";
		if(e->op & EDGEOP_NEQ) op_str += "!=, ";
		if(e->op & EDGEOP_LT) op_str += "<, ";
		if(e->op & EDGEOP_LEQ) op_str += "<=, ";
		op_str = op_str.substr(0, op_str.size()-2);
		op_str += "}";


		res += "node" + int_to_string((unsigned long int)e->source) +
			" [shape = box][label= \"" + e->source->t->to_string() + "\"] \n";
		res += "node" +  int_to_string((unsigned long int) e->target) +
		" [shape = box][label= \"" + e->target->t->to_string() + "\"] \n";

		res+= "node" + int_to_string((unsigned long int) e->source) + " -> " +
		"node" + int_to_string((unsigned long int) e->target) + " [label = \"" +
			op_str + "\"]\n";


	}
	res+= "}";
	return res;

}

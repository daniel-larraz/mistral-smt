/*
 * CNode.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include "cnode.h"
#include "util.h"
#include "term.h"
#include "assert.h"

#define ASSERT_ENABLED true



unordered_set<CNode*, hash<CNode*>, node_eq> CNode::nodes;
unordered_map<pair<int, CNode*>, CNode*> CNode::simp_map;
set<CNode*> CNode::to_delete;
VarMap CNode::vm;

bool CNode::delete_nodes = true;

size_t hash<CNode*>::operator() (const CNode* const & x) const
{
	CNode*& xx = (CNode*&)x;
	return xx->hash_code();

}

size_t hash<pair<int, CNode*> >::operator() (const pair<int,CNode*>  & x) const
{
	pair<int,CNode*>& xx = (pair<int,CNode*>&)x;
	return xx.first + 7*(size_t)xx.second;

}



CNode* CNode::get_simplification(simplification_level min_level)
{
	//return NULL;
	//cout << this->to_string() << "  " << this->hash_c << endl;
	pair<int,CNode*> key(min_level, this);

	if(simp_map.count(key) > 0){

		return simp_map[key];
	}

	return NULL;
}

void CNode::set_simplification(CNode* simplified_node,
		simplification_level level)
{


	if(simplified_node->get_type() == FALSE_NODE)
	{
		for(int i=UNSAT_SIMPLIFY; i< _END_SIMPLIFY_; i++) {
			pair<int,CNode*> key(i, this);
			simp_map[key] = simplified_node;
		}
		return;
	}


	pair<int,CNode*> key(level, this);
	if(simp_map.count(key) > 0) return;


	for(int i=UNSAT_SIMPLIFY; i<=level; i++)
	{
		pair<int,CNode*> key(i, this);
		simp_map[key] = simplified_node;
	}
}

template<cnode_type my_type, cnode_type other_type>
CNode* CNode::connective_refactor(const set<CNode*>& orig_children)
{

	set<CNode*> children;
	set<CNode*>::iterator it = orig_children.begin();
	for(; it!=orig_children.end(); it++) {
		children.insert((*it)->refactor());
	}

	/*
	 * If at least one of the children is an or, there may be
	 * opportunities for refactoring.
	 * First, build initial mapping from children to parent nodes in
	 * which they appear (child_to_parents). For example,
	 * if the and node is (x |y ) & (x|z), then mapping is
	 * x-> { (x|y), (x|z)}, y-> {(x|y)},  z-> {(x|z)}
	 */
	set<pair<CNode*, set<CNode*> >, refactor_lessthan > refactor_order;
	map<CNode*, set<CNode*> > child_to_parents;
	it = children.begin();
	for(; it!= children.end(); it++)
	{
		CNode* cur = *it;
		if(cur->get_type() != other_type) {
			child_to_parents[cur].insert(cur);
			continue;
		}
		Connective* other_node = (Connective*) cur;
		const set<CNode*>& other_children = other_node->get_operands();
		set<CNode*>::iterator it2 = other_children.begin();
		for(; it2!= other_children.end(); it2++)
		{
			CNode* other_child = *it2;
			child_to_parents[other_child].insert(cur);
		}
	}

	set<CNode*> refactored_children;

	while(child_to_parents.size() > 0)
	{
		refactor_order.clear();
		// Insert into refactor order
		map<CNode*, set<CNode*> >::iterator it2= child_to_parents.begin();
		for(; it2!= child_to_parents.end(); it2++) {
			refactor_order.insert(*it2);
		}


		CNode* cur = refactor_order.begin()->first;
		const set<CNode*>& parents = refactor_order.begin()->second;
		child_to_parents.erase(cur);

		if(ASSERT_ENABLED) assert(parents.size() != 0);

		/*
		 * If we have some node like (x |y |z ) & (x | a | b),
		 * the remainder_children would be ((y|z) & (a|b)).
		 */
		set<CNode*> remainder_children;
		set<CNode*>::iterator it = parents.begin();
		for(; it!= parents.end(); it++) {
			CNode* _cur_parent = *it;
			if(_cur_parent->get_type() != other_type) {
				if(my_type == AND) remainder_children.insert(False::make());
				else remainder_children.insert(True::make());
				continue;
			}
			Connective* cur_parent = (Connective*) _cur_parent;
			const set<CNode*>& cur_children = cur_parent->get_operands();

			/*
			 * If we are processing x and its parent x |y,
			 * we want to update dependencies between y and x|y in the maps.
			 */
			set<CNode*> parents_other_children;
			set<CNode*>::iterator it2 = cur_children.begin();
			for(; it2!= cur_children.end(); it2++) {
				CNode* other_child = *it2;
				if(other_child == cur) continue;
				parents_other_children.insert(other_child);
				set<CNode*>& all_parents = child_to_parents[other_child];
				if(all_parents.size() == 1) child_to_parents.erase(other_child);
				else child_to_parents[other_child].erase(cur_parent);

			}

			CNode* remainder_child = Connective::make(other_type,
					parents_other_children)->refactor();
			remainder_children.insert(remainder_child);
		}
		CNode* remainder =
				Connective::make(my_type, remainder_children)->refactor();
		CNode* refactored_child =
				Connective::make(other_type, cur, remainder)->refactor();
		refactored_children.insert(refactored_child);


	}

	if(refactored_children.size() == 1) return *refactored_children.begin();
	Connective* c = new Connective(my_type, refactored_children);
	return CNode::get_node(c);
}

/*
 * Refactors this constraint in a locally optimal way.
 */
CNode* CNode::refactor()
{
	if(factorization  != NULL) return factorization;
	if(node_type != AND && node_type != OR) {
		factorization = this;
		return this;
	}
	Connective* c = (Connective*) this;
	if(node_type == AND) {
		factorization = CNode::connective_refactor<AND, OR>(c->get_operands());
	}
	else {
		factorization = CNode::connective_refactor<OR, AND>(c->get_operands());
	}
	/*
	 * If the original constraint was satisfiable, the refactorization
	 * is still satisfiable and vice versa.
	 */
	if(get_simplification(UNSAT_SIMPLIFY) != NULL) {
		factorization->set_simplification(factorization, UNSAT_SIMPLIFY);
	}
	return factorization;
}


bool node_eq::operator()(const CNode* l1, const CNode* l2) const
{
  return *(CNode*)l1==*(CNode*)l2;
}

CNode::CNode() {
	negation = NULL;
	factorization = NULL;
}


VarMap& CNode::get_varmap()
{
	return vm;
}

CNode* CNode::get_node(CNode* node)
{

	unordered_set<CNode*, hash<CNode*>, node_eq>::iterator it = nodes.find(node);
	if(it == nodes.end()){

		nodes.insert(node);
		return node;
	}
	if(node != *it){
		if(delete_nodes) delete node;
		else to_delete.insert(node);
	}
	return *it;
}

CNode* CNode::uniquify_cnode(CNode* node)
{
	if(node == NULL) return NULL;
	delete_nodes = false;
	CNode* res = uniquify_cnode_rec(node);
	delete_nodes = true;
	set<CNode*>::iterator it = to_delete.begin();
	for(; it!= to_delete.end(); it++)
	{
		delete *it;
	}
	to_delete.clear();
	return res;

}

CNode* CNode::uniquify_cnode_rec(CNode* node)
{
	switch(node->get_type())
	{
	case FALSE_NODE:
		return False::make();
	case TRUE_NODE:
		return True::make();
	case BOOLEAN_VAR:
	{
		BooleanVar* b  = (BooleanVar*)node;
		return BooleanVar::make(b->get_name());
	}
	case EQ:
	{
		EqLeaf* l = (EqLeaf*) node;
		return EqLeaf::make(l->get_lhs(), l->get_rhs());
	}
	case ILP:
	{
		ILPLeaf* l = (ILPLeaf*) node;
		return ILPLeaf::make(l->get_operator(), l->get_elems(), l->get_constant());
	}
	case MOD:
	{
		ModLeaf* l = (ModLeaf*) node;
		return ModLeaf::make(l->get_term(), l->get_mod_constant());
	}
	case UNIVERSAL:
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*) node;
		return QuantifiedLeaf::make(ql->get_quantified_vars(),
				uniquify_cnode_rec(ql->get_index_guard()),
				uniquify_cnode_rec(ql->get_value_guard()));
	}
	case NOT:
	case AND:
	case OR:
	{
		Connective* c = (Connective*) node;
		set<CNode*> ops;
		set<CNode*>::const_iterator it = c->get_operands().begin();
		for(; it!= c->get_operands().end(); it++)
		{
			CNode* c = uniquify_cnode_rec(*it);
			ops.insert(c);
		}
		return Connective::make(c->get_type(), ops);
	}
	default:
		assert(false);
	}
}



CNode* CNode::true_node()
{
	static CNode* n = new True();
	return n;
}
CNode* CNode::false_node()
{
	static CNode* n = new False();
	return n;
}

void CNode::clear()
{
	vm.clear();
	vector<CNode*> to_delete;
	unordered_set<CNode*, hash<CNode*>, node_eq>::iterator it = nodes.begin();
	for(; it!= nodes.end(); it++) {
		to_delete.push_back(*it);
	}
	for(unsigned int i=0; i<to_delete.size(); i++) {
		delete to_delete[i];
	}

	nodes.clear();
	simp_map.clear();
	Term::clear();
	BooleanVar::clear();

}

string CNode::to_prefix_notation()
{
	string res;
	to_prefix_notation_rec(res);
	return res;
}

bool CompareCNode::operator()(const CNode* _c1, const CNode* _c2) const
{
	CNode* c1 = (CNode*)_c1;
	CNode* c2 = (CNode*)_c2;
	return c1->to_string() < c2->to_string();
}



bool CNode::is_leaf() const
{

	return get_type() <= UNIVERSAL;
}

bool CNode::is_literal() const
{
	// negations are always pushed in
	return get_type() <= NOT;
}

bool CNode::is_connective() const
{
	return !is_leaf();
}

bool CNode::is_constant() const
{
	return get_type() <= TRUE_NODE;
}

bool CNode::is_conjunct() const
{
	if(is_literal()) return true;
	if(get_type() != AND) return false;
	Connective* c = (Connective*) this;
	set<CNode*>::const_iterator it = c->get_operands().begin();
	for(; it!= c->get_operands().end(); it++) {
		CNode* cur = *it;
		if(!cur->is_literal()) return false;
	}
	return true;
}


bool CNode::is_disjunct() const
{
	if(is_literal()) return true;
	if(get_type() != OR) return false;
	Connective* c = (Connective*) this;
	set<CNode*>::const_iterator it = c->get_operands().begin();
	for(; it!= c->get_operands().end(); it++) {
		CNode* cur = *it;
		if(!cur->is_literal()) return false;
	}
	return true;
}


void CNode::to_prefix_notation_rec(string& res)
{

	switch(this->get_type())
	{
	case AND:
	{
		set<CNode*, CompareCNode> ops;
		Connective* c = (Connective*) this;
		set<CNode*, CompareCNode>::iterator it = c->get_operands().begin();
		for(; it!= c->get_operands().end(); it++) {
			ops.insert(*it);
		}

		//ops.insert(c->get_operands().begin(), c->get_operands().end());
		res += "( and ";

		it = ops.begin();
		for(; it!= ops.end(); it++)
		{
			CNode* cur = *it;
			cur->to_prefix_notation_rec(res);

		}
		res += " )";
		break;
	}
	case OR:
	{
		res += "( or ";
		Connective* c = (Connective*) this;
		set<CNode*, CompareCNode> ops;
		ops.insert(c->get_operands().begin(), c->get_operands().end());
		set<CNode*, CompareCNode>::iterator it = ops.begin();
		for(; it!= ops.end(); it++)
		{
			CNode* cur = *it;
			cur->to_prefix_notation_rec(res);

		}
		res += " )";
		break;
	}
	case NOT:
	{
		res += "( not ";
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		set<CNode*>::iterator it = ops.begin();
		for(; it!= ops.end(); it++)
		{
			CNode* cur = *it;
			cur->to_prefix_notation_rec( res);

		}
		res += " )";
		break;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;

		res += "( " + ilp->ilp_leaf_type_to_string(ilp->get_operator()) + " ";

		map<Term*, long int >::const_iterator it = ilp->get_elems().begin();
		for(int i=0; it!= ilp->get_elems().end(); it++, i++)
		{
			Term* t = it->first;
			if(i!=(int)ilp->get_elems().size() - 1)
			{
				res += "(+ ";
			}
			res += "(* ";
			int coef = it->second;
			if(coef < 0) {
				res += "(~ " + int_to_string(-coef);
				res += ")";
			}
			else  res += int_to_string(coef);
			res += " " + t->to_string();
			res +=")";

		}

		for(int i=0; i< (int)ilp->get_elems().size()-1; i++)
			res += ")";

		int constant = ilp->get_constant();
		if(constant < 0){
			res += "(~ " + int_to_string(-constant);
			res += ")";
		}
		else res += " " + int_to_string(ilp->get_constant());

		res += ")";
		break;
	}

	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		res += "( = ";
		res += eq->get_lhs()->to_string() + " ";
		res += eq->get_rhs()->to_string();
		res += ")";
		break;
	}
	default:
		res = "ERROR.";

	}
}

size_t CNode::hash_code()
{
	return hash_c;
}

CNode::~CNode() {
	// TODO Auto-generated destructor stub
}

/*
 * Returns a set of variables name used in the constraint.
 */
void CNode::get_vars(set<string>& vars)
{
	switch (get_type()) {
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return;
	case ILP: {
		ILPLeaf* ilp = (ILPLeaf*) this;
		map<Term*, long int>::const_iterator it = ilp->get_elems().begin();
		for (; it != ilp->get_elems().end(); it++) {
			it->first->get_vars(vars);
		}
		break;
	}
	case EQ: {
		EqLeaf* eq = (EqLeaf*) this;
		eq->get_lhs()->get_vars(vars);
		eq->get_rhs()->get_vars(vars);
		return;
	}
	case MOD:
	{
		ModLeaf* ml = (ModLeaf*) this;
		ml->get_term()->get_vars(vars);
		return;

	}
	case UNIVERSAL: {
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		ql->get_index_guard()->get_vars(vars);
		ql->get_value_guard()->get_vars(vars);
		set<int>::iterator it = ql->get_quantified_vars().begin();
		for (; it != ql->get_quantified_vars().end(); it++) {
			vars.erase(vm.get_name(*it));
		}
		return;

	}
	case AND:
	case OR:
	case NOT:
	case IMPLIES: {
		Connective* conn = (Connective*) this;
		set<CNode*>::iterator it = conn->get_operands().begin();
		for (; it != conn->get_operands().end(); it++) {
			(*it)->get_vars(vars);
		}
	}

	}
}


void CNode::get_vars(set<int>& vars)
{
	switch (get_type()) {
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return;
	case ILP: {
		ILPLeaf* ilp = (ILPLeaf*) this;
		map<Term*, long int>::const_iterator it = ilp->get_elems().begin();
		for (; it != ilp->get_elems().end(); it++) {
			it->first->get_vars(vars);
		}
		break;
	}
	case EQ: {
		EqLeaf* eq = (EqLeaf*) this;
		eq->get_lhs()->get_vars(vars);
		eq->get_rhs()->get_vars(vars);
		return;
	}
	case MOD:
	{
		ModLeaf* ml = (ModLeaf*) this;
		ml->get_term()->get_vars(vars);
		return;

	}
	case UNIVERSAL: {
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		ql->get_index_guard()->get_vars(vars);
		ql->get_value_guard()->get_vars(vars);
		set<int>::iterator it = ql->get_quantified_vars().begin();
		for (; it != ql->get_quantified_vars().end(); it++) {
			vars.erase(*it);
		}
		return;

	}
	case AND:
	case OR:
	case NOT:
	case IMPLIES: {
		Connective* conn = (Connective*) this;
		set<CNode*>::iterator it = conn->get_operands().begin();
		for (; it != conn->get_operands().end(); it++) {
			(*it)->get_vars(vars);
		}
	}

	}
}


void CNode::get_vars(set<Term*>& vars)
{
	switch (get_type()) {
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return;
	case ILP: {
		ILPLeaf* ilp = (ILPLeaf*) this;
		map<Term*, long int>::const_iterator it = ilp->get_elems().begin();
		for (; it != ilp->get_elems().end(); it++) {
			it->first->get_vars(vars);
		}
		break;
	}
	case EQ: {
		EqLeaf* eq = (EqLeaf*) this;
		eq->get_lhs()->get_vars(vars);
		eq->get_rhs()->get_vars(vars);
		return;
	}
	case MOD:
	{
		ModLeaf* ml = (ModLeaf*) this;
		ml->get_term()->get_vars(vars);
		return;

	}
	case UNIVERSAL: {
		assert(false);
	}
	case AND:
	case OR:
	case NOT:
	case IMPLIES: {
		Connective* conn = (Connective*) this;
		set<CNode*>::iterator it = conn->get_operands().begin();
		for (; it != conn->get_operands().end(); it++) {
			(*it)->get_vars(vars);
		}
	}

	}
}

CNode* CNode::rename_variables(map<int, int>& replacements)
{
	switch (get_type()) {
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return this;
	case EQ: {
		EqLeaf* old_eq = (EqLeaf*) this;
		Term* new_lhs = old_eq->get_lhs()->rename_variables(replacements);
		Term* new_rhs = old_eq->get_rhs()->rename_variables(replacements);
		if(new_lhs == old_eq->get_lhs() && new_rhs == old_eq->get_rhs())
			return this;
		return EqLeaf::make(new_lhs, new_rhs);
	}
	case MOD:
	{
		ModLeaf* old_leaf = (ModLeaf*) this;
		Term* old_lhs = old_leaf->get_term();
		Term* new_lhs = old_lhs->rename_variables(replacements);
		if(old_lhs == new_lhs) return this;
		return ModLeaf::make(new_lhs, old_leaf->get_mod_constant());

	}
	case ILP: {
		ILPLeaf* old_ilp = (ILPLeaf*) this;
		bool changed = false;
		map<Term*, long int> new_elems;
		const map<Term*, long int>& elems = old_ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for (; it != elems.end(); it++) {
			pair<Term*, int> cur = *it;
			pair<Term*, int> new_elem = cur;
			Term* new_term = cur.first->rename_variables(replacements);
			if (new_term != cur.first) {
				new_elem = pair<Term*, int> (new_term, cur.second);
				changed = true;
			}
			new_elems.insert(new_elem);
		}
		if (!changed)
			return old_ilp;
		return ILPLeaf::make(old_ilp->get_operator(), new_elems,
				old_ilp->get_constant());
	}
	case UNIVERSAL: {
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		CNode* index_guard = ql->get_index_guard();
		CNode* value_guard = ql->get_value_guard();

		CNode* new_ig = index_guard->rename_variables(replacements);
		CNode* new_vg = value_guard->rename_variables(replacements);

		if (new_ig == index_guard && new_vg == value_guard)
			return this;
		return QuantifiedLeaf::make(ql->get_quantified_vars(),
				new_ig, new_vg);
	}

	case AND:
	case OR:
	case NOT:
	case IMPLIES: {
		set<CNode*> new_args;
		Connective* old_c = (Connective*) this;
		const set<CNode*>& elems = old_c->get_operands();
		set<CNode*>::const_iterator it = elems.begin();
		for (; it != elems.end(); it++) {
			CNode* elem = *it;
			CNode* new_elem = elem->rename_variables(replacements);
			new_args.insert(new_elem);
		}
		return Connective::make(old_c->get_type(), new_args);
	}
	default:
		assert(false);
	}
}

CNode* CNode::rename_variable(int old_var_id, int new_var_id)
{
	switch (get_type()) {
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return this;
	case EQ: {
		EqLeaf* old_eq = (EqLeaf*) this;
		Term* new_lhs = old_eq->get_lhs()->rename_variable(old_var_id, new_var_id);
		Term* new_rhs = old_eq->get_rhs()->rename_variable(old_var_id, new_var_id);
		if(new_lhs == old_eq->get_lhs() && new_rhs == old_eq->get_rhs())
			return this;
		return EqLeaf::make(new_lhs, new_rhs);
	}
	case MOD:
	{
		ModLeaf* old_leaf = (ModLeaf*) this;
		Term* old_lhs = old_leaf->get_term();
		Term* new_lhs = old_lhs->rename_variable(old_var_id, new_var_id);
		if(old_lhs == new_lhs) return this;
		return ModLeaf::make(new_lhs, old_leaf->get_mod_constant());

	}
	case ILP: {
		ILPLeaf* old_ilp = (ILPLeaf*) this;
		bool changed = false;
		map<Term*, long int> new_elems;
		const map<Term*, long int>& elems = old_ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for (; it != elems.end(); it++) {
			pair<Term*, int> cur = *it;
			pair<Term*, int> new_elem = cur;
			Term* new_term = cur.first->rename_variable(old_var_id, new_var_id);
			if (new_term != cur.first) {
				new_elem = pair<Term*, int> (new_term, cur.second);
				changed = true;
			}
			new_elems.insert(new_elem);
		}
		if (!changed)
			return old_ilp;
		return ILPLeaf::make(old_ilp->get_operator(), new_elems,
				old_ilp->get_constant());
	}
	case UNIVERSAL: {
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		CNode* index_guard = ql->get_index_guard();
		CNode* value_guard = ql->get_value_guard();

		CNode* new_ig = index_guard->rename_variable(old_var_id, new_var_id);
		CNode* new_vg = value_guard->rename_variable(old_var_id, new_var_id);

		if (new_ig == index_guard && new_vg == value_guard)
			return this;
		return QuantifiedLeaf::make(ql->get_quantified_vars(),
				new_ig, new_vg);
	}

	case AND:
	case OR:
	case NOT:
	case IMPLIES: {
		set<CNode*> new_args;
		Connective* old_c = (Connective*) this;
		const set<CNode*>& elems = old_c->get_operands();
		set<CNode*>::const_iterator it = elems.begin();
		for (; it != elems.end(); it++) {
			CNode* elem = *it;
			CNode* new_elem = elem->rename_variable(old_var_id, new_var_id);
			new_args.insert(new_elem);
		}
		return Connective::make(old_c->get_type(), new_args);
	}
	default:
		assert(false);
	}

}

CNode* CNode::replace(CNode* orig , CNode* replacement)
{
	if(this == orig) return replacement;
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
	case EQ:
	case ILP:
	case MOD:
		return this;
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		bool changed = false;
		set<CNode*> new_ops;
		set<CNode*>::iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* old_op = *it;
			CNode* new_op = old_op->replace(orig, replacement);
			if(old_op != new_op) changed = true;
			new_ops.insert(new_op);
		}
		if(!changed) return this;
		return Connective::make(c->get_type(), new_ops);


	}

	default:
		assert(false);
	}

}


/*
 * If a given leaf contains the term t, this function replaces that leaf
 * with the provided replacement node.
 * If the term provided is, for example, x, this function does not replace
 * a leaf of the form f(x) = 3 with the replacement; It only replaces leaves
 * actually containing x itself, e.g. x+y=4.
 */
CNode* CNode::replace_leaves_containing_term(Term* t, CNode* replacement)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return this;
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		if(eq->get_lhs() == t || eq->get_rhs() == t)
			return replacement;
		return this;
	}
	case MOD:
	{
		ModLeaf* mod = (ModLeaf*) this;
		if(mod->get_term() == t)
			return replacement;
		return this;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int> & elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			Term* cur_t = it->first;
			if(cur_t == t) return replacement;
		}
		return this;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		bool changed = false;
		set<CNode*> new_ops;
		set<CNode*>::iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* old_op = *it;
			CNode* new_op = old_op->replace_leaves_containing_term(t,
					replacement);
			if(old_op != new_op) changed = true;
			new_ops.insert(new_op);
		}
		if(!changed) return this;
		return Connective::make(c->get_type(), new_ops);


	}

	default:
		assert(false);


	}
}

CNode* CNode::substitute(map<CNode*, CNode*> & subs)
{
	if(subs.count(this) > 0) return subs[this];
	cnode_type ct = get_type();
	if(this->is_literal() && ct!= UNIVERSAL) return this;
	switch(ct)
	{
	case AND:
	case OR:
	{
		Connective* c= (Connective*)this;
		const set<CNode*>& ops = c->get_operands();
		bool changed = false;
		set<CNode*> new_ops;
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++)
		{
			CNode* old_op = *it;
			CNode* new_op = old_op->substitute(subs);
			if(old_op != new_op) changed = true;
			new_ops.insert(new_op);
		}
		if(!changed) return this;
		return Connective::make(ct, new_ops);
	}
	default:
		assert(false);
	}

}

void CNode::get_literals_containing_term(Term* t, set<CNode*>& res)
{
	set<CNode*> literals;
	get_all_literals(literals);
	set<CNode*>::iterator it = literals.begin();
	for(; it!= literals.end(); it++) {
		CNode* cur = *it;
		if(!cur->contains_term(t)) continue;
		res.insert(cur);
	}
}

bool CNode::contains_term(set<Term*>& t)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return false;
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		Term* lhs = eq->get_lhs();
		Term* rhs = eq->get_rhs();
		if(lhs->contains_term(t)) return true;
		return rhs->contains_term(t);
	}
	case MOD:
	{
		ModLeaf* ml = (ModLeaf*) this;
		Term* lhs = ml->get_term();
		return(lhs->contains_term(t));
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			if(it->first->contains_term(t)) return true;
		}
		return false;
	}

	case UNIVERSAL:
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		CNode* index_g = ql->get_index_guard();
		if(index_g->contains_term(t)) return true;
		CNode* value_g = ql->get_value_guard();
		return value_g->contains_term(t);
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* cur = *it;
			if(cur->contains_term(t)) return true;
		}
		return false;
	}
	default:
		assert(false);
	}
}

bool CNode::contains_term(Term* t)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return false;
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		Term* lhs = eq->get_lhs();
		Term* rhs = eq->get_rhs();
		if(lhs->contains_term(t)) return true;
		return rhs->contains_term(t);
	}
	case MOD:
	{
		ModLeaf* ml = (ModLeaf*) this;
		Term* lhs = ml->get_term();
		return(lhs->contains_term(t));
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			if(it->first->contains_term(t)) return true;
		}
		return false;
	}

	case UNIVERSAL:
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		CNode* index_g = ql->get_index_guard();
		if(index_g->contains_term(t)) return true;
		CNode* value_g = ql->get_value_guard();
		return value_g->contains_term(t);
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* cur = *it;
			if(cur->contains_term(t)) return true;
		}
		return false;
	}
	default:
		assert(false);
	}
}

bool CNode::contains_var(int var_id)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return false;
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		Term* lhs = eq->get_lhs();
		Term* rhs = eq->get_rhs();
		if(lhs->contains_var(var_id)) return true;
		return rhs->contains_var(var_id);
	}
	case MOD:
	{
		ModLeaf* ml = (ModLeaf*) this;
		Term* lhs = ml->get_term();
		return(lhs->contains_var(var_id));
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			if(it->first->contains_var(var_id)) return true;
		}
		return false;
	}

	case UNIVERSAL:
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		CNode* index_g = ql->get_index_guard();
		if(index_g->contains_var(var_id)) return true;
		CNode* value_g = ql->get_value_guard();
		return value_g->contains_var(var_id);
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* cur = *it;
			if(cur->contains_var(var_id)) return true;
		}
		return false;
	}
	default:
		assert(false);
	}
}


/*
 * If this node entails an equality constraint on the given term t, returns
 * another term t' such that t=t'; otherwise NULL.
 */
Term* CNode::contains_term_equality(Term* t)
{
	return contains_term_equality_internal(t, true);
}


/*
 * Returns the number of leaves that contain the given term
 */
int CNode::num_leaves_containing_term(Term* t)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
		return 0;
	case UNIVERSAL:
	{
		QuantifiedLeaf* u = (QuantifiedLeaf*) this;
		return u->get_index_guard()->num_leaves_containing_term(t) +
			u->get_value_guard()->num_leaves_containing_term(t);
	}
	case MOD:
	{
		ModLeaf* ml = (ModLeaf*) this;
		Term* cur = ml->get_term();
		if(cur->contains_term(t)) return 1;
		return 0;
	}
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		if(eq->get_rhs()->contains_term(t)) return 1;
		if(eq->get_lhs()->contains_term(t)) return 1;
		return 0;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		map<Term*, long int>::const_iterator it= ilp->get_elems().begin();
		for(; it!= ilp->get_elems().end(); it++)
		{
			Term* cur = it->first;
			if(cur->contains_term(t)) return 1;
		}
		return 0;
	}
	case AND:
	case OR:
	case NOT:
	{
		int res = 0;
		Connective* c = (Connective*) this;
		set<CNode*>::const_iterator it = c->get_operands().begin();
		for(; it!= c->get_operands().end(); it++)
		{
			CNode* c = *it;
			res += c->num_leaves_containing_term(t);

		}
		return res;
	}
	default:
		assert(false);



	}
}

CNode* CNode::substitute(Term* t1, Term* t2)
{
	map<Term*, Term*> m;
	m[t1] = t2;
	return this->substitute(m);
}

CNode* CNode::substitute(Term* (*sub_func)(Term* t))
{
	switch(this->get_type())
	{
		case BOOLEAN_VAR:
		case TRUE_NODE:
		case FALSE_NODE:
			return this;
		case EQ:
		{
			EqLeaf* eq = (EqLeaf*) this;
			Term* old_lhs = eq->get_lhs();
			Term* old_rhs = eq->get_rhs();
			Term* new_lhs = old_lhs->substitute(sub_func);
			Term* new_rhs = old_rhs->substitute(sub_func);
			if(new_rhs == old_rhs && old_lhs == new_lhs) return this;
			return EqLeaf::make(new_lhs, new_rhs);
		}
		case ILP:
		{
			ILPLeaf* ilp = (ILPLeaf*) this;
			bool changed = false;
			map<Term*, long int> new_elems;
			const map<Term*, long int>& elems = ilp->get_elems();
			map<Term*, long int>::const_iterator it = elems.begin();
			for(; it!= elems.end(); it++)
			{
				Term* t = it->first;
				Term* new_t = t->substitute(sub_func);
				if(t!= new_t) changed = true;
				new_elems[new_t] = it->second;
			}
			if(!changed) return this;
			return ILPLeaf::make(ilp->get_operator(),
					new_elems, ilp->get_constant());
		}
		case MOD:
		{
			ModLeaf* ml = (ModLeaf*) this;
			Term* t = ml->get_term();
			Term* new_t = t->substitute(sub_func);
			if(t==new_t) return this;
			return ModLeaf::make(new_t, ml->get_mod_constant());
		}
		case AND:
		case OR:
		case NOT:
		{
			Connective* c = (Connective*) this;
			set<CNode*> new_ops;
			bool changed = false;
			const set<CNode*>& ops = c->get_operands();
			set<CNode*>::const_iterator it = ops.begin();
			for(; it!= ops.end(); it++)
			{
				CNode* op = *it;
				CNode* new_op = op->substitute(sub_func);
				if(op!=new_op) changed = true;
				new_ops.insert(new_op);
			}
			if(!changed) return this;
			return Connective::make(c->get_type(), new_ops);
		}
		default:
			assert(false);

	}
}

CNode* CNode::substitute(Term* (*sub_func)(Term* t, void* data), void* my_data)
{
	switch(this->get_type())
	{
		case BOOLEAN_VAR:
		case TRUE_NODE:
		case FALSE_NODE:
			return this;
		case EQ:
		{
			EqLeaf* eq = (EqLeaf*) this;
			Term* old_lhs = eq->get_lhs();
			Term* old_rhs = eq->get_rhs();
			Term* new_lhs = old_lhs->substitute(sub_func, my_data);
			Term* new_rhs = old_rhs->substitute(sub_func, my_data);
			if(new_rhs == old_rhs && old_lhs == new_lhs) return this;
			return EqLeaf::make(new_lhs, new_rhs);
		}
		case ILP:
		{
			ILPLeaf* ilp = (ILPLeaf*) this;
			bool changed = false;
			map<Term*, long int> new_elems;
			const map<Term*, long int>& elems = ilp->get_elems();
			map<Term*, long int>::const_iterator it = elems.begin();
			for(; it!= elems.end(); it++)
			{
				Term* t = it->first;
				Term* new_t = t->substitute(sub_func, my_data);
				if(t!= new_t) changed = true;
				new_elems[new_t] = it->second;
			}
			if(!changed) return this;
			return ILPLeaf::make(ilp->get_operator(),
					new_elems, ilp->get_constant());
		}
		case MOD:
		{
			ModLeaf* ml = (ModLeaf*) this;
			Term* t = ml->get_term();
			Term* new_t = t->substitute(sub_func, my_data);
			if(t==new_t) return this;
			return ModLeaf::make(new_t, ml->get_mod_constant());
		}
		case AND:
		case OR:
		case NOT:
		{
			Connective* c = (Connective*) this;
			set<CNode*> new_ops;
			bool changed = false;
			const set<CNode*>& ops = c->get_operands();
			set<CNode*>::const_iterator it = ops.begin();
			for(; it!= ops.end(); it++)
			{
				CNode* op = *it;
				CNode* new_op = op->substitute(sub_func, my_data);
				if(op!=new_op) changed = true;
				new_ops.insert(new_op);
			}
			if(!changed) return this;
			return Connective::make(c->get_type(), new_ops);
		}
		default:
			assert(false);

	}
}


Term* CNode::contains_term_equality_internal(Term* t, bool phase)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
	case UNIVERSAL:
	case MOD:
	case OR:
		return NULL;
	case EQ:
	{
		if(!phase) return NULL;
		EqLeaf* eq = (EqLeaf*) this;
		Term* lhs = eq->get_lhs();
		Term* rhs = eq->get_rhs();
		if(lhs == t && !rhs->contains_term(t))
			return rhs;
		if(rhs ==t && !lhs->contains_term(t))
			return lhs;
		return NULL;
	}


	case ILP:
	{
		if(!phase) return NULL;
		ILPLeaf* ilp = (ILPLeaf*) this;
		if(ilp->get_operator() != ILP_EQ) return NULL;
		const map<Term*, long int> & elems = ilp->get_elems();
		if(elems.count(t) == 0) return NULL;
		long int coef = elems.find(t)->second;
		if(coef != 1 && coef != -1) return NULL;
		map<Term*, long int> new_elems;

		// If flip sign is false, only flip sign of constant
		// Otherwise, constant sign stays same, but all element signs flip
		bool flip_sign = false;
		if(coef == 1) flip_sign = true;
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			Term* cur_elem = it->first;
			long int cur_coef = it->second;
			if(cur_elem == t) continue;
			if(cur_elem->contains_term(t)) return NULL;
			if(flip_sign) {
				new_elems[cur_elem] = -cur_coef;
			}
			else new_elems[cur_elem] = cur_coef;
		}

		long int constant = ilp->get_constant();
		if(!flip_sign) constant = -constant;
		Term* at= ArithmeticTerm::make(new_elems, constant);
		return at;
	}

	case NOT:
	{
		Connective* not_c = (Connective*)this;
		CNode* inner = *not_c->get_operands().begin();
		return inner->contains_term_equality_internal(t, !phase);
	}
	case AND:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* cur = *it;
			Term* res = cur->contains_term_equality_internal(t, phase);
			if(res != NULL)
				return res;
		}
		return NULL;
	}
	default:
		assert(false);
	}

}

void CNode::collect_term_equalities(Term* t, set<Term*>& eqs)
{
	collect_term_equalities_internal(t, true, eqs);
}


void CNode::collect_term_equalities_internal(Term* t, bool phase, set<Term*> &
		equalities)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
	case UNIVERSAL:
	case MOD:
	case OR:
		return;
	case EQ:
	{
		if(!phase) return;
		EqLeaf* eq = (EqLeaf*) this;
		Term* lhs = eq->get_lhs();
		Term* rhs = eq->get_rhs();
		if(lhs == t && !rhs->contains_term(t))
			equalities.insert(rhs);
		if(rhs ==t && !lhs->contains_term(t))
			equalities.insert(lhs);
		return;
	}


	case ILP:
	{
		if(!phase) return;
		ILPLeaf* ilp = (ILPLeaf*) this;
		if(ilp->get_operator() != ILP_EQ) return;
		const map<Term*, long int> & elems = ilp->get_elems();
		if(elems.count(t) == 0) return;
		long int coef = elems.find(t)->second;
		if(coef != 1 && coef != -1) return;
		map<Term*, long int> new_elems;

		// If flip sign is false, only flip sign of constant
		// Otherwise, constant sign stays same, but all element signs flip
		bool flip_sign = false;
		if(coef == 1) flip_sign = true;
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++) {
			Term* cur_elem = it->first;
			long int cur_coef = it->second;
			if(cur_elem == t) continue;
			if(cur_elem->contains_term(t)) return;
			if(flip_sign) {
				new_elems[cur_elem] = -cur_coef;
			}
			else new_elems[cur_elem] = cur_coef;
		}

		long int constant = ilp->get_constant();
		if(!flip_sign) constant = -constant;
		Term* at= ArithmeticTerm::make(new_elems, constant);
		equalities.insert(at);
		return;
	}

	case NOT:
	{
		Connective* not_c = (Connective*)this;
		CNode* inner = *not_c->get_operands().begin();
		inner->collect_term_equalities_internal(t, !phase, equalities);
		return;
	}
	case AND:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* cur = *it;
			cur->collect_term_equalities_internal(t, phase, equalities);
		}
		return;
	}
	default:
		assert(false);
	}

}

void CNode::get_nested_terms(set<Term*> & terms, bool include_function_subterms,
		bool include_constants)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
	case UNIVERSAL:
		return;
	case MOD:
	{
		ModLeaf* ml = (ModLeaf*) this;
		ml->get_term()->get_nested_terms(terms, include_function_subterms,
				include_constants);
		return;
	}
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		eq->get_rhs()->get_nested_terms(terms, include_function_subterms,
				include_constants);
		eq->get_lhs()->get_nested_terms(terms, include_function_subterms,
				include_constants);
		return;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* cur = it->first;
			cur->get_nested_terms(terms, include_function_subterms,
					include_constants);
		}
		return;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++)
		{
			CNode* cur = *it;
			cur->get_nested_terms(terms, include_function_subterms,
					include_constants);

		}
		return;
	}
	default:
		assert(false);

	}


}

/*
 * Return the conjunction of the constraint
 * representing restrictions on terms that appear in
 * this formula.
 */
CNode* CNode::get_attribute_constraints()
{
	set<CNode*> attribs;
	get_attributes(attribs);
	return Connective::make_and(attribs);
}

void CNode::get_attributes(set<CNode*>& attributes)
{
	switch(get_type())
	{
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		eq->get_rhs()->get_attributes(attributes);
		eq->get_lhs()->get_attributes(attributes);
		break;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			t->get_attributes(attributes);
		}
		break;
	}
	case MOD:
	{
		ModLeaf* m = (ModLeaf*) this;
		Term* t = m->get_term();
		t->get_attributes(attributes);
		break;
	}
	case UNIVERSAL:
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		CNode* index_g = ql->get_index_guard();
		CNode* value_g = ql->get_value_guard();
		if(index_g != NULL) index_g->get_attributes(attributes);
		if(value_g != NULL) value_g->get_attributes(attributes);
		break;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*> & children = c->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* c = *it;
			c->get_attributes(attributes);
		}
		break;
	}
	default:
		break;

	}
}


void CNode::get_all_fun_ids(set<int> & ids)
{
	switch(get_type())
	{
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		eq->get_rhs()->get_all_fun_ids(ids);
		eq->get_lhs()->get_all_fun_ids(ids);
		break;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			t->get_all_fun_ids(ids);
		}
		break;
	}
	case MOD:
	{
		ModLeaf* m = (ModLeaf*) this;
		Term* t = m->get_term();
		t->get_all_fun_ids(ids);
		break;
	}
	case UNIVERSAL:
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		CNode* index_g = ql->get_index_guard();
		CNode* value_g = ql->get_value_guard();
		if(index_g != NULL) index_g->get_all_fun_ids(ids);
		if(value_g != NULL) value_g->get_all_fun_ids(ids);
		break;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*> & children = c->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* c = *it;
			c->get_all_fun_ids(ids);
		}
		break;
	}
	default:
		break;

	}
}

void CNode::get_all_first_arguments(set<int>& fn_ids, map<int, set<Term*> >&
		fn_id_to_first_arg)
{
	switch(get_type())
	{
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		Term* rhs = eq->get_rhs();
		Term* lhs = eq->get_lhs();
		rhs->get_all_first_arguments(fn_ids, fn_id_to_first_arg);
		lhs->get_all_first_arguments(fn_ids, fn_id_to_first_arg);
		return;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			t->get_all_first_arguments(fn_ids, fn_id_to_first_arg);
		}
		return;
	}
	case MOD:
	{
		ModLeaf* m = (ModLeaf*) this;
		Term* t = m->get_term();
		t->get_all_first_arguments(fn_ids, fn_id_to_first_arg);
		return;

	}
	case UNIVERSAL:
	{

		return;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*> & children = c->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* c = *it;
			c->get_all_first_arguments(fn_ids, fn_id_to_first_arg);
		}
		return;
	}
	default:
		return;
	}
}

CNode* CNode::replace_first_argument(map<int, Term*>& fun_id_to_replacement)
{
	switch(get_type())
	{
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		Term* rhs = eq->get_rhs();
		Term* lhs = eq->get_lhs();
		Term* new_rhs = rhs->replace_first_argument(fun_id_to_replacement);
		Term* new_lhs = lhs->replace_first_argument(fun_id_to_replacement);
		if(rhs != new_rhs || lhs != new_lhs) {
			return EqLeaf::make(new_lhs, new_rhs);
		}
		else return this;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		bool changed = false;
		map<Term*, long int> new_elems;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			long int c = it->second;
			Term* new_t = t->replace_first_argument(fun_id_to_replacement);
			if(new_t != t) changed = true;
			new_elems[new_t] += c;
		}
		if(!changed) return this;
		return ILPLeaf::make(ilp->get_operator(), new_elems, ilp->get_constant());
	}
	case MOD:
	{
		ModLeaf* m = (ModLeaf*) this;
		Term* t = m->get_term();
		Term* new_t = t->replace_first_argument(fun_id_to_replacement);
		if(t == new_t) return this;
		return ModLeaf::make(new_t, m->get_mod_constant());

	}
	case UNIVERSAL:
	{

		return this;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		set<CNode*> new_children;
		bool changed = false;
		const set<CNode*> & children = c->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* c = *it;
			CNode* new_c = c->replace_first_argument(fun_id_to_replacement);
			if(c != new_c) changed = true;
			new_children.insert(new_c);
		}
		if(!changed) return this;
		return Connective::make(c->get_type(), new_children);
	}
	default:
		return this;

	}
}


void CNode::get_all_ilp_terms(set<Term*>& ilp_terms)
{
	switch(get_type())
	{
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			ilp_terms.insert(t);
		}
		break;
	}
	case MOD:
	{
		ModLeaf* m = (ModLeaf*) this;
		Term* t = m->get_term();
		ilp_terms.insert(t);
		break;
	}
	case UNIVERSAL:
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		CNode* index_g = ql->get_index_guard();
		CNode* value_g = ql->get_value_guard();
		if(index_g != NULL) index_g->get_all_ilp_terms(ilp_terms);
		if(value_g != NULL) value_g->get_all_ilp_terms(ilp_terms);
		break;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*> & children = c->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* c = *it;
			c->get_all_ilp_terms(ilp_terms);
		}
		break;
	}
	default:
		break;

	}
}
CNode* CNode::rewrite_ilp_neqs(set<Term*>& ilp_terms)
{
	switch(get_type())
	{

	case NOT:
	{
		Connective* not_c = (Connective*) this;
		CNode* inner = *not_c->get_operands().begin();
		if(inner->get_type() == EQ)
		{
			EqLeaf* eq = (EqLeaf*)inner;
			Term* rhs = eq->get_rhs();
			Term* lhs = eq->get_lhs();
			if(ilp_terms.count(rhs) > 0 || ilp_terms.count(lhs) > 0)
			{
				CNode* l1 = ILPLeaf::make(rhs, lhs, ILP_LT);
				CNode* l2 =  ILPLeaf::make(rhs, lhs, ILP_GT);
				return Connective::make(OR, l1, l2);
			}
			else return this;
		}

		else if(inner->get_type() == ILP &&
				((ILPLeaf*)inner)->get_operator() == ILP_EQ)
		{
			ILPLeaf* ilp = (ILPLeaf*) inner;
			const map<Term*, long int >& elems = ilp->get_elems();
			Term* t1 = ArithmeticTerm::make(elems, 0);
			Term* constant = ConstantTerm::make(ilp->get_constant());
			CNode* l1 = ILPLeaf::make(t1, constant, ILP_LT);
			CNode* l2 = ILPLeaf::make(t1, constant, ILP_GT);
			return Connective::make(OR, l1, l2);

		}
		else return this;
	}


	case AND:
	case OR:
	{
		Connective* c = (Connective*) this;
		set<CNode*> new_children;
		bool changed = false;
		const set<CNode*> & children = c->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* c = *it;
			CNode* new_c = c->rewrite_ilp_neqs(ilp_terms);
			if(c!= new_c) changed =true;
			new_children.insert(new_c);
		}
		if(!changed) return this;
		return Connective::make(get_type(), new_children);
	}
	default:
		return this;

	}
}

void CNode::get_all_arguments(int fun_id, int arg_num, set<Term*> & args)
{
	switch(get_type())
	{
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		eq->get_rhs()->get_all_arguments(fun_id, arg_num, args);
		eq->get_lhs()->get_all_arguments(fun_id, arg_num, args);
		break;
	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			t->get_all_arguments(fun_id, arg_num, args);
		}
		break;
	}
	case MOD:
	{
		ModLeaf* m = (ModLeaf*) this;
		Term* t = m->get_term();
		t->get_all_arguments(fun_id, arg_num, args);
		break;
	}
	case UNIVERSAL:
	{
		QuantifiedLeaf* ql = (QuantifiedLeaf*) this;
		CNode* index_g = ql->get_index_guard();
		CNode* value_g = ql->get_value_guard();
		if(index_g != NULL) index_g->get_all_arguments(fun_id, arg_num, args);
		if(value_g != NULL) value_g->get_all_arguments(fun_id, arg_num, args);
		break;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*> & children = c->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* c = *it;
			c->get_all_arguments(fun_id, arg_num, args);
		}
		break;
	}
	default:
		break;

	}
}

/*
 * Returns another CNode that explicitly includes attributes on the
 * terms nested in this CNode.
 */

CNode* CNode::add_attributes(set<Term*>* which_terms)
{
	set<Term*> all_terms;
	get_nested_terms(all_terms, false, false);
	set<CNode*> attributes;
	set<Term*>::iterator it = all_terms.begin();
	for(; it!= all_terms.end(); it++)
	{
		Term* t = *it;
		if(which_terms!=NULL && which_terms->count(t) == 0) continue;
		t->get_attributes(attributes);
	}
	attributes.insert(this);
	return Connective::make_and(attributes);
}

void CNode::get_all_literals(set<CNode*> & leaves)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case UNIVERSAL:
	case MOD:
	case EQ:
	case ILP:
	case NOT:
	{
		Leaf* l = (Leaf*)this;
		leaves.insert(l);
		return;
	}

	case OR:
	case AND:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* cur = *it;
			cur->get_all_literals(leaves);
		}
		return;
	}
	default:
		return;
	}
}

void CNode::get_all_leaves(set<CNode*> & leaves)
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case UNIVERSAL:
	case MOD:
	case EQ:
	case ILP:
	{
		Leaf* l = (Leaf*)this;
		leaves.insert(l);
		return;
	}

	case OR:
	case AND:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& ops = c->get_operands();
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* cur = *it;
			cur->get_all_leaves(leaves);
		}
		return;
	}
	default:
		return;
	}
}

/*
 * Does this node contain a (universal) quantifier?
 */
bool CNode::has_quantifier() const
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
	case EQ:
	case ILP:
	case MOD:
		return false;
	case UNIVERSAL:
		return true;
	case AND:
	case OR:
	case NOT:
	{
		const set<CNode*> & children = ((Connective*)this)->get_operands();
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* cur = *it;
			if(cur->has_quantifier()) return true;
		}
		return false;
	}
	default:
		assert(false);

	}
}

bool CNode::contains_inequality()
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
	case EQ:
	case MOD:
	case UNIVERSAL:
		return false;
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		return(ilp->get_operator() != ILP_EQ);
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>&  ops = c->get_operands();
		set<CNode*>::iterator it = ops.begin();
		for(; it!= ops.end(); it++)
		{

			CNode* child = *it;
			if(child->contains_inequality()) return true;
		}
		return false;

	}
	default:
		assert(false);
	}
}

/*
 * Making canonical means reconstructing this CNode with ILP leaves
 * having the invariant that their first element always has
 * positive coefficient.
 */
CNode* CNode::make_canonical()
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
	case EQ:
	case MOD:
	case UNIVERSAL:
		return this;
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		if(ilp->get_operator() == ILP_EQ) return ilp;
		const map<Term*, long int>& elems = ilp->get_elems();
		if(elems.begin()->second > 0) return ilp;
		CNode* res = ILPLeaf::make(ILP_LEQ, elems, ilp->get_constant());
		return res;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;
		bool changed = false;
		set<CNode*> new_ops;
		const set<CNode*>&  old_ops = c->get_operands();
		set<CNode*>::iterator it = old_ops.begin();
		for(; it!= old_ops.end(); it++)
		{
			CNode* child = *it;
			CNode* new_child = child->make_canonical();
			new_ops.insert(new_child);
			if(new_child != child) changed = true;
		}

		if(!changed) return c;
		return Connective::make(c->get_type(), new_ops);

	}
	default:
		assert(false);
	}
}

int CNode::get_size()
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
	case EQ:
	case MOD:
	case UNIVERSAL:
	case ILP:
	case NOT:
		return 1;
	case AND:
	case OR:
	{
		Connective* c = (Connective*) this;
		if(c->size != -1) return c->size;
		const set<CNode*>&  ops = c->get_operands();
		set<CNode*>::iterator it = ops.begin();
		int size = 0;
		for(; it!= ops.end(); it++)
		{
			CNode* child = *it;
			size += child->get_size();
		}
		c->size = size;
		return size;

	}
	default:
		assert(false);
	}
}

bool CNode::check_canonical()
{
	switch(this->get_type())
	{
	case BOOLEAN_VAR:
	case TRUE_NODE:
	case FALSE_NODE:
	case EQ:
	case MOD:
	case UNIVERSAL:
		return true;
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		if(ilp->get_operator() == ILP_EQ) return true;
		const map<Term*, long int>& elems = ilp->get_elems();
		if(elems.begin()->second > 0) return true;
		return false;
	}
	case AND:
	case OR:
	case NOT:
	{
		Connective* c = (Connective*) this;;
		const set<CNode*>&  ops = c->get_operands();
		set<CNode*>::iterator it = ops.begin();
		for(; it!= ops.end(); it++)
		{
			CNode* child = *it;
			bool res = child->check_canonical();
			if(!res) return false;
		}
		return true;

	}
	default:
		assert(false);
	}
}

CNode* CNode::evaluate_assignment(map<CNode*, bool>& assignments)
{
	switch(this->get_type())
	{
	case TRUE_NODE:
	case FALSE_NODE:
		return this;
	case BOOLEAN_VAR:
	case EQ:
	case ILP:
	case MOD:
	case UNIVERSAL:
	{
		if(assignments.count(this) == 0) return this;
		if(assignments[this]) return True::make();
		else return False::make();

	}
	case NOT:
	case AND:
	case OR:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& children = c->get_operands();
		if(get_type() == NOT)
		{
			CNode* inner = *children.begin();
			return Connective::make_not(inner->evaluate_assignment(assignments));
		}

		set<CNode*> new_children;
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* cur = *it;
			CNode* cur_eval = cur->evaluate_assignment(assignments);
			if(get_type() == AND && cur_eval->get_type() == FALSE_NODE)
				return cur_eval;
			if(get_type() == OR && cur_eval->get_type() == TRUE_NODE)
				return cur_eval;
			new_children.insert(cur_eval);

		}

		return Connective::make(c->get_type(), new_children);


	}
	default:
		assert(false);
	}
}

CNode* CNode::evaluate_assignment(map<Term*, SatValue>& assignment)
{
	switch(this->get_type())
	{
	case TRUE_NODE:
	case FALSE_NODE:
		return this;
	case BOOLEAN_VAR:
	{
		return True::make();
	}
	case EQ:
	{
		EqLeaf* eq = (EqLeaf*) this;
		Term* t1 = eq->get_lhs();
		Term* t2 = eq->get_rhs();
		Term* t1_assign = t1->evalute_term(assignment);
		Term* t2_assign = t2->evalute_term(assignment);
		return EqLeaf::make(t1_assign, t2_assign);


	}
	case ILP:
	{
		ILPLeaf* ilp = (ILPLeaf*) this;
		map<Term*, long int> new_elems;
		const map<Term*, long int>& elems = ilp->get_elems();
		map<Term*, long int>::const_iterator it = elems.begin();
		for(; it!= elems.end(); it++)
		{
			Term* t = it->first;
			Term* t_res = t->evalute_term(assignment);
			new_elems[t_res] += it->second;
		}
		long int constant = ilp->get_constant();
		return ILPLeaf::make(ilp->get_operator(), new_elems, constant);

	}
	case MOD:
	{
		ModLeaf* mod = (ModLeaf*) this;
		Term* t = mod->get_term();
		Term *t_res = t->evalute_term(assignment);
		return ModLeaf::make(t_res, mod->get_mod_constant());

	}
	case NOT:
	case AND:
	case OR:
	{
		Connective* c = (Connective*) this;
		const set<CNode*>& children = c->get_operands();
		if(get_type() == NOT)
		{
			CNode* inner = *children.begin();
			return Connective::make_not(inner->evaluate_assignment(assignment));
		}

		set<CNode*> new_children;
		set<CNode*>::iterator it = children.begin();
		for(; it!= children.end(); it++)
		{
			CNode* cur = *it;
			CNode* cur_eval = cur->evaluate_assignment(assignment);
			if(get_type() == AND && cur_eval->get_type() == FALSE_NODE)
				return cur_eval;
			if(get_type() == OR && cur_eval->get_type() == TRUE_NODE)
				return cur_eval;
			new_children.insert(cur_eval);

		}

		return Connective::make(c->get_type(), new_children);


	}
	case UNIVERSAL:
	{
		return this;
	}
	default:
		assert(false);




	}
}

/*
 * Comparison between different refactoring options
 */
 inline bool CNode::refactor_lessthan::operator()
		 (const pair<CNode*, set<CNode*> >& ref1,
			  const pair<CNode*, set<CNode*> >& ref2) const
{
	 bool res;
  int num_appear1 = ref1.second.size();
  int num_appear2 = ref2.second.size();
  int score1 = ref1.first->get_size() * num_appear1;
  int score2 = ref2.first->get_size() * num_appear2;
  if(score1 < score2) res =false;
  else if(score1 > score2) res = true;
  else if(num_appear1 < num_appear2) res = false;
  else if(num_appear1 > num_appear2) res = true;
  else res = ref1.first < ref2.first;
  return res;

}

CNode* CNode::to_cnf()
{
	switch(get_type())
	{
	case AND:
	{
		Connective* and_c = (Connective*) this;

		set<CNode*> new_ops;
		const set<CNode*>& ops =  and_c->get_operands();
		set<CNode*>::iterator it = ops.begin();
		for(; it!= ops.end(); it++)
		{
			CNode* cur = *it;
			CNode* new_cur = cur->to_cnf();
			new_ops.insert(new_cur);

		}
		return Connective::make_and(new_ops);
	}
	case OR:
	{
		Connective* or_c = (Connective*) this;
		const set<CNode*>& ops =  or_c->get_operands();
		assert(ops.size() >= 2);

		/*
		 * To distribute, we need a child that is an AND.
		 */
		Connective* and_child = NULL;
		set<CNode*> to_distribute;
		set<CNode*>::const_iterator it = ops.begin();
		for(; it!= ops.end(); it++) {
			CNode* cur = *it;
			if(and_child == NULL && cur->get_type() == AND) {
				and_child = static_cast<Connective*>(cur);
			}
			else to_distribute.insert(cur);
		}

		if(and_child == NULL) return this;
		CNode* dist_c = Connective::make_or(to_distribute);


		set<CNode*> cnf_ops;
		/*
		 * Iterate over the children of AND child and distribute
		 */
		const set<CNode*>& and_children = and_child->get_operands();
		for(it = and_children.begin(); it!= and_children.end(); it++)
		{
			CNode* cur_child = *it;
			CNode* new_op = Connective::make(OR, cur_child, dist_c);
			CNode* cnf_op = new_op->to_cnf();
			cnf_ops.insert(cnf_op);


		}

		return Connective::make_and(cnf_ops);



	}

	default:
		return this;
	}
}

int CNode::num_disjuncts()
{
	if(is_literal()) return 0;
	assert(this->is_connective());
	Connective* c = static_cast<Connective*>(this);
	int res = 0;
	if(c->is_disjunct()) res = 1;

	const set<CNode*>& children = c->get_operands();
	set<CNode*>::const_iterator it = children.begin();
	for(; it != children.end(); it++) {
		res += (*it)->num_disjuncts();
	}
	return res;
}


CNode* CNode::divide(long int constant, Term* t)
 {
	 if(is_connective())
	 {
		 Connective* c = (Connective*)this;
		 bool changed = false;
		 set<CNode*> new_ops;
		 const set<CNode*>& ops = c->get_operands();
		 set<CNode*>::iterator it = ops.begin();
		 for( ;it!= ops.end(); it++){
			 CNode* op = *it;
			 CNode* new_op = op->divide(constant,t);
			 if(new_op != op) changed = true;
			 new_ops.insert(new_op);
		 }

		 if(changed) return Connective::make(c->get_type(), new_ops);
	 }

	 return this;
 }


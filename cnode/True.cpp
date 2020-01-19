/*
 * True.cpp
 *
 *  Created on: Jan 22, 2009
 *      Author: tdillig
 */

#include "True.h"

True::True()
{
	hash_c = ~0;
	node_type = TRUE_NODE;
	negations_folded = this;

}

True::~True()
{

}

CNode* True::make()
{
	return CNode::true_node();
}

bool True::operator==(const CNode& other)
{
	return(other.get_type() == TRUE_NODE);
}
string True::to_string()
{
	return "true";
}

CNode* True::substitute(map<Term*, Term*>& subs)
{
	return this;
}



/*
 * False.cpp
 *
 *  Created on: Jan 22, 2009
 *      Author: tdillig
 */

#include "False.h"


False::False()
{
	hash_c = 0;
	node_type = FALSE_NODE;
	negations_folded = this;

}

False::~False()
{

}

CNode* False::make()
{
	return CNode::false_node();
}


bool False::operator==(const CNode& other)
{
	return(other.get_type() == FALSE_NODE);
}
string False::to_string()
{
	return "false";
}

CNode* False::substitute(map<Term*, Term*>& subs)
{
	return this;
}




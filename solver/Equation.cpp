/*
 * Equation.cpp
 *
 *  Created on: Dec 9, 2008
 *      Author: tdillig
 */

#include "Equation.h"


ostream& operator <<(ostream &os,const Equation &_obj)
{
	Equation& obj = (Equation&) _obj;
	os<<obj.to_string();
	return os;
}

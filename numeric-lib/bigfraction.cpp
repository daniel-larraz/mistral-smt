/*
 * bigfraction.cpp
 *
 *  Created on: Dec 8, 2008
 *      Author: tdillig
 */

#include "bigfraction.h"


ostream& operator <<(ostream &os,const bigfraction &_obj)
{
	bigfraction &obj = (bigfraction &)_obj;
	os << obj.to_string();
	return os;
}

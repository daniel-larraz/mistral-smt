/*
 * matrix.cpp
 *
 *  Created on: Dec 6, 2008
 *      Author: tdillig
 */

#include "matrix.h"
#include <assert.h>

ostream& operator <<(ostream &os,const matrix &_obj)
{
	matrix & obj = (matrix&) _obj;
    os << obj.to_string();
    return os;
}





/*
 * Matrix.cpp
 *
 *  Created on: Dec 10, 2008
 *      Author: tdillig
 */

#include "Matrix.h"

ostream& operator <<(ostream &os,const Matrix &_obj)
{
	Matrix& obj = (Matrix&)_obj;
	os<<obj.to_string();
	return os;
}

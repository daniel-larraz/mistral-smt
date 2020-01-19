/*
 * SatValue.h
 *
 *  Created on: Aug 3, 2009
 *      Author: tdillig
 */

#ifndef SATVALUE_H_
#define SATVALUE_H_

#include "bignum.h"


/*
 * Represents a satisfying assignment.
 * If the variable is known to be an integer (i.e.
 * involved in a linear system), the satisfying
 * assignment is an integer. Otherwise,
 * we assign some made up element that is
 * unique for each equivalence class.
 */
class SatValue {
public:

	bool integer;
	//If integer, the actual integer value, otherwise a unique id per
	//equivalence class.
	bignum value;

	string to_string()
	{
		if(!integer)
			return "e"+value.to_string();
		return value.to_string();
	}

	SatValue();
	~SatValue();
};

#endif /* SATVALUE_H_ */

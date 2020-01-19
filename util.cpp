/*
 * util.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include <sstream>
#include "util.h"
#include "mistral.h"


string float_to_string(float i)
{
	stringstream s;
	s << i;
	string res;
	s >> res;
	return res;
}


string int_to_string(long i)
{
	/*
	stringstream s;
	s << i;
	string res;
	s >> res;
	*/
	char temp[100];
	sprintf(temp, "%ld",  i);
	string res = temp;


	return res;
}
/*
void address_to_string(string & res, void* v)
{
	char temp[100];
	sprintf(temp, "%lu", (unsigned long int) v);
	res.append(temp);

}*/

long int string_to_int(string s)
{
	stringstream ss;
	ss<< s;
	long int res;
	ss >> res;
	return res;
}





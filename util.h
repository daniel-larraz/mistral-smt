/*
 * util.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef UTIL_H_
#define UTIL_H_

#include <string>
#include <vector>
#include <stdlib.h>
using namespace std;

//#define DWORD_ALIGN(x) ((((x)+3)/4)*4)

string int_to_string(long l);
long int string_to_int(string s);
static inline void  address_to_string(string & res, void* v)
{
	char temp[100];
	temp[0] = 'a';
	sprintf(temp+1, "%lu", (unsigned long int) v);
	res.append(temp);
}
string float_to_string(float f);
string linear_system_to_string(int* matrix, int num_rows, int num_cols,
		vector<string>& vars);
inline bool have_same_sign(long int a, long int b)
{
	long int temp = a ^ b;
	return !(temp & (1L << 63));

}


inline long int gcd(long int _a, long int _b)
{
	long int a = labs(_a);
	long int b = labs(_b);

	int t;
	while(b!=0){
		t = a;
		a = b;
		b = t % b;
	}
	return a;
}

inline long int lcm(long int a, long int b)
{
	long int d = gcd(a, b);
	return labs(a*b/d);
}



#endif /* UTIL_H_ */

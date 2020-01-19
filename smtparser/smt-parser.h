/*
 * mistral-parser.h
 *
 *  Created on: Nov 15, 2011
 *      Author: isil
 */


#ifndef MISTRAL_SMT_PARSER_H_
#define MISTRAL_SMT_PARSER_H_

#include <string>
using namespace std;




CNode* smtlib_parse_constraint(const string & s, void (*write_fn)(string));




#endif /* MISTRAL_SMT_PARSER_H_ */

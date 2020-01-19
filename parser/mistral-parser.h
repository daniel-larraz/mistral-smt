/*
 * mistral-parser.h
 *
 *  Created on: Nov 15, 2011
 *      Author: isil
 */


#ifndef MISTRAL_PARSER_H_
#define MISTRAL_PARSER_H_

#include <string>
using namespace std;




CNode* parse_constraint(const string & s, void (*write_fn)(string));
Term* parse_term(const string & s, void (*write_fn)(string));



#endif /* MISTRAL_PARSER_H_ */

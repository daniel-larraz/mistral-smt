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

enum SmtCommand { None, CheckSat, GetAbduct };

struct SmtResult {
  SmtCommand smt_command;
  CNode* constraint;
  Term* abduct_name;
  CNode* conclusion;

  SmtResult() :
    smt_command(None),
    constraint(nullptr),
    abduct_name(nullptr),
    conclusion(nullptr) {}

  SmtResult(CNode* constr) :
    smt_command(CheckSat),
    constraint(constr),
    abduct_name(nullptr),
    conclusion(nullptr)
  {}

  SmtResult(CNode* constr, Term* abd_name, CNode* concl) :
    smt_command(GetAbduct),
    constraint(constr),
    abduct_name(abd_name),
    conclusion(concl)
  {}
};


SmtResult smtlib_parse_constraint(const string & s, void (*write_fn)(string));




#endif /* MISTRAL_SMT_PARSER_H_ */

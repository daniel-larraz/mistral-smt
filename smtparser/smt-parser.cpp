#include <malloc.h>
#include "smt-parser-defs.h"
#include <stdlib.h>
#include <iostream>
#include "smtparser.hpp"
#include "cnode.h"


CNode* smt_res_constraint;
Term* smt_res_term;
void (*smt_parser_error_fn)(string);
int smt_curr_lineno;

using namespace std;
int zzlex();
int zzparse();
extern int zz_scan_string(const char* c);



CNode* smtlib_parse_constraint(const string & s, void (*write_fn)(string))
{
	smt_curr_lineno = 1;
	smt_res_constraint = NULL;
	smt_res_term = NULL;
	smt_parser_error_fn = write_fn;
	string t = s;
	zz_scan_string(t.c_str());
	if(zzparse()!= 0) {
		smt_res_term = NULL;
		smt_res_constraint = NULL;
	}
	if(smt_res_constraint == NULL && smt_res_term != NULL && write_fn != NULL) {
		write_fn("Error: Expected constraint, not term.");
	}
	return smt_res_constraint;
}


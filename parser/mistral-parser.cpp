#include <malloc.h>
#include "mistral-parser-defs.h"
#include <stdlib.h>
#include <iostream>
#include "parser.hpp"
#include "cnode.h"


CNode* res_constraint;
Term* res_term;
void (*parser_error_fn)(string);
int curr_lineno;

using namespace std;
int yylex();
int yyparse();
extern int yy_scan_string(const char* c);



CNode* parse_constraint(const string & s, void (*write_fn)(string))
{
	curr_lineno = 1;
	res_constraint = NULL;
	res_term = NULL;
	parser_error_fn = write_fn;
	string t = s+ ";";
	yy_scan_string(t.c_str());
	if(yyparse()!= 0) {
		res_term = NULL;
		res_constraint = NULL;
	}
	if(res_constraint == NULL && res_term != NULL && write_fn != NULL) {
		write_fn("Error: Expected constraint, not term.");
	}
	return res_constraint;
}

Term* parse_term(const string & s, void (*write_fn)(string))
{
	curr_lineno = 1;
	res_constraint = NULL;
	res_term = NULL;
	parser_error_fn = write_fn;
	string t =  "?" + s+ ";";
	yy_scan_string(t.c_str());
	if(yyparse()!= 0) {
		res_term = NULL;
		res_constraint = NULL;
	}
	if(res_term == NULL && res_constraint != NULL && write_fn != NULL) {
		write_fn("Error: Expected term, not constraint.");
	}
	return res_term;
}




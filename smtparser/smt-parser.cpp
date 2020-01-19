#include <malloc.h>
#include "smt-parser-defs.h"
#include <stdlib.h>
#include <iostream>
#include "smtparser.hpp"
#include "cnode.h"


CNode* smt_res_constraint;
Term* smt_res_term;

int smt_ite_id;
vector<IteInfo> smt_ite_expressions;

void (*smt_parser_error_fn)(string);
int smt_curr_lineno;

using namespace std;
int zzlex();
int zzparse();
extern int zz_scan_string(const char* c);



CNode* smtlib_parse_constraint(const string & s, void (*write_fn)(string))
{
        smt_ite_id = 1;
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

        if (!smt_ite_expressions.empty()) {
          set<CNode*> ops;
          for (auto& ite_info : smt_ite_expressions) {
            CNode* eq1 = EqLeaf::make(ite_info.var, ite_info.term1); 
            CNode* c1 = ite_info.condition;
            CNode* impl1 = Connective::make_implies(c1, eq1);

            CNode* eq2 = EqLeaf::make(ite_info.var, ite_info.term2);
            CNode* c2 = Connective::make_not(ite_info.condition);
            CNode* impl2 = Connective::make_implies(c2, eq2);

            ops.insert(impl1);
            ops.insert(impl2);
          }
          CNode* ite_defs = Connective::make_and(ops);
          smt_res_constraint = Connective::make(AND, smt_res_constraint, ite_defs);
        }

	return smt_res_constraint;
}


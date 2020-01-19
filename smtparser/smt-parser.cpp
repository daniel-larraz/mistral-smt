#include <malloc.h>
#include "smt-parser-defs.h"
#include <stdlib.h>
#include <iostream>
#include "smt-parser.h"
#include "cnode.h"

bool smt_res_check_sat_found;
Term* smt_res_abduct_id;
CNode* smt_res_aduct_conclusion;

set<CNode*> smt_res_asserts;

int smt_ite_id;
vector<IteInfo> smt_ite_expressions;

void (*smt_parser_error_fn)(string);
int smt_curr_lineno;

using namespace std;
int zzlex();
int zzparse();
extern int zz_scan_string(const char* c);



SmtResult smtlib_parse_constraint(const string & s, void (*write_fn)(string))
{
        smt_ite_id = 1;
	smt_curr_lineno = 1;
	smt_res_check_sat_found = false;
        smt_res_abduct_id = NULL;
        smt_res_aduct_conclusion = NULL;
	smt_parser_error_fn = write_fn;
	string t = s;
	zz_scan_string(t.c_str());
	if(zzparse()!= 0) {
                smt_res_abduct_id = NULL;
                smt_res_aduct_conclusion = NULL;
                return SmtResult();
	}

        if (!smt_res_check_sat_found && smt_res_abduct_id == NULL) {
                return SmtResult();
        }

        if (!smt_ite_expressions.empty()) {
          for (auto& ite_info : smt_ite_expressions) {
            CNode* eq1 = EqLeaf::make(ite_info.var, ite_info.term1); 
            CNode* c1 = ite_info.condition;
            CNode* impl1 = Connective::make_implies(c1, eq1);

            CNode* eq2 = EqLeaf::make(ite_info.var, ite_info.term2);
            CNode* c2 = Connective::make_not(ite_info.condition);
            CNode* impl2 = Connective::make_implies(c2, eq2);

            smt_res_asserts.insert(impl1);
            smt_res_asserts.insert(impl2);
          }
        }

        CNode* smt_res_constraint = Connective::make_and(smt_res_asserts);
        if(smt_res_abduct_id == NULL) { // CheckSat
	  return SmtResult(smt_res_constraint);
        }
        else { // GetAbduct
          return SmtResult(smt_res_constraint, smt_res_abduct_id, smt_res_aduct_conclusion);
        }
}


#ifndef MISTRAL_SMT_PARSER_DEFS_H_
#define MISTRAL_SMT_PARSER_DEFS_H_

#include "cnode.h"
#include "term.h"
#include <string>
using namespace std;

union parse_res_union
{
  CNode* c;
  Term* t;
  string* s;
};

enum PARSE_KIND {PARSE_CNODE, PARSE_TERM, PARSE_STRING};

struct parse_result
{
	PARSE_KIND kind;
	parse_res_union res;
};



//typedef parse_result YYSTYPE;
#define YYSTYPE parse_result

extern YYSTYPE yylval;

#define YYINITDEPTH 100000


extern CNode* smt_res_constraint;
extern Term* smt_res_term;

extern int smt_curr_lineno;
extern void (*smt_parser_error_fn)(string);

#endif /* MISTRAL_SMT_PARSER_DEFS_H_ */

class ScopeTable
{
private:
	vector<map<string, Term*> > mappings;
public:

	ScopeTable()
	{

	}
	void push()
	{
		mappings.push_back(map<string, Term*>());
	}
	void pop() {
		assert(mappings.size() > 0);
		mappings.pop_back();
	}
	void put(const string & name, Term* t) {
		(*mappings.rbegin())[name] = t;
	}
	Term* get(const string& name)
	{
		vector<map<string, Term*> >::reverse_iterator it = mappings.rbegin();
		for(; it != mappings.rend(); it++) {
			const map<string, Term*> & cur = *it;
			if(cur.count(name) > 0) return cur.find(name)->second;
		}
		return NULL;
	}

};

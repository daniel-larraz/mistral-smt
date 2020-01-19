#ifndef MISTRAL_PARSER_DEFS_H_
#define MISTRAL_PARSER_DEFS_H_

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


extern CNode* res_constraint;
extern Term* res_term;

extern int curr_lineno;
extern void (*parser_error_fn)(string);

#endif /* MISTRAL_PARSER_DEFS_H_ */

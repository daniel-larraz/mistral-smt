
 %{
#include "smt-parser-defs.h"
#include <malloc.h>
#include <stdlib.h>
#include <iostream>
#include "cnode.h"
#include "term.h"
#include "../util.h"


struct pp
{
	map<Term*, Term*>* t_sub;
	map<CNode*, CNode*>* c_sub;
};

using namespace std;
int yylex();
extern int yy_scan_string(const char* c);
int yyerror(const char* p)
{ 
  if(smt_parser_error_fn != NULL) {
    smt_parser_error_fn("Error at line " + int_to_string(smt_curr_lineno) + ": " + string(p));
  }
  return 1;
};

 
ScopeTable st;


%}



/* BISON Declarations */
%name-prefix="zz"
%token 

TOKEN_PLUS 
TOKEN_MINUS 
TOKEN_IDENTIFIER
TOKEN_TIMES 
TOKEN_DIVIDE 
TOKEN_INT 
TOKEN_LPAREN 
TOKEN_RPAREN 
TOKEN_AND 
TOKEN_OR 
TOKEN_NOT

TOKEN_EQ 
TOKEN_GT 
TOKEN_GEQ 
TOKEN_LT 
TOKEN_LEQ 

TOKEN_COND
TOKEN_ERROR
TOKEN_LET
TOKEN_ASSERT



%nonassoc EXPR
%nonassoc TOKEN_PRINT 
%left TOKEN_EQ TOKEN_NEQ TOKEN_LT TOKEN_LEQ TOKEN_GT TOKEN_GEQ
%left TOKEN_AND TOKEN_OR
%left TOKEN_PLUS TOKEN_MINUS
%left TOKEN_TIMES TOKEN_DIVIDE
%nonassoc TOKEN_ISNIL
%right TOKEN_CONS
%nonassoc TOKEN_HD TOKEN_TL





%%


program: assert_list
{
	assert($1.kind == PARSE_CNODE);
	CNode* t = $1.res.c;
	smt_res_constraint = t;
}


assert_list: assert_list assertion
{
  assert($1.kind == PARSE_CNODE);
  assert($2.kind == PARSE_CNODE);
  CNode* c1 = $1.res.c;
  CNode* c2 = $2.res.c;
  $$.kind = PARSE_CNODE;
  $$.res.c = Connective::make(AND, c1, c2);
}
|
assertion
{
$$ = $1;
}

assertion: TOKEN_LPAREN TOKEN_ASSERT constraint TOKEN_RPAREN
{
	$$ = $3;
}

constraint: TOKEN_LPAREN TOKEN_AND and_list TOKEN_RPAREN
{
	$$ = $3;
}
|
TOKEN_LPAREN TOKEN_OR or_list TOKEN_RPAREN
{
	$$ = $3;
}
|
TOKEN_LPAREN TOKEN_NOT constraint TOKEN_RPAREN
{
  assert($3.kind == PARSE_CNODE);
  CNode* c = $3.res.c;
  $$.kind = PARSE_CNODE;
  $$.res.c = Connective::make_not(c);
  
}
|
TOKEN_LPAREN constraint TOKEN_RPAREN
{
	$$ = $2;
}
|
TOKEN_LPAREN TOKEN_EQ exp exp TOKEN_RPAREN
{
    assert($3.kind == PARSE_TERM);
    assert($4.kind == PARSE_TERM);
    Term* t1 = $3.res.t;
    Term* t2 = $4.res.t;
    $$.kind = PARSE_CNODE;
    $$.res.c = EqLeaf::make(t1, t2);
} 
|
TOKEN_LPAREN TOKEN_GT exp exp TOKEN_RPAREN
{
    assert($3.kind == PARSE_TERM);
    assert($4.kind == PARSE_TERM);
    Term* t1 = $3.res.t;
    Term* t2 = $4.res.t;
    $$.kind = PARSE_CNODE;
    $$.res.c = ILPLeaf::make(t1, t2, ILP_GT);
} 
|
TOKEN_LPAREN TOKEN_GEQ exp exp TOKEN_RPAREN
{
    assert($3.kind == PARSE_TERM);
    assert($4.kind == PARSE_TERM);
    Term* t1 = $3.res.t;
    Term* t2 = $4.res.t;
    $$.kind = PARSE_CNODE;
    $$.res.c = ILPLeaf::make(t1, t2, ILP_GEQ);
} 
|
TOKEN_LPAREN TOKEN_LT exp exp TOKEN_RPAREN
{
    assert($3.kind == PARSE_TERM);
    assert($4.kind == PARSE_TERM);
    Term* t1 = $3.res.t;
    Term* t2 = $4.res.t;
    $$.kind = PARSE_CNODE;
    $$.res.c = ILPLeaf::make(t1, t2, ILP_LT);
} 
|
TOKEN_LPAREN TOKEN_LEQ exp exp TOKEN_RPAREN
{
 	assert($3.kind == PARSE_TERM);
    assert($4.kind == PARSE_TERM);
    Term* t1 = $3.res.t;
    Term* t2 = $4.res.t;
    $$.kind = PARSE_CNODE;
    $$.res.c = ILPLeaf::make(t1, t2, ILP_LEQ);
} 
|
TOKEN_LPAREN TOKEN_LET TOKEN_LPAREN  let_list TOKEN_RPAREN constraint TOKEN_RPAREN
{
     assert($4.kind == (PARSE_KIND)99);
     
     

     assert($6.kind == PARSE_CNODE);
     pp* p = (pp*)  $4.res.t;
     
     map<Term*, Term*>* subs =  p->t_sub;
      map<CNode*, CNode*>* subs_c =  p->c_sub;
     
     
     CNode* t = $6.res.c;
     //cout << "Term before: " << t->to_string() << endl;
     t = t->substitute(*subs);
     t = t->substitute(*subs_c);
     //  cout << "Term after: " << t->to_string() << endl;
     delete subs;
     delete subs_c;
     delete p;
     $$.kind = PARSE_CNODE;
      $$.res.c = t;   
} 



exp: TOKEN_INT
{
	$$ = $1;
}
| TOKEN_IDENTIFIER
{
	$$ = $1;
}
|
TOKEN_LPAREN exp TOKEN_RPAREN
{
	$$ = $2;
}
|
TOKEN_LPAREN TOKEN_LET TOKEN_LPAREN  let_list TOKEN_RPAREN exp TOKEN_RPAREN
{
     assert($4.kind == (PARSE_KIND)99);
     pp* p = (pp*)  $4.res.t;
     map<Term*, Term*>* subs =  (map<Term*, Term*>*) p->t_sub;
     assert($6.kind == PARSE_TERM);
     Term* t = $6.res.t;
   //  cout << "Term before: " << t->to_string() << endl;
     t = t->substitute(*subs);
     //  cout << "Term after: " << t->to_string() << endl;
     delete subs;
     delete p;
     $$.kind = PARSE_TERM;
      $$.res.t = t;   
} 
| TOKEN_LPAREN TOKEN_PLUS plus_list TOKEN_RPAREN
{
 	$$ = $3;
    
} 
|
TOKEN_LPAREN TOKEN_MINUS exp minus_list TOKEN_RPAREN
{
 	assert($3.kind == PARSE_TERM);
    assert($4.kind == PARSE_TERM);
    Term* t1 = $3.res.t;
    Term* t2 = $4.res.t;
    $$.kind = PARSE_TERM;
    map<Term*, long int> terms;
    terms[t1]+=1;
    terms[t2]-=1;
    $$.res.t = ArithmeticTerm::make(terms, 0);
} 
|
TOKEN_LPAREN TOKEN_MINUS exp  TOKEN_RPAREN
{
    assert($3.kind == PARSE_TERM);
    Term* t1 = $3.res.t;
    $$.kind = PARSE_TERM;
    map<Term*, long int> terms;
    terms[t1]-=1;
    $$.res.t = ArithmeticTerm::make(terms, 0);
} 

|
TOKEN_LPAREN TOKEN_TIMES exp exp TOKEN_RPAREN
{
   	assert($3.kind == PARSE_TERM);
    assert($4.kind == PARSE_TERM);
    Term* t1 = $3.res.t;
    Term* t2 = $4.res.t;
    ConstantTerm* ct = NULL;
    Term* other = NULL;
    if(t1->get_term_type() == CONSTANT_TERM){
    	ct = static_cast<ConstantTerm*>(t1);
    	other = t2;
    }
    else if(t2->get_term_type() == CONSTANT_TERM){
    	ct = static_cast<ConstantTerm*>(t2);
    	other = t1;
    }
    if(ct == NULL) {
    	zzerror("Non-linear constraint");
    	YYERROR;
    }
    
    
    $$.kind = PARSE_TERM;
    map<Term*, long int> terms;
    terms[other]=ct->get_constant();
    $$.res.t = ArithmeticTerm::make(terms, 0);
} 













and_list: and_list constraint
{
  assert($1.kind == PARSE_CNODE);
  assert($2.kind == PARSE_CNODE);
  CNode* c1 = $1.res.c;
  CNode* c2 = $2.res.c;
  $$.kind = PARSE_CNODE;
  $$.res.c = Connective::make(AND, c1, c2);
}
|
constraint
{
 $$ = $1;
}


or_list: or_list constraint
{
  assert($1.kind == PARSE_CNODE);
  assert($2.kind == PARSE_CNODE);
  CNode* c1 = $1.res.c;
  CNode* c2 = $2.res.c;
  $$.kind = PARSE_CNODE;
  $$.res.c = Connective::make(OR, c1, c2);
}
|
constraint
{
 $$ = $1;
}





plus_list: plus_list exp
{
 	assert($1.kind == PARSE_TERM);
    assert($2.kind == PARSE_TERM);
    Term* t1 = $1.res.t;
    Term* t2 = $2.res.t;
    $$.kind = PARSE_TERM;
    map<Term*, long int> terms;
    terms[t1]+=1;
    terms[t2]+=1;
    $$.res.t = ArithmeticTerm::make(terms, 0);
}
|
exp
{
 $$ = $1;
}



minus_list: plus_list exp
{
 	assert($1.kind == PARSE_TERM);
    assert($2.kind == PARSE_TERM);
    Term* t1 = $1.res.t;
    Term* t2 = $2.res.t;
    $$.kind = PARSE_TERM;
    map<Term*, long int> terms;
    terms[t1]+=1;
    terms[t2]-=1;
    $$.res.t = ArithmeticTerm::make(terms, 0);
}
|
exp
{
 $$ = $1;
}





let_list: let_list let_elem
{
	pp* p1 = (pp*)$1.res.t;
	pp* p2 = (pp*)$2.res.t;

	{
	  map<Term*, Term*>* subs1 = (map<Term*, Term*>* )p1->t_sub;
	  map<Term*, Term*>* subs2 = (map<Term*, Term*>* )p2->t_sub;
	  for(map<Term*, Term*>::iterator it = subs2->begin(); it != subs2->end();
	  	it++)
	  	{
	  	(*subs1)[it->first] = it->second;
	  	}
	  delete subs2;
	}
	
	{
	  map<CNode*, CNode*>* subs1 = (map<CNode*, CNode*>* )p1->c_sub;
	  map<CNode*, CNode*>* subs2 = (map<CNode*, CNode*>* )p2->c_sub;
	  for(map<CNode*, CNode*>::iterator it = subs2->begin(); it != subs2->end();
	  	it++)
	  	{
	  	(*subs1)[it->first] = it->second;
	  	}
	  delete subs2;
	}
	delete p2;
	
	  
	  
	  $$.kind = (PARSE_KIND)99;
      $$.res.t = (Term*) p1;
}
|
let_elem
{
 $$ = $1;
}


let_elem: TOKEN_LPAREN exp exp TOKEN_RPAREN
{
  map<Term*, Term*>* subs = new  map<Term*, Term*>();
  assert($2.kind == PARSE_TERM);
  assert($3.kind == PARSE_TERM);
  Term* t1 = $2.res.t;
  Term* t2 = $3.res.t;
  (*subs)[t1] = t2;
  pp* p = new pp;
  p->t_sub = subs;
  p->c_sub = new map<CNode*, CNode*>();
  $$.kind = (PARSE_KIND)99;
  $$.res.t = (Term*) p;
}
| TOKEN_LPAREN constraint constraint TOKEN_RPAREN
{
  map<CNode*, CNode*>* subs = new  map<CNode*, CNode*>();
  assert($2.kind == PARSE_CNODE);
  assert($3.kind == PARSE_CNODE);
  CNode* t1 = $2.res.c;
  CNode* t2 = $3.res.c;
  (*subs)[t1] = t2;
  pp* p = new pp;
  p->t_sub = new map<Term*, Term*>();
  p->c_sub = subs;
  $$.kind = (PARSE_KIND)99;
  $$.res.t = (Term*) p;
}




 %{
#include "mistral-parser-defs.h"
#include <malloc.h>
#include <stdlib.h>
#include <iostream>
#include "cnode.h"
#include "term.h"
#include "../util.h"




using namespace std;
int yylex();
extern int yy_scan_string(const char* c);
int yyerror(const char* p)
{ 
  if(parser_error_fn != NULL) {
    parser_error_fn("Error at line " + int_to_string(curr_lineno) + ": " + string(p));
  }
  return 1;
};



 



%}
/* BISON Declarations */
%token TOKEN_PLUS TOKEN_MINUS TOKEN_TIMES TOKEN_MOD TOKEN_LPAREN TOKEN_RPAREN TOKEN_INT_CONSTANT TOKEN_VAR_IDENTIFIER TOKEN_FUN_IDENTIFIER TOKEN_COMMA TOKEN_NOT TOKEN_AND TOKEN_OR TOKEN_IMPLIES
TOKEN_GT TOKEN_GEQ TOKEN_LT TOKEN_LEQ TOKEN_EQ TOKEN_NEQ TOKEN_TRUE TOKEN_FALSE TOKEN_BOOL_VAR_ID TOKEN_SPECIAL_TERM



%nonassoc TOKEN_RPAREN
%nonassoc TOKEN_LPAREN


%right TOKEN_IMPLIES
%right TOKEN_OR
%right TOKEN_AND

%nonassoc TOKEN_NOT



%left TOKEN_PLUS TOKEN_MINUS
%left TOKEN_TIMES TOKEN_DIVIDE

%nonassoc TOKEN_LOWER

 

 
%%  
 
 
input: constraint
      {
      assert($1.kind == PARSE_CNODE);
	CNode* t = $1.res.c;
	res_constraint = t;
      }
      |
      TOKEN_SPECIAL_TERM term
      {
      assert($2.kind == PARSE_TERM);
	Term* t = $2.res.t;
	res_term = t;
      };

  
constraint:
    leaf
    {
      $$ = $1;
    }
    | TOKEN_NOT constraint
    {
      CNode* c = $2.res.c;
      CNode* not_c = Connective::make_not(c);
      $$.res.c = not_c;
      $$.kind = PARSE_CNODE;
    }
  | constraint TOKEN_AND constraint
   {
      CNode* c1=$1.res.c;
      CNode* c2 = $3.res.c;
      CNode* c = Connective::make(AND, c1, c2);
      $$.res.c = c;
      $$.kind = PARSE_CNODE;

    }
  | constraint TOKEN_OR constraint
   {
      CNode* c1=$1.res.c;
      CNode* c2 = $3.res.c;
      CNode* c = Connective::make(OR, c1, c2);
      $$.res.c = c;
      $$.kind = PARSE_CNODE;

    }

  | constraint TOKEN_IMPLIES constraint
   {
      CNode* c1=$1.res.c;
      CNode* c2 = $3.res.c;
      CNode* c = Connective::make_implies(c1, c2);
      $$.res.c = c;
      $$.kind = PARSE_CNODE;

    }

   | TOKEN_LPAREN constraint TOKEN_RPAREN
    {
      $$ = $2;
    }

;

leaf:
  term TOKEN_GT term
  {
    Term* t1 = $1.res.t;
    Term* t2 = $3.res.t;
    CNode* ilp = ILPLeaf::make(t1, t2, ILP_GT);
    $$.res.c = ilp;
    $$.kind = PARSE_CNODE;
  }
  | term TOKEN_GEQ term
  {
    Term* t1 = $1.res.t;
    Term* t2 = $3.res.t;
    CNode* ilp = ILPLeaf::make(t1, t2, ILP_GEQ);
    $$.res.c = ilp;
    $$.kind = PARSE_CNODE;
  }
  | term TOKEN_LT term
  {
    Term* t1 = $1.res.t;
    Term* t2 = $3.res.t;
    CNode* ilp = ILPLeaf::make(t1, t2, ILP_LT);
    $$.res.c = ilp;
    $$.kind = PARSE_CNODE;
  }
  | term TOKEN_LEQ term
  {
    Term* t1 = $1.res.t;
    Term* t2 = $3.res.t;
    CNode* ilp = ILPLeaf::make(t1, t2, ILP_LEQ);
    $$.res.c = ilp;
    $$.kind = PARSE_CNODE;
  }
  | term TOKEN_EQ term
  {
    Term* t1 = $1.res.t;
    Term* t2 = $3.res.t;
    CNode* ilp = ILPLeaf::make(t1, t2, ILP_EQ);
    $$.res.c = ilp;
    $$.kind = PARSE_CNODE;
  }
  | term TOKEN_NEQ term
  {
    Term* t1 = $1.res.t;
    Term* t2 = $3.res.t;
    CNode* ilp = ILPLeaf::make(t1, t2, ILP_EQ);
    CNode* res_c = Connective::make_not(ilp);
    $$.res.c = res_c;
    $$.kind = PARSE_CNODE;
  }
  |
  TOKEN_BOOL_VAR_ID
  {
    string* var_name = $1.res.s;
    BooleanVar* bv = BooleanVar::make(*var_name);
    delete var_name;
    $$.res.c = bv;
    $$.kind = PARSE_CNODE;
  }
  |
  TOKEN_TRUE
  {
     $$.res.c = True::make();
     $$.kind = PARSE_CNODE;
  }
  | TOKEN_FALSE
  {
     $$.res.c = False::make();
     $$.kind = PARSE_CNODE;
  }
  |
  term TOKEN_MOD term TOKEN_EQ term
  {
    Term* t1 = $1.res.t;
    Term* t2 = $3.res.t;
    Term* t3 = $5.res.t;
    if(t2->get_term_type()!=CONSTANT_TERM){
      yyerror("Mod argument must be constant");
      YYERROR;
    }
    ConstantTerm* ct = static_cast<ConstantTerm*>(t2);
    long int constant = ct->get_constant();
    CNode* c = ModLeaf::make(t1, constant, t3);
    $$.res.c = c;
    $$.kind = PARSE_CNODE;
    
  }

  | term TOKEN_MOD term TOKEN_NEQ term
  {
    Term* t1 = $1.res.t;
    Term* t2 = $3.res.t;
    Term* t3 = $5.res.t;
    if(t2->get_term_type()!=CONSTANT_TERM){
      yyerror("Mod argument must be constant");
      YYERROR;
    }
    ConstantTerm* ct = static_cast<ConstantTerm*>(t2);
    long int constant = ct->get_constant();
    CNode* c = ModLeaf::make(t1, constant, t3);
    c = Connective::make_not(c);
    $$.res.c = c;
    $$.kind = PARSE_CNODE;
    
  }

  

  
  
;

term:
      signed_multiply_term {$$ = $1;}
      | term  TOKEN_PLUS multiply_term
	{
	  Term* t1 = ($1).res.t;
	  Term* t2 = ($3).res.t;
	  Term* at = t1->add(t2);
	  $$.res.t = at;
	  $$.kind = PARSE_TERM;
	}
      |  term TOKEN_MINUS multiply_term 
    	{
	  Term* t1 = ($1).res.t;
	  Term* t2 = ($3).res.t;
	  Term* at = t1->subtract(t2);
	  $$.res.t = at;
	  $$.kind = PARSE_TERM;
	}
;

  

signed_multiply_term: 
	  multiply_term {$$ = $1;}
	  | TOKEN_PLUS multiply_term {$$ = $2;}
	  | TOKEN_MINUS multiply_term 
	    {
	      Term* t = $2.res.t;
	      $$.res.t = t->multiply(-1);
	      $$.kind = PARSE_TERM;
	    }
	
;


multiply_term:
      paren_or_atomic_term {$$ = $1;}
      | multiply_term  TOKEN_TIMES paren_or_atomic_term
	{
	  Term* t1 = $1.res.t;
	  Term* t2 = $3.res.t;
	  $$.res.t = t1->multiply(t2);
	  $$.kind = PARSE_TERM;
	}

      | multiply_term  TOKEN_TIMES TOKEN_MINUS paren_or_atomic_term
	{
	  Term* t1 = $1.res.t;
	  Term* t2 = $4.res.t;
	  t2 = t2->multiply(-1);
	  $$.res.t = t1->multiply(t2);
	  $$.kind = PARSE_TERM;  
	}
      |  multiply_term TOKEN_TIMES TOKEN_PLUS  paren_or_atomic_term
	{
	  Term* t1 = $1.res.t;
	  Term* t2 = $4.res.t;
	  $$.res.t = t1->multiply(t2);
	  $$.kind = PARSE_TERM;
	}
    

      |  multiply_term paren_or_atomic_term
	{
	  Term* t1 = $1.res.t;
	  Term* t2 = $2.res.t;
	  $$.res.t = t1->multiply(t2);
	  $$.kind = PARSE_TERM;
	} 

      
;

paren_or_atomic_term: 
    atomic_term 
    {
      $$ = $1;
    }
    |  TOKEN_LPAREN term TOKEN_RPAREN 
      {	
	$$ = $2;
      }
  ;

atomic_term: 
      TOKEN_INT_CONSTANT {$$ = $1; }
      | TOKEN_VAR_IDENTIFIER 
	{
	  string* var_name = $1.res.s;
	  Term* vt = VariableTerm::make(*var_name);
	  delete var_name;
	  $$.res.t = vt;
	  $$.kind = PARSE_TERM;
    
	}
     | TOKEN_FUN_IDENTIFIER TOKEN_RPAREN 
	{
	  string* fun_name = $1.res.s;
	  vector<Term*> args;
	  bool invertible = (*fun_name)[fun_name->length()-1] == '#';
	  if(invertible) {
	    *fun_name = fun_name->substr(0, fun_name->length()-1);
	  }
	  Term* ft = FunctionTerm::make(*fun_name, args, invertible);
	  delete fun_name;
	  $$.res.t = ft;
	  $$.kind = PARSE_TERM;
	}

      | TOKEN_FUN_IDENTIFIER args_list TOKEN_RPAREN  
	{
	  string* fun_name = $1.res.s;
	  bool invertible = (*fun_name)[fun_name->length()-1] == '#';
	    if(invertible) {
	    *fun_name = fun_name->substr(0, fun_name->length()-1);
	  }
	  Term* t = ($2).res.t;
	  assert(t->get_term_type() == FUNCTION_TERM);
	  FunctionTerm* args_ft = static_cast<FunctionTerm*>(t);
	  vector<Term*> args = args_ft->get_args();
	  Term* ft = FunctionTerm::make(*fun_name, args, invertible);
	  delete fun_name;
	  $$.res.t = ft;
	  $$.kind = PARSE_TERM;
	}
  ;


args_list:
      term
      {
	Term* t = $1.res.t;
	
	vector<Term*> args;
	args.push_back(t);
	Term* ft = FunctionTerm::make("dummy", args, false);
	$$.res.t = ft;
	$$.kind = PARSE_TERM;
      }
      | args_list TOKEN_COMMA term
      {
	Term* t = $3.res.t;
	vector<Term*> new_args;


	Term* old_t = $1.res.t;
	assert(old_t->get_term_type() == FUNCTION_TERM);
	FunctionTerm* old_ft = static_cast<FunctionTerm*>(old_t);

	for(vector<Term*>::const_iterator it = old_ft->get_args().begin(); 
	    it!= old_ft->get_args().end(); it++)
	{
	  new_args.push_back(*it);
	}
	new_args.push_back(t);

	Term* ft = FunctionTerm::make("dummy", new_args, false);
	$$.res.t = ft;
	$$.kind = PARSE_TERM;
      }
      ;



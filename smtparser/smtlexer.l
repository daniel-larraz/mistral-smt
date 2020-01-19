%{
#include "smt-parser-defs.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "smtparser.hpp"
#include <iostream>
#include "term.h"
#include "../util.h"


using namespace std;


 
int c = 0;





%}

%x IGNORE
%x NEUTRAL


%option noyywrap
%option prefix="zz"

WHITESPACE [ \t\f\r\v]+
NEWLINE [\n]
PLUS [+]
MINUS [-]
TIMES [*] 
DIVIDE [/] 
DIGIT [0-9]
INT_CONSTANT {DIGIT}+
ALPHA [a-zA-Z_?]
IDENTIFIER {ALPHA}({ALPHA}|{DIGIT})*
LPAREN [(]
RPAREN [)]
AND [aA][nN][dD]
OR [oO][rR]
EQ [=]
GT [>]
GEQ ">="
LT [<]
LEQ "<="
COND "?"
NOT [nN][oO][tT]
LET [lL][eE][tT]
ASSERT [aA][sS][sS][eE][rR][tT]

SET [(]{WHITESPACE}*[sS][eE][tT]
DECLARE [(]{WHITESPACE}*[dD][eE][cC][lL][aA][rR][eE]
CHECK_SAT [(]{WHITESPACE}*[cC][hH][eE][cC][kK][-][sS][aA][tT]{WHITESPACE}*[)]
EXIT [(]{WHITESPACE}*[eE][xX][iI][tT]{WHITESPACE}*[)]
  
 
%x STRING
%x COMMENT

%%



{WHITESPACE} {
  /* Do nothing */
}

{CHECK_SAT} {
  /* Do nothing */
}

{EXIT} {
  /* Do nothing */
}


{SET} {
	BEGIN(IGNORE);
	c = 1;
}

{DECLARE} {
	BEGIN(IGNORE);
	c = 1;
}

<IGNORE>{LPAREN} {
  c++;
}


<IGNORE>{RPAREN} {
  c--;
  if(c == 0) BEGIN(INITIAL);
}

<IGNORE>{NEWLINE} {
  smt_curr_lineno++;
}

<IGNORE>. {
 /* do nothing */
}

{NEWLINE} {
 smt_curr_lineno++;
}

{PLUS} {
 return TOKEN_PLUS;
}

{MINUS} {
 return TOKEN_MINUS;
}


{TIMES} {
 return TOKEN_TIMES;
}

{DIVIDE} {
 return TOKEN_DIVIDE;
}

{INT_CONSTANT} {
	string num(zztext);
	long int lexeme = string_to_int(num);
	Term* t = ConstantTerm::make(lexeme);
	zzlval.res.t = t;
	zzlval.kind = PARSE_TERM;
 	return TOKEN_INT;
}

{LPAREN} {
 return TOKEN_LPAREN;
}

{RPAREN} {
 return TOKEN_RPAREN;
}

{ASSERT} {
 return TOKEN_ASSERT;
}

{AND} {
  return TOKEN_AND;
}

{OR} {
  return TOKEN_OR;
}

{EQ} {
  return TOKEN_EQ;
}

{NOT} {
  return TOKEN_NOT;
}

{GT} {
  return TOKEN_GT;
}

{GEQ} {
  return TOKEN_GEQ;
}

{LT} {
  return TOKEN_LT;
}

{LEQ} { 
  return TOKEN_LEQ;
}
 
{LET} { 
  return TOKEN_LET;
}
 


{IDENTIFIER} {

	string lexeme(zztext);
	Term* t = VariableTerm::make(lexeme);
	zzlval.res.t = t;
	zzlval.kind = PARSE_TERM;
 	 return TOKEN_IDENTIFIER;
}



. {

  return TOKEN_ERROR;
}



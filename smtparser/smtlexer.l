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
IMPLIES "=>"
EQ [=]
GT [>]
GEQ ">="
LT [<]
LEQ "<="
NOT [nN][oO][tT]
LET [lL][eE][tT]
ASSERT [aA][sS][sS][eE][rR][tT]
CHECK_SAT [cC][hH][eE][cC][kK][-][sS][aA][tT]
GET_ABDUCT [gG][eE][tT][-][aA][bB][dD][uU][cC][tT]

SET [(]{WHITESPACE}*[sS][eE][tT]
DECLARE [(]{WHITESPACE}*[dD][eE][cC][lL][aA][rR][eE]
EXIT [(]{WHITESPACE}*[eE][xX][iI][tT]{WHITESPACE}*[)]

TRUE  [tT][rR][uU][eE]
FALSE [fF][aA][lL][sS][eE]

ITE [iI][tT][eE]
 
%x STRING
%x COMMENT

%%



{WHITESPACE} {
  /* Do nothing */
}

{CHECK_SAT} {
  return TOKEN_CHECK_SAT;
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

{GET_ABDUCT} {
 return TOKEN_GET_ABDUCT;
}

{AND} {
  return TOKEN_AND;
}

{OR} {
  return TOKEN_OR;
}

{IMPLIES} {
  return TOKEN_IMPLIES;
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
 
{TRUE} {
  return TOKEN_TRUE;
}

{FALSE} {
  return TOKEN_FALSE;
}

{ITE} {
  return TOKEN_ITE;
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



%{
#include "mistral-parser-defs.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "parser.hpp"
#include <iostream>
#include "term.h"
#include "../util.h"


using namespace std;


 






%}

%x EXPECT_BOOL
%x NEUTRAL

%option noyywrap

WHITESPACE [ \t\f\r\v]+
NEWLINE [\n]
PLUS [+]
MINUS [-]
TIMES [*] 
MOD [%]
DIGIT [0-9]
INT_CONSTANT {DIGIT}+
ALPHA [a-zA-Z]
LEGAL_ID_SYMBOL {ALPHA}|[_$@#'`~:\^\{\}]
IDENTIFIER {LEGAL_ID_SYMBOL}({LEGAL_ID_SYMBOL}|{DIGIT})*
COMMA [,]
LPAREN [(]
RPAREN [)]
AND [&]
OR [\|]
NOT [!]
IMPLIES "->"
GT [>]
GEQ ">="
LT [<]
LEQ "<="
EQ [=]
NEQ "!="
TRUE [tT][rR][uU][eE]
FALSE [fF][aA][lL][sS][eE]
BOOLOP {AND}|{OR}|{IMPLIES}
BOOLOP_LEFT {AND}|{OR}|{IMPLIES}|{NOT}
LEFTBOOL ({WHITESPACE}|{NEWLINE}|{LPAREN})*
RIGHTBOOL ({WHITESPACE}|{NEWLINE}|{RPAREN})*
SPECIAL_EOF [;]
SPECIAL_TERM "\?"
  
 

%%
 /* The simple do nothing and count lines rules 
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

<INITIAL>({LEFTBOOL}{NOT}?{LEFTBOOL}{IDENTIFIER}{RIGHTBOOL})({BOOLOP}|{SPECIAL_EOF}) {
  BEGIN(EXPECT_BOOL);
  yyless(0);
}

<NEUTRAL>({BOOLOP_LEFT}{LEFTBOOL}{IDENTIFIER}{RIGHTBOOL}({BOOLOP}|{SPECIAL_EOF})) {
  BEGIN(EXPECT_BOOL);
  yyless(0);
} 


<INITIAL,NEUTRAL>{WHITESPACE}+ {
    BEGIN(NEUTRAL); /* do nothing, remove whitespaces */
} 
<EXPECT_BOOL>{WHITESPACE}+ {} 


<INITIAL,NEUTRAL>{SPECIAL_TERM} {
  BEGIN(NEUTRAL); 
  return TOKEN_SPECIAL_TERM;
}

<EXPECT_BOOL>{SPECIAL_TERM} {
  return TOKEN_SPECIAL_TERM;
}


<INITIAL,NEUTRAL>{NEWLINE}      {
  BEGIN(NEUTRAL); ++curr_lineno; /* increment line count*/
} 
<EXPECT_BOOL>{NEWLINE}      {
   ++curr_lineno;
}

<INITIAL,NEUTRAL>{PLUS}       { 
  BEGIN(NEUTRAL);
  return TOKEN_PLUS; 
}
<EXPECT_BOOL>{PLUS}       { 
  return TOKEN_PLUS; 
}

<INITIAL,NEUTRAL>{MINUS}       { 
    BEGIN(NEUTRAL);
    return TOKEN_MINUS; 
}
<EXPECT_BOOL>{MINUS}       { 
   return TOKEN_MINUS; 
}


<INITIAL,NEUTRAL>{TIMES}      { 
  BEGIN(NEUTRAL);
  return TOKEN_TIMES; 
}
<EXPECT_BOOL>{TIMES}      { 
  return TOKEN_TIMES; 
}


<INITIAL,NEUTRAL>{MOD}       { 
  BEGIN(NEUTRAL);
  return TOKEN_MOD; 
}
<EXPECT_BOOL>{MOD}       { 
  return TOKEN_MOD; 
}


<INITIAL,NEUTRAL>{COMMA} 	{
  BEGIN(NEUTRAL);
  return TOKEN_COMMA;
}
<EXPECT_BOOL>{COMMA} 	{
  return TOKEN_COMMA;
}


<INITIAL,NEUTRAL>{LPAREN}  	{
  BEGIN(NEUTRAL);
  return TOKEN_LPAREN;
}
<EXPECT_BOOL>{LPAREN}  	{
  return TOKEN_LPAREN;
}


<INITIAL,NEUTRAL>{RPAREN}  	{
  BEGIN(NEUTRAL);
  return TOKEN_RPAREN;
}
<EXPECT_BOOL>{RPAREN}  	{
  return TOKEN_RPAREN;
}
<INITIAL,NEUTRAL>{AND}		{
  BEGIN(NEUTRAL);
  return TOKEN_AND;
}
<EXPECT_BOOL>{AND}		{
  return TOKEN_AND;
}


<INITIAL,NEUTRAL>{OR}		{
  BEGIN(NEUTRAL);
  return TOKEN_OR;
}
<EXPECT_BOOL>{OR}		{
  return TOKEN_OR;
}


<INITIAL,NEUTRAL>{NOT}		{
  BEGIN(NEUTRAL);
  return TOKEN_NOT;
}
<EXPECT_BOOL>{NOT}		{
  return TOKEN_NOT;
}



<INITIAL,NEUTRAL>{IMPLIES}	{
  BEGIN(NEUTRAL);
  return TOKEN_IMPLIES;
}
<EXPECT_BOOL>{IMPLIES}	{
  return TOKEN_IMPLIES;
}


<INITIAL,NEUTRAL>{GT}		{
  BEGIN(NEUTRAL); 
  return TOKEN_GT;
}
<EXPECT_BOOL>{GT}		{
  return TOKEN_GT;
}


<INITIAL,NEUTRAL>{GEQ}		{
  BEGIN(NEUTRAL);
  return TOKEN_GEQ;
}
<EXPECT_BOOL>{GEQ}		{
  return TOKEN_GEQ;
}


<INITIAL,NEUTRAL>{LT}		{
  BEGIN(NEUTRAL);
  return TOKEN_LT;
}
<EXPECT_BOOL>{LT}		{
 return TOKEN_LT;
}


<INITIAL,NEUTRAL>{LEQ}		{
    BEGIN(NEUTRAL);
    return TOKEN_LEQ;
}
<EXPECT_BOOL>{LEQ}		{
    return TOKEN_LEQ;
}


<INITIAL,NEUTRAL>{EQ}	{
    BEGIN(NEUTRAL);
    return TOKEN_EQ;
}
<EXPECT_BOOL>{EQ}	{
    return TOKEN_EQ;
}


<INITIAL,NEUTRAL>{NEQ}		{
    BEGIN(NEUTRAL);
    return TOKEN_NEQ;
}
<EXPECT_BOOL>{NEQ}		{
    return TOKEN_NEQ;
}


<INITIAL,NEUTRAL>{TRUE} 		{
    BEGIN(NEUTRAL);
    return TOKEN_TRUE;
}
<EXPECT_BOOL>{TRUE} 		{
    return TOKEN_TRUE;
}


<INITIAL,NEUTRAL>{FALSE}		{
    BEGIN(NEUTRAL);
    return TOKEN_FALSE;
}
<EXPECT_BOOL>{FALSE}		{
    return TOKEN_FALSE;
}


<INITIAL,NEUTRAL>{INT_CONSTANT} {      
	BEGIN(NEUTRAL);
	string num(yytext);
	long int lexeme = string_to_int(num);
	Term* t = ConstantTerm::make(lexeme);
	yylval.res.t = t;;
	yylval.kind = PARSE_TERM;
	return TOKEN_INT_CONSTANT;
};


<EXPECT_BOOL>{INT_CONSTANT} {
    string num(yytext);
    long int lexeme = string_to_int(num);
    Term* t = ConstantTerm::make(lexeme);
    yylval.res.t = t;;
    yylval.kind = PARSE_TERM;
    return TOKEN_INT_CONSTANT;
};

<INITIAL,NEUTRAL>{IDENTIFIER}({WHITESPACE}|{NEWLINE})*{LPAREN} {
      BEGIN(NEUTRAL);
      string temp(yytext);
      temp = temp.substr(0, temp.length()-1);
      string res;
      for(int i=temp.length()-1; i >=0; i--)
      {
	if(temp[i] == ' ' ||  temp[i] == '\t' || temp[i] == '\f' || temp[i] == '\r'
	|| temp[i] == '\v') continue;
	res = temp.substr(0, i+1);
	break;
      } 

      string* s = new string(res);
      
      yylval.res.s = s;
      yylval.kind = PARSE_STRING;
      return TOKEN_FUN_IDENTIFIER;
};


<EXPECT_BOOL>{IDENTIFIER}({WHITESPACE}|{NEWLINE})*{LPAREN} {
	string temp(yytext);
	temp = temp.substr(0, temp.length()-1);
	string res;
	for(int i=temp.length()-1; i >=0; i--)
	{
	  if(temp[i] == ' ' ||  temp[i] == '\t' || temp[i] == '\f' || temp[i] == '\r'
	  || temp[i] == '\v') continue;
	  res = temp.substr(0, i+1);
	  break;
	}

	string* s = new string(res);
	
	yylval.res.s = s;
	yylval.kind = PARSE_STRING;
	return TOKEN_FUN_IDENTIFIER;
};



<EXPECT_BOOL>{IDENTIFIER} {
  BEGIN(NEUTRAL);
  string* s = new string(yytext);
  yylval.res.s = s; 
  yylval.kind = PARSE_STRING;
  return TOKEN_BOOL_VAR_ID;
}


<INITIAL,NEUTRAL>{IDENTIFIER} {
    string* s = new string(yytext);
    yylval.res.s = s;
    yylval.kind = PARSE_STRING;
    return TOKEN_VAR_IDENTIFIER;
}




<INITIAL,NEUTRAL,EXPECT_BOOL>{SPECIAL_EOF} {}
<INITIAL,NEUTRAL,EXPECT_BOOL><<EOF>>	{BEGIN(INITIAL);return 0;}




%{ 
/* $Id: factorial.l,v 0.1 BETA 2013 $ */
/* (Factorial with functions included as instructions) */
#include <stdlib.h> 
#include <string.h> 
#include "node.h"
#include "y.tab.h"
#include <math.h>

void yyerror(char *s);
int ncom, nlflag, nstr;
long StringToBase(char n[]);
char str[100];

%} 
%x COM
%x STR
%x SCOM

%% 
 /* comment */
"==".*			; 
"=<"			BEGIN COM; ncom++;
<COM>"=>"		if(--ncom == 0){nlflag = 0; BEGIN INITIAL;}
<COM>\"			BEGIN SCOM;
<COM>"=<"		ncom++;
<COM><<EOF>>		{yyerror("ERROR: END OF FILE\n"); BEGIN INITIAL;}
<COM>.|\n		;

<SCOM>\\\"		;
<SCOM>\"		BEGIN COM;
<SCOM>.|\n		;

"="			return EQ;
"<>"			return NE;
"<="			return LE;
">="			return GE;
":="			return ATR;
"++"			{nlflag = 1; return INC;}
"--"			{nlflag = 1; return DEC;}
"void"			{nlflag = 0; return VOID;}
"integer"		{nlflag = 0; return INTEGER;}
"string"		{nlflag = 0; return STRING;}
"public"		{nlflag = 0; return PUBLIC;}
"number"		{nlflag = 0; return NUMBER;}
"const"			{nlflag = 0; return CONST;}
"if"			{nlflag = 0; return IF;}
"then"			{nlflag = 0; return THEN;}
"else"			{nlflag = 0; return ELSE;}
"while"			{nlflag = 0; return WHILE;}
"do"			{nlflag = 0; return DO;}
"for"			{nlflag = 0; return FOR;}
"in"			{nlflag = 0; return IN;}
"step"			{nlflag = 0; return STEP;}
"upto"			{nlflag = 0; return UPTO;}
"downto"		{nlflag = 0; return DOWNTO;}
"break"			{nlflag = 0; return BREAK;}
"continue"		{nlflag = 0; return CONTINUE;}

[A-Za-z][A-Za-z0-9_]*	{nlflag = 1; yylval.s = strdup(yytext); return VARIABLE; } 

[1-9][0-9]*		{ yylval.i = strtol(yytext, 0, 10); if(yylval.i < 0) yyerror("ERROR: INTEGER OVERFLOWS \n"); nlflag = 1; return INT; } 
[0][0-9]*		{ yylval.i = StringToBase(yytext); if(yylval.i < 0) yyerror("ERROR: INTEGER OVERFLOWS \n"); nlflag = 1; return INT; }
"0b"[01]+		{ yylval.i = strtol(yytext+2, 0, 2); if(yylval.i < 0) yyerror("ERROR: INTEGER OVERFLOWS \n"); nlflag = 1; return INT; } 


\"			BEGIN STR; nstr = 0;
<STR>\\\"		str[nstr++] = '\"';
<STR>\\n		str[nstr++] = '\n';
<STR>\\r		str[nstr++] = '\r';
<STR>\\t		str[nstr++] = '\t';
<STR>\"			{nlflag = 1; BEGIN INITIAL; yytext[yyleng-1] = 0; str[nstr] = 0; yylval.s = strdup(str); return STRI; }
<STR>.|\n		str[nstr++] = *yytext;
<STR><<EOF>>		{yyerror("ERROR: END OF FILE\n"); BEGIN INITIAL;}



[0-9]+"."[0-9]+([Ee][+-]?[0-9]+)?		{ nlflag = 1; yylval.n = strtod(yytext, 0); return NUM; } 



[-+*/%<>=\|&~]		return *yytext;
!			{nlflag = 1; return *yytext;}
[#\{\}\[\]\(;,]		{nlflag = 0; return *yytext;}
\)			{nlflag = 1; return *yytext;}
[ \t\r]+		{nlflag = 0;} /* ignore whitespace */ 
\n			if(nlflag){nlflag = 0; return ';';}
.			yyerror("Unknown character"); 
%% 
int yywrap(void) { return 1; } 
char *getyytext() { return yytext; }

long StringToBase(char n[]) {

    int i = 0;
    long octal = 0;
    long decimal=0;
    octal = atoi(n);
    
    while(octal != 0) {
      decimal = decimal + (octal % 10) * pow(8,i++);
      octal = octal/10;
    }
 
    return decimal;
}
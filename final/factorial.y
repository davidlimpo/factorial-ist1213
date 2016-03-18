%{
/* Para testar apenas o lex, deve ter um yacc mínimo para gerar o y.tab.h
   Basta definir os tokens necessários à linguagem a testar (%token).
   Também a rotina main() deve chamar apenas o lex (yylex()).
   Devemos igualmente fornecer uma rotina de impressão de erros yyerror.
   A gramática é vazia (file: ;) pelo que só reconhece a linguagem vazia, não devendo ser chamado o analisador sintáctico do yacc (yyparse()).

Compilar com:
byacc -dv solex.y
flex -dl lang.l
gcc lex.yy.c y.tab.c

Executar os exemplos (apenas com redirecção):
./lang < exemplo.lang

Para garantir que as expressões regulares reconhecem correctamente as sequências de entrada deve adicionar o modo debug (-d) ao flex.
Ao executar os diversos exemplos deve verificar quais as expressões regulares que as reconhecem cada uma das sequências de entrada.
As expressões regulares são identificadas pelo número da linha em que se encontram no ficheiro lex.
*/   
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include "node.h"
#include "tabid.h"

extern void yyerror(char *s);
extern void program(int enter, Node *body), declare_int(char *name, int value, int init, int _con, int _gl, int _ptr, char *name_prt), declare_num(char *name, double value, int init, int _con, int _gl), declare_str(char *name, char *value, int init, int _con, int _gl);
extern void function(char *name, int enter, Node *body, int f_type, int _pub, int f_con);


char* nome_func;
char* nome_func2;
int pos;
int id_func;
int pflag = 0;
static int arg;
int lb = 0;
char *mklbl(int n);
static Node *mkvar(char *name);
int valor_int;
double valor_num;
char* valor_str;
int aux2;
int aux_init;
int _gl;
int _con;
int f_type, f_gl, f_con;
int lbl; /* label counter for generated labels */
int lblbreak;
int aux_else;
Node *b; 
int _ptr;
%}

%union {
	int i;			/* integer value */
	char *s;		/* symbol name or string literal */
	double n;
	Node *a;
};

%token <i> INT
%token <s> STRI VARIABLE
%token <n> NUM
%token VOID PUBLIC CONST
%token IF THEN WHILE DO FOR IN STEP UPTO DOWNTO BREAK CONTINUE INTEGER STRING NUMBER DOLAR PAR

%type <i> tipo ast incdec
%type <a> args expr init lvalue instr instruc corpo corpoop paramco param declr elseop params paramop

%nonassoc ELSEX
%nonassoc ELSE
%right ATR
%left '|'
%left '&'
%nonassoc '~'
%left EQ NE
%left LE GE '<' '>'
%left '+' '-'
%left '*' '/' '%'
%nonassoc INC DEC '!' UMINUS
%nonassoc '('')''['']'

%token LABEL JMP JZ JNZ ETIQ CALL LOCAL END EXPR BLOCO STMT INDEX BV

%%
file	: decl
     	;
     	
decl	: /* empty */
	| decl declr
	;
	
declr	: decpub deccons tipo ast VARIABLE { nome_func = $5; id_func = $3 + $4 + 8; } init ';' {
												  if (aux2 < 8) 
												  { IDnew($3+$4, $5 ,0);
												    switch($3){
												      case 0:
													declare_int($5, valor_int, aux_init, _con, _gl, _ptr, nome_func2); break;
												      case 1:
													declare_num($5, valor_num, aux_init, _con, _gl); break;
												      case 2:
													declare_str($5, valor_str, aux_init, _con, _gl); break;
												    }
												  }
												  else { IDpop(); 
												    function($5, -pos, $7, id_func, _gl, f_con);
												  }
												}
	;

decpub	: /*empty*/							{_gl = 0;}
	| PUBLIC							{_gl = 1;}
	;
	
deccons	: /*empty*/							{_con = 0;}
	| CONST								{_con = 1;}
	;
	
tipo	: INTEGER							{ $$ = 0; }
	| NUMBER							{ $$ = 1; }
	| STRING							{ $$ = 2; }
	| VOID								{ $$ = 3; }
	;

ast	: /*empty*/							{ $$ = 0; _ptr = 0;}
	| '*'								{ $$ = 4; _ptr = 1;}
	;
	
init	: /* empty */							{ $$ = nilNode(END); aux2 = 0; aux_init = 0;}
	| ATR INT							{ $$ = intNode(INT, $2); valor_int = $2; aux2 = 0;  aux_init = 1;}
	| ATR NUM							{ $$ = realNode(NUM, $2);  valor_num = $2; aux2 = 0;  aux_init = 1;}
	| ATR constan STRI						{ $$ = strNode(STRI, $3);  valor_str = $3; aux2 = 0;  aux_init = 1;}
	| ATR VARIABLE							{ $$ = uniNode(ATR, mkvar($2)); nome_func2 = $2; }
	| '(' { IDnew(id_func, nome_func, 0); IDpush(); if(id_func != 11){ IDnew(id_func-8, nome_func, pos = -4);} else pos = 8;  }  params ')' corpoop			{ $$ = $5; aux2 = 8; } //se for funçao é -8
	;

constan	: /*empty*/
	| CONST
	;

params	: /*empty*/							{$$ = 0; pflag = 0; }
	| param paramop							{$$ = 0; pflag = 1; }
	;

param	: tipo ast VARIABLE										{ if (pos <= 0) pos -= 4; IDnew($1+$2, $3, pos); if (pos >= 8) pos += 4; $$ = mkvar($3);}
	;

paramop	: /*empty*/											{$$ = nilNode(END);}
	| ',' param paramop										{$$ = binNode(PAR, $2, $3);}
	;
	
corpo	: '{' paramco instr '}'										{ $$ = binNode(BLOCO, $2, $3); }
	;

corpoop	: /*empty*/											{ $$ = nilNode(END); pos = -4; }
	| { pos = -4; } corpo										{ $$ = $2; }
	;
	
paramco	: /*empty*/											{ $$ = nilNode(END); }
	| paramco param ';'										{ $$ = binNode(PAR, $1, $2); }
	;
	
instr	: /*empty*/											{ $$ = nilNode(END); }
	| instr instruc											{ $$ = binNode(STMT, $1, $2); }
	;
	
instruc	: IF expr THEN instruc elseop									{if(!aux_else){

													    int lbl1 = ++lbl;
													    $$ = seqNode(';', 3,
													    binNode(JZ,$2, strNode(ETIQ, mklbl(lbl1))),
													    $4, /* instr */
													    strNode(LABEL, mklbl(lbl1)));
													  }else{
													  
													    int lbl1 = ++lbl, lbl2 = ++lbl;
													    $$ = seqNode(';', 6,
													    binNode(JZ,$2, strNode(ETIQ, mklbl(lbl1))),
													    $4, /* instr */
													    strNode(JMP, mklbl(lbl2)),
													    strNode(LABEL, mklbl(lbl1)),
													    $5, /* else */
													    strNode(LABEL, mklbl(lbl2)));
													  }
													}
	
				
	| DO instruc WHILE expr ';'									{ int lbl1 = ++lbl, lbl2 = ++lbl;
													    $$ = seqNode(';', 6,
													    strNode(JMP, mklbl(lbl1)),
													    strNode(LABEL, mklbl(lbl2)),
													    $2, /* instr */
													    strNode(LABEL, mklbl(lbl1)),
													    binNode(JNZ,$4, strNode(ETIQ, mklbl(lbl2))),
													    strNode(LABEL, mklbl(lblbreak))
													    );}
															
	| FOR lvalue IN expr updo expr stexpr DO instruc 						{ $$ = 0; }
	| expr ';' 											{ $$ = uniNode(EXPR, $1); }
	| corpo												{ $$ = $1; }
	| BREAK inteiro ';'										{ lblbreak = ++lbl; $$ = strNode(JMP, mklbl(lblbreak)); }
	| CONTINUE inteiro ';'										{ $$ = 0; }
	| lvalue '#' expr ';'										{ $$ = 0; }
	;
	
updo	: UPTO
	| DOWNTO
	;
	
stexpr	:
	| STEP expr
	;
	
elseop	: %prec ELSEX											{$$ = 0; aux_else = 0;}
	| ELSE instruc											{$$ = $2; aux_else = 1;}
	;
		
inteiro	:
	| INT
	; 

lvalue	: VARIABLE											{ $$ = mkvar($1); }
	| lvalue '[' expr ']'										{ $$ = binNode(INDEX, $1, $3);/* $$ = $1-4; lb++;*/ }			// FALTA!!!!!!!!!!!!!!!!!!!!!!!!
	;
	
expr	: INT							{ $$ = intNode(INT, $1); }
	| NUM							{ $$ = realNode(NUM, $1); }
	| STRI							{ $$ = strNode(STRI, $1); }
	| lvalue						{ $$ = $1; }
	| lvalue ATR expr					{ $$ = binNode(ATR, $1, $3);}
	| '*' expr %prec UMINUS					{ $$ = uniNode(UMINUS, $2); }
	| '&' expr %prec UMINUS					{ $$ = uniNode(UMINUS, $2); }
	| '!' expr %prec UMINUS					{ $$ = uniNode(UMINUS, $2);}
	| '-' expr %prec UMINUS					{ $$ = uniNode(UMINUS, $2); }
	| incdec lvalue						{ $$ = binNode($1, nilNode(END), $2); }
	| lvalue incdec						{ $$ = binNode($2, $1, nilNode(END));}
	| expr '+' expr						{ $$ = binNode('+', $1, $3);}
	| expr '-' expr						{ $$ = binNode('-', $1, $3); }
	| expr '*' expr						{ $$ = binNode('*', $1, $3);}
	| expr '/' expr						{ $$ = binNode('/', $1, $3);}
	| expr '%' expr						{ $$ = binNode('%', $1, $3);}
	| expr '<' expr						{ $$ = binNode('<', $1, $3); }
	| expr '>' expr						{ $$ = binNode('>', $1, $3); }
	| expr GE expr						{ $$ = binNode(GE, $1, $3); }
	| expr LE expr						{ $$ = binNode(LE, $1, $3); }
	| expr NE expr						{ $$ = binNode(NE, $1, $3); }
	| expr EQ expr						{ $$ = binNode(EQ, $1, $3); }
	| '~' expr						{ $$ = uniNode('~', $2); }
	| expr '&' expr						{ $$ = binNode('&', $1, $3); }
	| expr '|' expr						{ $$ = binNode('|', $1, $3); }
	| '(' expr ')'						{ $$ = $2; }
	| VARIABLE '(' ')'					{ $$ = binNode(CALL, strNode(VARIABLE, $1), nilNode(END)); }
	| VARIABLE '(' args ')'					{ $$ = binNode(CALL, strNode(VARIABLE, $1), $3); } 
	;

args	: expr							{ $$ = $1; arg = 1;}
	| args ',' expr						{ $$ = binNode(',', $3, $1); arg++; }
	;
	
incdec	: INC							{ $$ = INC; }
	| DEC							{ $$ = DEC; }
	;
	
%%

static Node *mkvar(char *name) {
  long loc;
  int typ = IDfind(name, &loc); /* find type and offset of the variable */
  if (typ < 8 && loc != 0) /* global variables have offset==0 */
    return intNode(LOCAL, loc); /* local variables are accessed by offset */
  return strNode(VARIABLE, name); /* global variables are accessed by name */
}

char *mklbl(int n) {
  static char buf[20];
  sprintf(buf, "_i%d", n);
  return strdup(buf);
}

char **yynames =
#if YYDEBUG > 0
		 (char**)yyname;
#else
		 0;
#endif

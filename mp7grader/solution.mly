/* Use the expression datatype defined in expressions.ml: */
%{
    open Mp7common
    let andsugar l r = IfExp(l,r,ConExp (Bool false))
    let orsugar l r = IfExp(l,ConExp (Bool true),r)
    let gtsugar l r = BinExp(Less,r,l)
    let geqsugar l r = orsugar (gtsugar l r) (BinExp(Eq, l, r))
(*IfExp(BinExp(Less,r,l)
                            ,ConExp(Bool true)
                            ,BinExp(Eq,l,r))
*)
    let leqsugar l r = orsugar (BinExp(Less,l,r)) (BinExp(Eq, l, r))
(* IfExp(BinExp(Less,l,r)
                            ,ConExp(Bool true)
                            ,BinExp(Eq,l,r))
*)
%}

/* Define the tokens of the language: */
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <string> STRING IDENT
%token <(int*int)> OPCOM CLCOM SCLCOM
%token DBLSEMI PLUS MINUS TIMES DIV DPLUS DMINUS DTIMES DDIV CARAT EXP LT GEQ LEQ GT
       EQUALS AND OR PIPE ARROW DCOLON LET REC SEMI IN IF THEN ELSE FUN
       LBRAC RBRAC LPAREN RPAREN COMMA
       UNIT ERROR EOF
       TRY WITH UNDERSCORE RAISE 
       HEAD TAIL PRINT NEG FST SND

/* Define the "goal" nonterminal of the grammar: */
%start main
%type <Mp7common.toplvl> main

%%

main:
    expression DBLSEMI      			{ (Anon $1) }
  | LET IDENT EQUALS expression	DBLSEMI 	{ TopLet ($2,$4) }
  | LET REC IDENT IDENT EQUALS expression DBLSEMI  	{ (TopRec ($3, $4, $6)) }

expression:
   op_exp				{ $1 }

op_exp:
  | pure_or_exp OR and_exp		{ orsugar $1 $3 }
  | and_exp				{ $1 }

and_exp:
  | pure_and_exp AND rel_exp		{ andsugar $1 $3 }
  | rel_exp				{ $1 }

rel_exp:
  | pure_rel_exp LT cons_exp		{ BinExp (Less,$1,$3) }
  | pure_rel_exp EQUALS cons_exp	{ BinExp (Eq,$1,$3) }
  | pure_rel_exp GT cons_exp		{ gtsugar $1 $3 }
  | pure_rel_exp LEQ cons_exp		{ leqsugar $1 $3 }
  | pure_rel_exp GEQ cons_exp		{ geqsugar $1 $3 }
  | cons_exp	     			{ $1 }

cons_exp:
  | pure_add_exp DCOLON cons_exp	{ BinExp(Cons,$1,$3) }
  | add_exp				{ $1 }

add_exp:
  | pure_add_exp PLUS mult_exp		{ BinExp(Add,$1,$3) }
  | pure_add_exp MINUS mult_exp		{ BinExp(Sub,$1,$3) }
  | pure_add_exp DPLUS mult_exp		{ BinExp(FAdd,$1,$3) }
  | pure_add_exp DMINUS mult_exp	{ BinExp(FSub,$1,$3) }
  | pure_add_exp CARAT mult_exp	        { BinExp(Concat,$1,$3) }
  | mult_exp				{ $1 }

mult_exp:
  | pure_mult_exp TIMES expo_exp 	{ BinExp(Mul,$1,$3) }
  | pure_mult_exp DIV expo_exp 		{ BinExp(Div,$1,$3) }
  | pure_mult_exp DTIMES expo_exp 	{ BinExp(FMul,$1,$3) }
  | pure_mult_exp DDIV expo_exp 	{ BinExp(FDiv,$1,$3) }
  | expo_exp	       			{ $1 }

expo_exp:
  | pure_app_raise_exp EXP expo_exp        { BinExp (Exp,$1,$3) }
  | nonop_exp                           { $1 }

nonop_exp:
    if_let_fun_try_exp		{ $1 }
  | app_raise_exp		{ $1 }

app_raise_exp:
    app_exp	{ $1 }
  | pure_app_exp RAISE app_raise_exp { AppExp($1,RaiseExp($3)) }
  | pure_app_exp RAISE if_let_fun_try_exp { AppExp($1,RaiseExp($3)) }
  | RAISE app_raise_exp		{ RaiseExp $2 }
  | RAISE if_let_fun_try_exp		{ RaiseExp $2 }

app_exp:
  | atomic_expression		{ $1 }
  | pure_app_exp nonapp_exp 	{ AppExp($1,$2) }
  | HEAD nonapp_exp		{ MonExp (Head,$2) }
  | TAIL nonapp_exp		{ MonExp (Tail,$2) }
  | PRINT nonapp_exp		{ MonExp (Print,$2) }
  | NEG nonapp_exp		{ MonExp (Neg,$2) }
  | FST nonapp_exp		{ MonExp (Fst,$2) }
  | SND nonapp_exp		{ MonExp (Snd,$2) }

nonapp_exp:
    atomic_expression		{ $1 }
  | if_let_fun_try_exp		{ $1 }


if_let_fun_try_exp:
    TRY expression WITH exp_matches	{ match $4 with (m,ms) -> TryWithExp ($2, m, ms) }
  | LET REC IDENT IDENT EQUALS expression IN expression	{ RecExp($3, $4, $6, $8) }
  | LET IDENT EQUALS expression IN expression		{ LetExp($2, $4, $6) }
  | FUN IDENT ARROW expression				{ FunExp($2, $4) }
  | IF expression THEN expression ELSE expression	{ IfExp($2, $4, $6) }

exp_matches:
    exp_match					{ ($1, []) }
  | no_try_exp_match PIPE exp_matches		{ (match $3 with (em, ems) -> ($1, em::ems)) }

exp_match:
    pat ARROW expression { ($1, $3) }

no_try_exp_match:
    pat ARROW no_try_expression		{ ($1, $3) }


no_try_expression:
    no_try_op_exp			{ $1 }

no_try_op_exp:
  | pure_or_exp OR no_try_and_exp	{ orsugar $1 $3 }
  | no_try_and_exp	   		{ $1 }

no_try_and_exp:
    pure_and_exp AND no_try_eq_exp	{ andsugar $1 $3 }
  | no_try_eq_exp	     		{ $1 }

no_try_eq_exp:
  no_try_rel_exp     			{ $1 }

no_try_rel_exp:
  | pure_rel_exp LT no_try_cons_exp	{ BinExp (Less,$1,$3) }
  | pure_rel_exp EQUALS no_try_cons_exp	{ BinExp (Eq,$1,$3) }
  | pure_rel_exp GT no_try_cons_exp	{ gtsugar $1 $3 }
  | pure_rel_exp GEQ no_try_cons_exp	{ geqsugar $1 $3 }
  | pure_rel_exp LEQ no_try_cons_exp	{ leqsugar $1 $3 }
  | no_try_cons_exp    			{ $1 }

no_try_cons_exp:
  | pure_add_exp DCOLON no_try_cons_exp { BinExp(Cons,$1,$3) }
  | no_try_add_exp			{ $1 }

no_try_add_exp:
  | pure_add_exp PLUS no_try_mult_exp	{ BinExp(Add,$1,$3) }
  | pure_add_exp MINUS no_try_mult_exp	{ BinExp(Sub,$1,$3) }
  | pure_add_exp DPLUS no_try_mult_exp	{ BinExp(FAdd,$1,$3) }
  | pure_add_exp DMINUS no_try_mult_exp	{ BinExp(FSub,$1,$3) }
  | pure_add_exp CARAT no_try_mult_exp  { BinExp(Concat,$1,$3) }
  | no_try_mult_exp			{ $1 }

no_try_mult_exp:
  | pure_mult_exp TIMES no_try_expo_exp { BinExp(Mul,$1,$3) }
  | pure_mult_exp DIV no_try_expo_exp 	{ BinExp(Div,$1,$3) }
  | pure_mult_exp DTIMES no_try_expo_exp{ BinExp(FMul,$1,$3) }
  | pure_mult_exp DDIV no_try_expo_exp 	{ BinExp(FDiv,$1,$3) }
  | no_try_expo_exp			{ $1 }

no_try_expo_exp: 
  | pure_app_raise_exp EXP no_try_expo_exp { BinExp(Exp,$1,$3) }
  | no_try_nonop_exp                    { $1 }

no_try_nonop_exp:
    no_try_if_let_fun_exp		{ $1 }
  | no_try_app_raise_expression		{ $1 }

no_try_app_raise_expression:
    no_try_app_expression		{ $1 }
  | pure_app_exp RAISE no_try_app_raise_expression { AppExp($1,RaiseExp($3)) }
  | RAISE no_try_app_raise_expression  { RaiseExp($2) }

no_try_app_expression:
    atomic_expression				{ $1 } 
  | pure_app_exp no_try_nonapp_expression 	{ AppExp($1,$2) }
  | HEAD no_try_nonapp_expression		{ MonExp (Head,$2) }
  | TAIL no_try_nonapp_expression		{ MonExp (Tail,$2) }
  | PRINT no_try_nonapp_expression		{ MonExp (Print,$2) }
  | NEG no_try_nonapp_expression		{ MonExp (Neg,$2) }

no_try_nonapp_expression:
    atomic_expression			{ $1 }
  | no_try_if_let_fun_exp		{ $1 }

no_try_if_let_fun_exp:
    IF expression THEN expression ELSE no_try_expression	{ IfExp($2,$4,$6) }
  | LET IDENT EQUALS expression IN no_try_expression		{ LetExp($2,$4,$6) }
  | LET REC IDENT IDENT EQUALS expression IN no_try_expression	{ RecExp($3,$4,$6,$8) }



pat:
  | UNDERSCORE	{ None }
  | INT		{ Some $1 }

pure_or_exp:
  | pure_or_exp OR pure_and_exp		{ orsugar $1 $3 }
  | pure_and_exp   			{ $1 }

pure_and_exp:
  | pure_and_exp AND pure_eq_exp	{ andsugar $1 $3 }
  | pure_eq_exp	     			{ $1 }

pure_eq_exp:
  pure_rel_exp	     		{ $1 }

pure_rel_exp:
  | pure_rel_exp LT pure_cons_exp	{ BinExp (Less,$1,$3) }
  | pure_rel_exp EQUALS pure_cons_exp	{ BinExp (Eq,$1,$3) }
  | pure_rel_exp GT pure_cons_exp	{ gtsugar $1 $3 }
  | pure_rel_exp GEQ pure_cons_exp	{ geqsugar $1 $3 }
  | pure_rel_exp LEQ pure_cons_exp	{ leqsugar $1 $3 }
  | pure_cons_exp	     		{ $1 }

pure_cons_exp:
  | pure_add_exp DCOLON pure_cons_exp   { BinExp(Cons,$1,$3) }
  | pure_add_exp			{ $1 }

pure_add_exp:
  | pure_add_exp PLUS pure_mult_exp	{ BinExp(Add,$1,$3) }
  | pure_add_exp MINUS pure_mult_exp	{ BinExp(Sub,$1,$3) }
  | pure_add_exp DPLUS pure_mult_exp	{ BinExp(FAdd,$1,$3) }
  | pure_add_exp DMINUS pure_mult_exp	{ BinExp(FSub,$1,$3) }
  | pure_add_exp CARAT pure_mult_exp    { BinExp(Concat,$1,$3) }
  | pure_mult_exp			{ $1 }

pure_mult_exp:
  | pure_mult_exp TIMES pure_expo_exp 	{ BinExp(Mul,$1,$3) }
  | pure_mult_exp DIV pure_expo_exp 	{ BinExp(Div,$1,$3) }
  | pure_mult_exp DTIMES pure_expo_exp 	{ BinExp(FMul,$1,$3) }
  | pure_mult_exp DDIV pure_expo_exp 	{ BinExp(FDiv,$1,$3) }
  | pure_expo_exp	       		{ $1 }

pure_expo_exp:
  | pure_app_raise_exp EXP pure_expo_exp  { BinExp(Exp,$1,$3) }
  | pure_app_raise_exp           { $1 }

pure_app_raise_exp:
    pure_app_exp		{ $1 }
  | pure_app_exp RAISE pure_app_raise_exp { AppExp($1,RaiseExp($3)) }
  | RAISE pure_app_raise_exp  { RaiseExp($2) }

pure_app_exp:
    atomic_expression			{ $1 }
  | pure_app_exp atomic_expression 	{ AppExp($1,$2) }
  | HEAD atomic_expression		{ MonExp (Head,$2) }
  | TAIL atomic_expression		{ MonExp (Tail,$2) }
  | PRINT atomic_expression		{ MonExp (Print,$2) }
  | NEG atomic_expression		{ MonExp (Neg,$2) }


atomic_expression:
    constant_expression         { ConExp $1 }
  | IDENT			{ VarExp $1 }
  | list_expression		{ $1 }
  | paren_expression            { $1 }

list_expression:
    LBRAC list_contents			{ $2 }
 
list_exp_end:
    RBRAC				{ ConExp Nil }
  | SEMI list_tail				{ $2 }

list_tail:
    RBRAC				{ ConExp Nil }
  | list_contents			{ $1 }

list_contents:
    expression list_exp_end	{ BinExp(Cons,$1,$2) }

paren_expression:
    LPAREN par_exp_end			{ $2 }

par_exp_end:
    expression RPAREN			{ $1 }
  | expression COMMA expression RPAREN	{ BinExp (Comma,$1,$3) }

constant_expression:
    INT                         { Int $1 }
  | BOOL			{ Bool $1 }
  | FLOAT			{ Float $1 }
  | LBRAC RBRAC			{ Nil }
  | STRING			{ String $1 }
  | UNIT			{ Unit }



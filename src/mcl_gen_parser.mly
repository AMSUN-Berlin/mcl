(*
 * Copyright (c) 2014, TU Berlin
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *   * Neither the name of the TU Berlin nor the
 *     names of its contributors may be used to endorse or promote products
 *     derived from this software without specific prior written permission.

 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL TU Berlin BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

%token LAMBDA HASH GT LT NEQ GEQ LEQ EQ LPAREN RPAREN LBRACKET RBRACKET LDBRACKET RDBRACKET LBRACE RBRACE LEFTARROW DLEFTARROW BULLET LANGLE RANGLE SEMICOLON COMMA DOT

%token <int> INT
%token <float> FLOAT
%token <string> IDENT
%token <string> HOST
%token PLUS MINUS TIMES DIV PLUSDOT MINUSDOT TIMESDOT DIVDOT 
%token EOF

%token IF THEN ELSE NEW LET REC IN PUT GET RETURN MODEL STATE REPLACE REPLACEABLE EXTEND WITH TRUE FALSE

%right lowest
%nonassoc IDENT INT FLOAT HOST LAMBDA LPAREN RPAREN RBRACKET LDBRACKET RDBRACKET LBRACE RBRACE LEFTARROW BULLET LANGLE RANGLE 
%left COMMA
%left SEMICOLON         /* lowest precedence */
%left GT LT NEQ GEQ LEQ EQ 
%left PLUS MINUS PLUSDOT MINUSDOT     /* medium precedence */
%left TIMES DIV TIMESDOT DIVDOT        
%nonassoc UMINUS        /* highest precedence */
%nonassoc below_app
%left app_prec     
%left DOT LBRACKET   


%{
  open Mcl
  open Parsetree
  open Mcl_parser_utils
         
  let lift_ident x =
    let loc = {
      Location.loc_start = {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0}; 
      loc_end = {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 1} ; 
      loc_ghost = false} in    
    
    { pexp_desc = Pexp_ident {Asttypes.txt = Longident.Lident x ; loc ; } ; 		
      pexp_loc = loc;
      pexp_attributes = [] }

  let bin_op op e1 e2 = 
    App(App((Host(lift_ident op)), e1), e2)

  let rec make_lam b = function
    | [] -> b
    | x::args -> Abs(x, make_lam b args)
%}

%start <Mcl.model_expr> main
%start <Mcl.expr> sole_expr

%%
main: m = model EOF { m }

sole_expr: e = expr EOF { e } 

model :
| LBRACE fds = separated_list(SEMICOLON, field) RBRACE 
			     { Model(fds) }
| MODEL x = IDENT EQ m = model IN m2 = model { MLet(x, m, m2) }
| STATE x = IDENT EQ e = expr IN m = model { MState(x, e, m) }
| REPLACE x = IDENT WITH e = expr IN m = model { MModify(x, e, m) }
| x = IDENT { MVar(x) }


field:
| e = expr { Unnamed e }
| EXTEND m = model { Extend m }
| x = IDENT DLEFTARROW e = expr { Named(x, e) }
| REPLACEABLE x = IDENT DLEFTARROW e = expr { Replaceable(x, e) }

expr_comma_list:
    es=expr_comma_list COMMA e=expr    { e :: es }
  | e1=expr COMMA e2=expr  { [e2;e1] }

expr:
  | TRUE { Const(Bool(true)) }
  | FALSE { Const(Bool(false)) }
  | i = INT 
            { Const (Int (i)) }
| f = FLOAT
    { Const (Float (f)) }
| x = IDENT 
    { Var(x) }
| LPAREN e = expr RPAREN
    { e }
| e1 = expr e2 = expr { App(e1, e2) } %prec app_prec

| es = expr_comma_list { Tup(List.rev es) }

| e = expr DOT n=INT { Project(n, e) } 
| e = expr DOT x=IDENT { Method(x, e) }
                       
| e1 = expr PLUS e2 = expr
    { bin_op "+" e1 e2 }
| e1 = expr MINUS e2 = expr
    { bin_op "-" e1 e2 }
| e1 = expr TIMES e2 = expr
    { bin_op "*" e1 e2 }
| e1 = expr DIV e2 = expr
    { bin_op "/" e1 e2 }

| e1 = expr PLUSDOT e2 = expr
    { bin_op "+." e1 e2 }
| e1 = expr MINUSDOT e2 = expr
    { bin_op "-." e1 e2 }
| e1 = expr TIMESDOT e2 = expr
    { bin_op "*." e1 e2 }
| e1 = expr DIVDOT e2 = expr
    { bin_op "/." e1 e2 }


| e1 = expr GT e2 = expr
    { bin_op ">" e1 e2 }
| e1 = expr LT e2 = expr
    { bin_op "<" e1 e2 }
| e1 = expr GEQ e2 = expr
    { bin_op ">=" e1 e2 }
| e1 = expr LEQ e2 = expr
    { bin_op "<=" e1 e2 }
| e1 = expr NEQ e2 = expr
    { bin_op "<>" e1 e2 }


| MINUS e = expr %prec UMINUS
    { App((Host(lift_ident "~-")), e) }
| HASH e = expr %prec HASH
    { Length(e) }
 | NEW me = model
    { New(me) }
| RETURN e = expr 
    { Return e }

| LET x = IDENT args = list (IDENT) EQ e1 = expr IN e2 = expr
    { Let(x, make_lam e1 args, e2) }
| LET REC x = IDENT args = list (IDENT) EQ e1 = expr IN e2 = expr
    { Letrec(x, make_lam e1 args, e2) }
| LAMBDA x = IDENT DOT e = expr 
    { Abs(x, e) }
| IF c = expr THEN t = expr ELSE e = expr 
    { Cond(c,t,e) }
| LDBRACKET e = expr WITH i = expr EQ u = expr RDBRACKET
    { Update(e, i, u) }
| LDBRACKET es = separated_list(SEMICOLON, expr) RDBRACKET
    { Vec(Array.of_list es) }

| e = expr LBRACKET idx = expr RBRACKET 
    { Idx(e, idx) }

| x=IDENT BULLET GET 
    { Get(x) }
| x=IDENT BULLET PUT e = expr 
    { Put(x, e) }
| x=IDENT LEFTARROW e = expr SEMICOLON e2 = expr
    { Bind(x, e, e2) } %prec lowest
| RETURN e = expr 
    { Return(e) }

| h = HOST { try Host ( Parse.expression (Lexing.from_string h)) with
               Syntaxerr.Error e -> raise (HostSyntaxError ($startpos, e))
           }


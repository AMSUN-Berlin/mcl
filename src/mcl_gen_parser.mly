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

(* let delimiter_strings = ["λ" ; "="; "⟪"; "⟫"; "."; ";"; "("; ")"; "["; "]" ; "←"; "•"; "⟦"; "⟧"; "⟨"; "⟩"] *)
%token LAMBDA GT LT NEQ GEQ LEQ EQ LPAREN RPAREN LBRACKET RBRACKET LDBRACKET RDBRACKET LEFTARROW BULLET LANGLE RANGLE SEMICOLON COMMA DOT

%token <int> INT
%token <float> FLOAT
%token <string> IDENT
%token <string> HOST
%token PLUS MINUS TIMES DIV
%token EOF

%token IF THEN ELSE (*NEW*) LET REC IN PUT GET RETURN

%nonassoc IDENT INT FLOAT HOST LAMBDA LPAREN RPAREN LBRACKET RBRACKET LDBRACKET RDBRACKET LEFTARROW BULLET LANGLE RANGLE SEMICOLON COMMA DOT
%left GT LT NEQ GEQ LEQ EQ 
%left PLUS MINUS        /* lowest precedence */
%left TIMES DIV         /* medium precedence */
%nonassoc UMINUS        /* highest precedence */
%left app_prec          


%{
  open Mcl
  open Parsetree

  let lift_ident x =
    let loc = {
      Location.loc_start = {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0}; 
      loc_end = {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 1} ; 
      loc_ghost = false} in    
    
    { pexp_desc = Pexp_ident {Asttypes.txt = Longident.Lident x ; loc ; } ; 		
      pexp_loc = loc;
      pexp_attributes = [] }
%}

%start <Mcl.expr> main

%%
main: e = expr EOF { e }

expr:
| i = INT
    { Const (Int (i)) }
| f = FLOAT
    { Const (Float (f)) }
| x = IDENT 
    { Var(x) }
| LPAREN e = expr RPAREN
    { e }
| e1 = expr e2 = expr { App(e1, e2) } %prec app_prec
| e1 = expr PLUS e2 = expr
    { App(App((Host(lift_ident "+")), e1), e2) }
| e1 = expr MINUS e2 = expr
    { App(App((Host(lift_ident "-")), e1), e2) }
| e1 = expr TIMES e2 = expr
    { App(App((Host(lift_ident "*")), e1), e2) }
| e1 = expr DIV e2 = expr
    { App(App((Host(lift_ident "/")), e1), e2) }

| e1 = expr GT e2 = expr
    { App(App((Host(lift_ident ">")), e1), e2) }
| e1 = expr LT e2 = expr
    { App(App((Host(lift_ident "<")), e1), e2) }
| e1 = expr GEQ e2 = expr
    { App(App((Host(lift_ident ">=")), e1), e2) }
| e1 = expr LEQ e2 = expr
    { App(App((Host(lift_ident "<=")), e1), e2) }
| e1 = expr NEQ e2 = expr
    { App(App((Host(lift_ident "<>")), e1), e2) }



| MINUS e = expr %prec UMINUS
    { App((Host(lift_ident "~-")), e) }

| LET x = IDENT EQ e1 = expr IN e2 = expr 
    { Let(x,e1,e2) }
| LET REC x = IDENT EQ e1 = expr IN e2 = expr
    { Letrec(x, e1, e2) }
| LAMBDA x = IDENT DOT e = expr 
    { Abs(x, e) }
| IF c = expr THEN t = expr ELSE e = expr 
    { Cond(c,t,e) }
| LDBRACKET es = separated_list(SEMICOLON, expr) RDBRACKET
    { Vec(Array.of_list es) }
| e = expr LBRACKET idx = expr RBRACKET 
    { Idx(e, idx) }
| x = IDENT LANGLE es = separated_list(COMMA, expr) RANGLE
    { Adt(x, es) }
| x=IDENT BULLET GET 
    { Get(x) }
| x=IDENT BULLET PUT e = expr 
    { Put(x, e) }
| x=IDENT LEFTARROW e = expr SEMICOLON e2 = expr
    { Bind(x, e, e2) }
| RETURN e = expr 
    { Return(e) }
| h = HOST { Host ( Parse.expression (Lexing.from_string h)) }


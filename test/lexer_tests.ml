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
 *
 *)

open OUnit
open Mcl_gen_parser
open Mcl_lexer

let tok_comp t = function
  | HOST x -> ( match t with HOST y -> x = y | _ -> false )
  | IDENT x -> ( match t with IDENT y -> x=y | _ -> false ) 
  | FLOAT x -> ( match t with FLOAT y when x = y -> true | _ -> false )
  | INT x -> ( match t with INT y when x = y -> true | _ -> false ) 
  | t' -> t = t'

let teardown _ = ()

let rec tokenize ls = function
    t :: r -> begin
      match (next_token ls).token with 
	EOF -> assert_equal ~msg:"EOF" [] r
      | t' -> assert_equal ~cmp:tok_comp ~msg:"equality" ~printer:name_of_token  t t' ;
			   tokenize ls r
    end
  | [] -> assert_equal ~msg:"EOF" ~printer:name_of_token EOF (next_token ls).token
  
let test_lexing (ls, toks) = tokenize ls toks

let samples = [ 
  ("λ", [LAMBDA]);  
  (">< >=<=  <>", [GT;LT;GEQ;LEQ;NEQ]);
  ("⟦⟧[]", [LDBRACKET;RDBRACKET;LBRACKET;RBRACKET]);
  ("+-*/", [PLUS;MINUS;TIMES;DIV]);
  (" 1.234", [FLOAT(1.234)]);
  (" 1234", [INT(1234)]);
  ("x", [IDENT("x")]) ;
  ("new_foo", [IDENT("new_foo")]);
  ("x2", [IDENT("x2")]);
  ("x y", [IDENT "x"; IDENT "y"]) ;
  ("x 2 x 3. x", [IDENT "x"; INT 2; IDENT "x"; FLOAT 3.; IDENT "x"]) ;
  ("identifier5 identifier5", [IDENT "identifier5"; IDENT "identifier5"]);
  ("let id", [LET; IDENT "id"])  ;
  ("let id = λx", [LET; IDENT "id"; EQ; LAMBDA; IDENT "x"])  ;
  ("let id = λx.x in id", [LET; IDENT "id"; EQ; LAMBDA; IDENT "x"; DOT; IDENT "x"; IN; IDENT "id"]) ;
  ("let rec x = λx.x in x", [LET; REC; IDENT "x"; EQ; LAMBDA; IDENT "x"; DOT ; IDENT "x"; IN ; IDENT "x"]); 
  ("if then else", [IF; THEN; ELSE]);
  ("⟦a⟧", [LDBRACKET; IDENT "a"; RDBRACKET]);
  ("⟪+⟫", [HOST "+"]);
  ("⟪(*ocaml comment inside constant*)⟫", [HOST "(*ocaml comment inside constant*)"]) ;
  ("⟪(*ocaml comment inside constant*)⟫⟪⟫", [HOST "(*ocaml comment inside constant*)"; HOST "" ]) ;
  ("foo•put", [IDENT "foo" ; BULLET ; PUT ] ) ;
  ("foo•get", [IDENT "foo" ; BULLET ; GET ] ) ;
  ("x←1", [IDENT "x"; LEFTARROW; INT 1 ] );
  ("{}", [LBRACE; RBRACE]);
  ("⇐", [DLEFTARROW]);
  ("replaceable", [REPLACEABLE]);
  ("state", [STATE]);
  ("model", [MODEL]);
  ("with", [WITH]);
  ("extend", [EXTEND]);
  (";", [SEMICOLON]);
  ("return", [RETURN]);
]

let test_case (input, expected) =
  let setup () = (state_from_utf8_string input, expected)
  in
  (Printf.sprintf "test lexing '%s'" input) >:: (bracket setup test_lexing teardown)

let suite = ("Lexer" >::: ( List.map test_case samples )) ;

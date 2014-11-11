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
open Mcl_parser
open Mcl
open Mcl_lexer
open Mcl_pp
open Parsetree

let rec parse ucs = 
  let next () = next_token ucs in    
  expr_parser "test" next

(* ignore locations for comparison *)
let rec compare_exp e1 = function
  | Host(c) -> (expr2str e1) = expr2str (Host c)
  | _ as e2 -> e1 = e2

let test_parsing (ucs, expected) = assert_equal ~cmp:compare_exp ~msg:"equality" ~printer:expr2str expected (parse ucs)

let lift_ident x =
  let loc = {
    Location.loc_start = {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0}; 
    loc_end = {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 1} ; 
    loc_ghost = false} in    
    
  { pexp_desc = Pexp_ident {Asttypes.txt = Longident.Lident x ; loc ; } ; 		
    pexp_loc = loc;
    pexp_attributes = [] }

let samples = [ 
  (" 1.234", Const(Float(1.234)));
  ("x", Var("x")) ;
  ("λx.x", Abs("x", Var("x"))) ;
  ("let v = ⟦1⟧ in v[0]", Let("v", Vec([| Const(Int(1)) |]), Idx(Var("v"), Const(Int(0))) ));
  ("x x", App(Var("x"), Var("x"))) ;
  ("3 > 4", App(App(Host(lift_ident ">"), Const(Int(3))), Const(Int(4))));
  ("3 * 4", App(App(Host(lift_ident "*"), Const(Int(3))), Const(Int(4))));
  ("⟪ Foo ⟫", Host(lift_ident "Foo")) ;
  ("⟪(+)⟫ 40 2", App(App(Host(lift_ident "+"), Const(Int(40))), Const(Int(2))));
  (" 1234", Const(Int(1234)));
  (" 1.234", Const(Float(1.234)));
  ("let x = 42 in x", Let("x", Const(Int(42)), Var("x")));
  ("let x = λx.x in x", Let("x", Abs("x", Var("x")), Var("x")));
  ("let rec x = λx.x in x", Letrec("x", Abs("x", Var("x")), Var("x")));
  ("let f = ⟪(+)⟫ 40 in f 2", Let("f", App(Host(lift_ident "+"), Const(Int(40))), App(Var("f"), Const(Int(2))) ) );
]

let test_case (input, expected) =
  let teardown _ = () in
  let setup () = (state_from_utf8_string input, expected)
  in
  (Printf.sprintf "test parsing '%s'" input) >:: (bracket setup test_parsing teardown)
						  
let suite = "Parser" >:::
	      ( List.map test_case samples )

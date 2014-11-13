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

let erase_locations_mapper = { Ast_mapper.default_mapper with 
			       location = fun mapper l -> Location.none
			     }

let erase_location e = erase_locations_mapper.expr erase_locations_mapper e

let rec erase_location = function
  | Host(c) -> Host ( erase_locations_mapper.expr erase_locations_mapper c )
  | Abs(x, e) -> Abs ( x, erase_location e)
  | App(l, r) -> App ( erase_location l, erase_location r )
  | Let(x, e, i) ->  Let ( x, erase_location e, erase_location i)
  | Letrec(x, e, i) ->  Letrec ( x, erase_location e, erase_location i)
  | Cond(c, t, e) ->  Cond (erase_location c, erase_location t, erase_location e)
  | Idx(e, i) -> Idx(erase_location e, erase_location i)
  | Vec(es) -> Vec ( Array.map erase_location es )
  | Case(e, ps) -> Case(erase_location e, List.map (fun (p, e) -> (p, erase_location e)) ps)
  | Put(l, e) -> Put(l, erase_location e)
  | Return(e) -> Return (erase_location e)
  | Bind(x, l, r) -> Bind(x, erase_location l, erase_location r)
  | Adt(a, es) -> Adt(a, List.map erase_location es)
  | Client e -> Client (erase_location e)
  | _ as e -> e

let test_parsing (ucs, expected) = assert_equal ~cmp:compare_exp ~msg:"equality" ~printer:expr2str (erase_location expected) (erase_location (parse ucs))

let lift_ident x =
  let loc = {
    Location.loc_start = {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0}; 
    loc_end = {Lexing.pos_fname = ""; pos_lnum = 42; pos_bol = 0; pos_cnum = 1} ; 
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
  ("3 > 4", Client(App(App(Host(lift_ident ">"), Const(Int(3))), Const(Int(4)))));
  ("3 * 4", Client(App(App(Host(lift_ident "*"), Const(Int(3))), Const(Int(4)))));
  ("⟪ foo ⟫", Host(lift_ident "foo")) ;
  ("ℒ x", Client(Var("x"))) ;  
  ("-1", Client(App(Host(lift_ident "~-"), Const(Int(1)))));
  ("⟪(>)⟫ (-1) 2", App(App(Host(lift_ident ">"), Client(App(Host(lift_ident "~-"), Const(Int(1))))), Const(Int(2)))) ;
  ("ℒ ⟪ foo ⟫", Client(Host(lift_ident "foo"))) ;
  ("ℒ ⟪(+)⟫ 40 2", Client (App(App(Host(lift_ident "+"), Const(Int(40))), Const(Int(2)))));
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

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

let erase_locations_mapper = { Ast_mapper.default_mapper with 
			       location = fun mapper l -> Location.none
			     }

let rec prep_expr = function
  | Host(c) -> Host ( erase_locations_mapper.expr erase_locations_mapper c )
  | Abs(x, e) -> Abs ( x, prep_expr e)
  | App(l, r) -> App ( prep_expr l, prep_expr r )
  | Let(x, e, i) ->  Let ( x, prep_expr e, prep_expr i)
  | Letrec(x, e, i) ->  Letrec ( x, prep_expr e, prep_expr i)
  | Cond(c, t, e) ->  Cond (prep_expr c, prep_expr t, prep_expr e)
  | Idx(e, i) -> Idx(prep_expr e, prep_expr i)
  | Vec(es) -> Vec ( Array.map prep_expr es )
  | Case(e, tes) -> Case(prep_expr e, StrMap.map prep_expr tes)
  | Put(l, e) -> Put(l, prep_expr e)
  | Return(e) -> Return (prep_expr e)
  | Bind(x, l, r) -> Bind(x, prep_expr l, prep_expr r)
  | New(m) -> New(prep_model m)
  | _ as e -> e

and prep_field = function
    Extend m -> Extend (prep_model m)
  | Unnamed e -> Unnamed (prep_expr e)
  | Named (x, e) -> Named(x, prep_expr e)
  | Replaceable(x, e) -> Replaceable(x, prep_expr e)

and prep_model = function
  | Model(fds) -> Model(List.map prep_field fds)
  | MVar x -> MVar x
  | MLet(x, m, m') -> MLet(x, prep_model m, prep_model m')
  | MState(x, e, m) -> MState(x, prep_expr e, prep_model m)
  | MModify(x, e, m) -> MModify(x, prep_expr e, prep_model m)

let lift_ident = Mcl_ocaml.lift_ident

let expr_test input f =
  let ucs = state_from_utf8_string input in
  let next () = next_token ucs in
  let last () = last_token ucs in
  fun () ->
  try
    f (expr_parser "test" next last)
  with 
    SyntaxError e -> assert_failure (Printf.sprintf "Syntax Error at %s:\n%s" (show_syntax_error e) (error_message e input))

let expr input expected = 
  (Printf.sprintf "Parse '%s'" input) >::: [
    ("parsing" >::
       expr_test input (fun e -> assert_equal ~cmp:equal_expr ~msg:"equality of parsed expression" ~printer:expr2str (prep_expr expected) (prep_expr e)) ) ;
    ("re-parsing" >::
       expr_test input (fun e -> expr_test (expr2str ~max:100 e) (fun e -> assert_equal ~cmp:equal_expr ~msg:"equality of re-parsed expression" ~printer:expr2str (prep_expr expected) (prep_expr e)) ())) ;
  ]
      
  
let model input expected =
  let parse_model input = 
    let ucs = state_from_utf8_string input in
    let next () = next_token ucs in
    let last () = last_token ucs in
    try 
      model_parser "test" next last
    with
      SyntaxError e -> assert_failure (Printf.sprintf "Syntax Error at %s:\n%s" (show_syntax_error e) (error_message e input))
  in
  (Printf.sprintf "Parse '%s'" input) >::: [
    "parsing" >::
      (fun () -> assert_equal ~cmp:equal_model_expr ~msg:"equality of parsed model" ~printer:model2str (prep_model expected) (prep_model (parse_model input)) ) ;
    "re-parsing" >::
      (fun () -> assert_equal ~cmp:equal_model_expr ~msg:"equality of re-parsed model" ~printer:model2str (prep_model expected) (prep_model (parse_model (model2str (parse_model input)) ))) ;
  ]

let test_cases = [ 
  expr "1.234" (Const(Float(1.234)));
  expr "x" (Var("x")) ;
  expr "new_foo" (Var "new_foo");
  expr "λx.x" (Abs("x", Var("x"))) ;
  expr "let v = ⟦1⟧ in v[0]" (Let("v", Vec([| Const(Int(1)) |]), Idx(Var("v"), Const(Int(0))) ));
  expr "x x" (App(Var("x"), Var("x"))) ;
  expr "3 > 4" (App(App(Host(lift_ident ">"), Const(Int(3))), Const(Int(4))));
  expr "3 * 4" (App(App(Host(lift_ident "*"), Const(Int(3))), Const(Int(4))));
  expr "⟪ foo ⟫" (Host(lift_ident "foo")) ;
  expr "-1" (Const(Int(-1)));
  expr "⟪(>)⟫ (-1) 2" (App(App(Host(lift_ident ">"), Const(Int(-1))), Const(Int(2)))) ;
  expr " 1234" (Const(Int(1234)));
  expr " 1.234" (Const(Float(1.234)));
  expr "f -1.234" (App(Var("f"), Const(Float(-1.234))));
  expr "x + y.2 .2" (App(App(Host(lift_ident "+"), Var("x")), Project(2, Project(2, Var("y")))));
  expr "x + y.2[0].1" (App(App(Host(lift_ident "+"), Var("x")), Project(1, Idx(Project(2, Var("y")), Const(Int(0))))));

  expr "let x = 42 in x" (Let("x", Const(Int(42)), Var("x")));
  expr "let x = λx.x in x" (Let("x", Abs("x", Var("x")), Var("x")));
  expr "let rec x = λx.x in x" (Letrec("x", Abs("x", Var("x")), Var("x")));
  expr "let f = ⟪(+)⟫ 40 in f 2" (Let("f", App(Host(lift_ident "+"), Const(Int(40))), App(Var("f"), Const(Int(2))) ) );
  expr "let add a b = a + b in 42" (Let("add", Abs("a",Abs("b", App(App(Host(lift_ident "+"), Var("a")), Var("b")))), Const(Int(42))));

  expr "x.bar" (Method("bar", Var("x")));
  
  expr "xs ← states•get ; x" (Bind("xs", Get("states"), Var("x"))) ;
  expr "xs ← states•put ⟦⟧ ; x" (Bind("xs", Put("states", Vec([||])), Var("x"))) ;

  model "{}" (Model([]));
  model "{1}" (Model([Unnamed (Const(Int 1))]));
  expr "new {1}" (New (Model([Unnamed (Const(Int 1))])));
  model "{1;2;3}" (Model([Unnamed (Const(Int 1)) ; Unnamed (Const(Int 2)) ; Unnamed (Const(Int 3))]));
  model "{extend {}}" (Model([Extend(Model [])])) ;
  model "{extend {} ; x ⇐ u}" (Model([Extend(Model []); Named("x", Var("u"))])) ;
  model "{x ⇐ u}" (Model([Named("x", Var("u"))])) ;
  model "{replaceable x ⇐ u}" (Model([Replaceable("x", Var("u"))])) ;
  model "replace x with y in m" (MModify("x", Var("y"), MVar("m"))) ;

  expr "return 1" (Return ( Const (Int 1))) ;
  expr "x ← g ; f 1" (Bind("x", Var("g"), App(Var("f"), Const(Int(1))))) ;
  expr "x ← g ; x ← g ; return x" (Bind("x", Var("g"), Bind("x", Var("g"), Return(Var("x"))))) ;

  expr "(1,2).1" (Project(1, Tup [Const (Int 1); Const (Int 2)] ));
]
						  
let suite = "Parser" >::: test_cases

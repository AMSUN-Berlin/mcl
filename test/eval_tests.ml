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
open Mcl_dynamics

let samples = [
  ("42", VConst(Int(42)) );
  ("42.", VConst(Float(42.)) );
  ("⟪(+)⟫ 40 2", VConst(Int(42)) );
  ("⟪(>)⟫ 40 2 ", VConst(Bool(true)) );
  ("let v = ⟦1⟧ in v[0]", VConst(Int(1)));
  ("let f = ⟪(+)⟫ 40 in (f 2)", VConst(Int(42)) );
  ("-1", VConst(Int(-1)) );
  ("⟪(>)⟫ 0 2", VConst(Bool(false)));
  ("⟪(>)⟫ (-1) 2", VConst(Bool(false)));

  ("⟦1;2;3⟧", VVec([|VConst(Int(1));VConst(Int(2));VConst(Int(3));|])) ;

  ("(1,2.,1+2)", VTup([VConst(Int(1)); VConst(Float(2.)); VConst(Int(3))]));
  ("(0., ⟦⟧, -9.81, 1.2)", VTup([VConst(Float(0.));VVec([||]);VConst(Float(-9.81));VConst(Float(1.2))])) ;
  ("#⟦⟧"), VConst(Int(0));

  ("let rec fac = λn.if n > 0 then n * (fac (n - 1)) else 1 in fac 1",  VConst(Int(1)));
  ("let rec fac = λn.if n > 0 then n * (fac (n - 1)) else 1 in fac 2",  VConst(Int(2)));
  ("let rec fac = λn.if n > 0 then n * (fac (n - 1)) else 1 in fac 3",  VConst(Int(6)));
  ("let rec fac = λn.if n > 0 then n * (fac (n - 1)) else 1 in fac 6",  VConst(Int(720)));

  ("return 1", VMonad(MReturn(VConst(Int(1)))));
]

let test_case (input, expected) =
  (Printf.sprintf "test evaluating '%s'" input) >:: (Parser_tests.expr_test input
                                                                            (fun e -> assert_equal ~msg:"equality" ~printer:val2str expected (eval (e))))
                                                      
let test_subst (i,x,s,ex) = assert_equal ~msg:"equality" ~printer:expr2str ex (subst x (lift_value s) i)

let subst_samples = [
  (App(Var("f"), Var("x")), "f", VAbs("x", Var("x")), App(Abs("x", Var("x")), Var("x")));
]

let subst_test_case (i, x, s, ex) =
  let teardown _ = () in
  let setup () = (i, x, s, ex) in
  (Printf.sprintf "test substituting '%s' for '%s' in '%s'" x (val2str s) (expr2str i) ) >:: (bracket setup test_subst teardown)
 

let subst_suite = "Substitution" >::: ( List.map subst_test_case subst_samples)
						  
let suite = "Interpreter" >:::	      
	      ( List.map test_case samples )

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
open Batteries
open Mcl_parser
open Mcl
open Mcl_lexer
open Mcl_pp
open Mcl_ocaml
open Mcl_dynamics

let ocaml_interpreter = Mcl_ocaml.ocaml_interpreter ()

let eval e = 
  match ocaml_interpreter with 
    Some ocaml_interpreter -> begin
			     match (ocaml_interpreter (mclc e)) with
			       Result.Ok (_, v) -> object_value v
			     | Result.Bad err -> VConst(Err(err))
    end
  | None -> VConst(Err("Error loading OCaml interpreter"))

let test_case (input, expected) =
  let msg = Printf.sprintf "Check equality with '%s'" (val2str expected) in
  let equals e = (bin_op "=" e (lift_value expected)) in
  (Printf.sprintf "test evaluating '%s'" input) >:: (Parser_tests.expr_test input (fun e -> assert_equal ~msg:msg ~printer:val2str (VConst (Bool true)) (eval (equals e))))

let samples = [
  ("true", VConst(Bool(true)));
  ("42", VConst(Int(42)) );
  ("42.", VConst(Float(42.)) );
  ("⟪(+)⟫ 40 2", VConst(Int(42)) );
  ("⟪(>)⟫ 40 2 ", VConst(Bool(true)) );
  ("let v = ⟦1⟧ in v[0]", VConst(Int(1)));
  ("let f = ⟪(+)⟫ 40 in (f 2)", VConst(Int(42)) );
  ("-1", VConst(Int(-1)) );
  ("⟪(>)⟫ 0 2", VConst(Bool(false)));
  ("⟪(>)⟫ (-1) 2", VConst(Bool(false)));

  ("let rec fac = λn.if n > 0 then n * (fac (n - 1)) else 1 in fac 1",  VConst(Int(1)));
  ("let rec fac = λn.if n > 0 then n * (fac (n - 1)) else 1 in fac 2",  VConst(Int(2)));
  ("let rec fac = λn.if n > 0 then n * (fac (n - 1)) else 1 in fac 3",  VConst(Int(6)));
  ("let rec fac = λn.if n > 0 then n * (fac (n - 1)) else 1 in fac 6",  VConst(Int(720)));

  ("let foo = None in match foo with None -> 1 | Some d -> d in foo", VConst(Int(1)));

  ("⟦1;2;3⟧", VVec([|VConst(Int(1));VConst(Int(2));VConst(Int(3));|])) ;

  ("(1,2.,1+2).3", VConst(Int(3)));
  ("#⟦⟧"), VConst(Int(0));
  ("#⟦⟦⟧ with 0 = 1⟧"), VConst(Int(1));
  ("⟦⟦⟧ with 0 = 1⟧[0]"), VConst(Int(1));  
]
						  
let suite = "Compiler" >:::	      
	      ( List.map test_case samples )

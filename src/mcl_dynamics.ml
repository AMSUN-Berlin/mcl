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

open Mcl
open Mcl_pp
open Batteries
    
let error_expected op exp got =
  VConst( Err ( Printf.sprintf "in '%s' expected: %s but got: '%s'" op exp got ) )

module StrMap = Map.Make(String)
module StrSet = Set.Make(String)

let bool_poly_bin_ops = StrSet.of_enum (List.enum [
					    "(>)" ;
					    "(<)";
					    "(>=)";
					    "(<=)";
					    "(!=)";
					    "(=)" ;
					    "(<>)";
				     ])

let bool_poly_op_apply a b = function
  | "(>)" -> a > b
  | "(<)" -> a < b
  | "(>=)" -> a >= b
  | "(<=)" -> a <= b
  | "(<>)" -> a <> b
  | "(!=)" -> a != b
  | "(=)" -> a = b

let int_bin_op_apply a b = function
  | "(+)" -> a + b
  | "(-)" -> a - b
  | "(/)" -> a / b
  | "( * )" -> a * b

let int_int_bin_ops = StrSet.of_enum (List.enum [
					  "(+)" ;
					  "(-)" ;
					  "( * )" ;
					  "(/)" ;
				     ])

let int_bin_ops = StrSet.union int_int_bin_ops bool_poly_bin_ops

let rec pass_error e f = match eval e with
  | VConst(Err msg) as err -> err
  | _ as v -> f v

and eval_array es vs i = if i < (Array.length es) then
			   pass_error es.(i) (fun v -> (vs.(i) <- v ; eval_array es vs (i+1)))
			 else
			   VVec(vs)

and eval = function
  | Const c -> VConst c
  | Abs(x,e) -> VAbs(x,e)

  | Cond(i,t,e) -> begin match eval i with
			 | VConst(Err(_)) as err -> err
			 | VConst(Bool(true)) -> eval t
			 | VConst(Bool(false)) -> eval e
			 | _ as v -> error_expected (expr2str i) "boolean value" (val2str v)
		   end

  | App(e1, e2) as app -> begin match eval e1 with 			   
				| VConst(Err msg) as err -> err
				| VAbs(y, e3) -> eval ( subst y ( eval e2 ) e3 )

				(* int/poly operator application on int, first argument *)
				| VConst(Prim(op, [])) when StrSet.mem op int_bin_ops -> 
				   begin match eval e2 with
					 | VConst(Int(a)) -> VConst(Prim(op, [VConst(Int(a))]))
					 | VConst(Err msg) as err -> err
					 | _ as v -> error_expected (expr2str app) "int-argument" (val2str v)
				   end

				(* int operator application, second argument *)
				| VConst(Prim(op, [VConst(Int(a))])) when StrSet.mem op int_int_bin_ops -> 
				   begin match eval e2 with
					 | VConst(Int(b)) -> VConst(Int(int_bin_op_apply a b op))					    
					 | VConst(Err msg) as err -> err
					 | _ as v-> error_expected (expr2str app) "int-argument" (val2str v) 
				   end

				(* poly operator application on int, second argument *)
				| VConst(Prim(op, [VConst(Int(a))])) when StrSet.mem op bool_poly_bin_ops -> 
				   begin match eval e2 with
					 | VConst(Int(b)) -> VConst(Bool(bool_poly_op_apply a b op))					    
					 | VConst(Err msg) as err -> err
					 | _ as v-> error_expected (expr2str app) "int-argument" (val2str v) 
				   end

				| VConst(Prim(op, _)) -> VConst(Err(Printf.sprintf "Unknown primitive operation '%s'" op))

				| _ as v -> error_expected (expr2str app) "function value" (val2str v) 
			  end

  | Let(x, e1, e2) -> pass_error e1 (fun v -> eval ( subst x v e2 ))

  | Letrec(x,e1,e2) -> begin match  eval e1 with 
			       VAbs(y, e3) -> let v = VAbs(y, Letrec(x,e1,e3)) in
					      eval ( subst x v e2 )
			     | _ -> VConst ( Err (Printf.sprintf "'%s' is not a function" x))
		       end

  | Vec(es) -> eval_array es (Array.map (fun _ -> unit_val) es) 0

  | Idx(e1, e2) -> pass_error e1 (function 
				   | VVec(vs) ->
				      pass_error e2 (function						      
						      | VConst(Int(idx)) when idx >= (Array.length vs) || idx < 0 -> 
							 error_expected (expr2str e2) "valid index" (string_of_int idx)
						      | VConst(Int(idx)) -> vs.(idx)
						      | _ as v -> error_expected (expr2str e2) "int value" (val2str v)
						    )
				   | _ as v -> error_expected (expr2str e1) "vector value" (val2str v)
				 )

  | Get(l) -> VMonad(MGet(l))

  | Put(l, e) -> begin match eval e with
		       | VConst(Err msg) -> VConst(Err msg)
		       | _ as v -> VMonad(MPut(l, v))
		 end

  | Return(e) -> begin match eval e with
		       | VConst(Err msg) -> VConst(Err msg)
		       | _ as v -> VMonad(MReturn(v))	 
		 end

  | Bind(x, e1, e2) -> begin match eval e1 with
			     | VConst(Err msg) -> VConst(Err msg)
			     | VMonad(m) -> VMonad(MChain(x, m, e2))
			     | _ as v -> error_expected (expr2str e1) "monadic value" (val2str v) 
		       end

  | _ as exp -> VConst (Err (Printf.sprintf "Don't know how to evaluate '%s'. Confused." (expr2str exp)))
		       

let rec elab s = function
  | MReturn(v) -> (s, v)
  | MGet(l) -> (s, StrMap.find l s) (* TODO: error handling *)
  | MPut(l, v) -> (StrMap.add l v s, VVec( [| |] ) ) (* TODO: error handling *)
  | MChain(x, m, e) -> 
     let (s', v) = elab s m in 
     begin
       match eval (subst x v e) with
       | VConst(Err msg) -> (s, VConst(Err msg))
       | VMonad(m') -> elab s' m'
       | _ as v -> (s, error_expected (expr2str e) "monadic value" (val2str v))
     end

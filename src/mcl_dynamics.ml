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
open Format
open Batteries
open Outcometree

module StrMap = Map.Make(String)

type value = VConst of const
	   | VAbs of string * expr
	   | VAdt of string * (value list)
	   | VObj of (expr StrMap.t)
	   | VMonad of monad
	   | VVec of value array
	   | VHost of out_value * string

and monad = MGet of string 
	   | MPut of string * value
	   | MReturn of value 
	   | MChain of string * monad * expr

let unit_val = VVec([||])

let rec pp_field fmt (x,e) = fprintf fmt "%s@ =@ %a" x pp_expr e

let rec pp_val fmt = function 
  | VHost(v,_) -> fprintf fmt "⟪%a⟫" (!Oprint.out_value) v
  | VConst c -> fprintf fmt "@[%a@]" pp_const c
  | VAbs(x, e) -> fprintf fmt "@[(λ%s.%a)@]" x pp_expr e
  | VMonad(m) -> pp_monad fmt m
  | VVec(vs) -> fprintf fmt "@[⟦%a⟧@]" (pp_list ~sep:";" pp_val) (Array.to_list vs)
  | VAdt(a, vs) -> fprintf fmt "@[%s⟨%a⟩@]" a (pp_list ~sep:";" pp_val) vs
  | VObj ms -> fprintf fmt "@[⦃%a⦄@]" (pp_enum ~sep:";" pp_field) (StrMap.enum ms)

and pp_monad fmt = function
  | MReturn v -> fprintf fmt "@[return@ %a@]" pp_val v
  | MPut (l, v) -> fprintf fmt "@[%s•put@ %a@]" l pp_val v
  | MGet (l) -> fprintf fmt "@[%s•get@]" l
  | MChain (x, m, e) -> fprintf fmt "@[%s@ ←@ %a@ ;@ %a]" x pp_monad m pp_expr e

let val2str v = 
  (pp_val Format.str_formatter v) ;
  Format.flush_str_formatter ()

let ident x = {Asttypes.txt = Longident.Lident x ; loc = Location.none}

let rec lift_monad = function 
  | MGet s -> Get s 
  | MReturn v -> Return (lift_value v) 
  | MPut(s,v) -> Put(s, lift_value v) | MChain(x, m, e) -> Bind(x, lift_monad m, e)
		
and lift_value = function
  | VConst c   -> Const c 
  | VAbs (x,e) -> Abs(x,e)
  | VVec vs -> Vec (Array.map lift_value vs)
  | VAdt (a, vs) -> Adt(a, List.map lift_value vs)
  | VMonad (m) -> lift_monad m 
  | VHost (_, x) -> Host (Ast_helper.Exp.ident  (ident x))
        
let error_expected op exp got =
  VConst( Err ( Printf.sprintf "in '%s' expected: %s but got: '%s'" op exp got ) )

module StrSet = Set.Make(String)

let ocaml_interpreter = Mcl_ocaml.ocaml_interpreter ()


let rec pass_error e f = match eval e with
  | VConst(Err msg) as err -> err
  | _ as v -> f v

and eval_array es vs i = if i < (Array.length es) then
			   pass_error es.(i) (fun v -> (vs.(i) <- v ; eval_array es vs (i+1)))
			 else
			   VVec(vs)

and lift_back e = pass_error e (function 
  | VHost (Oval_constr ( Oide_ident "true", [] ), _) -> VConst (Bool true )
  | VHost (Oval_constr ( Oide_ident "false", [] ), _) -> VConst (Bool false)
  | VHost (Oval_float f, x) -> VConst (Float f)
  | VHost (Oval_int i, x) -> VConst (Int i)
  | VHost (v, x) -> VHost(v, x)
  | v -> error_expected (expr2str e) "host language value" (val2str v))

and eval_host_app x e = 
 lift_back (Host (Ast_helper.Exp.apply (Ast_helper.Exp.ident (ident x)) [("", e)]))

and eval = function
   
  | Const c -> VConst c
  | Abs(x,e) -> VAbs(x,e)

  | Host ( h ) -> begin match ocaml_interpreter with 
			  Some(eval) -> 
			  begin 
			    match eval h with
			      Ok(x,v) -> VHost ( v, x )
			    | Bad(err) -> VConst(Err(err))
			  end
			| None -> VConst(Err("No working OCaml interpreter loaded."))
		  end

  | Cond(i,t,e) -> 
     begin match eval i with
	   | VConst(Err(_)) as err -> err
	   | VConst(Bool(true)) -> eval t
	   | VConst(Bool(false)) -> eval e
	   | v -> error_expected (expr2str i) "boolean value" (val2str v)
     end

  | App(e1, e2) as app -> pass_error e1 (function  			   
				| VConst(Err msg) as err -> err
				| VAbs(y, e3) -> eval ( subst y ( lift_value (eval e2) ) e3 )
				| VHost(_,x) as f -> pass_error e2 (function
						      | VConst (Bool b) -> 
							 eval_host_app x (Ast_helper.Exp.ident (ident (string_of_bool b)))
						      | VConst (Float f) -> 
							 eval_host_app x (Ast_helper.Exp.constant (Asttypes.Const_float (string_of_float f)))						 
						      | VConst (Int i) -> 
							 eval_host_app x (Ast_helper.Exp.constant (Asttypes.Const_int i))
						      | v -> VConst(Err(Printf.sprintf "Currently, only literal arguments are supported to OCaml expressions, got '%s'\n" (val2str v)))
								   )
				| _ as v -> error_expected (expr2str app) "function value" (val2str v) 
					)

  | Let(x, e1, e2) -> pass_error e1 (fun v -> eval ( subst x (lift_value v) e2 ))

  | Letrec(x,e1,e2) -> begin match  eval e1 with 
			       VAbs(y, e3) -> let r = Abs(y, Letrec(x,e1,e3)) in
					      let e' = subst x r e2 in
					      eval ( subst x r e2 )
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

(*
and meval = function
  | Model(fds) ->
  | MLet (x, m, m') -> 
  | MState (x, e, m) ->
  | MModify (x, e, m) ->
  | _ as m -> VConst (Err (Printf.sprintf "Don't know how to evaluate '%s'. Confused." (m2str m)))
 *)

let rec elab s = function
  | MReturn(v) -> (s, v)
  | MGet(l) -> (s, StrMap.find l s) (* TODO: error handling *)
  | MPut(l, v) -> (StrMap.add l v s, VVec( [| |] ) ) (* TODO: error handling *)
  | MChain(x, m, e) -> 
     let (s', v) = elab s m in 
     begin
       match eval (subst x (lift_value v) e) with
       | VConst(Err msg) -> (s, VConst(Err msg))
       | VMonad(m') -> elab s' m'
       | _ as v -> (s, error_expected (expr2str e) "monadic value" (val2str v))
     end

open Outcometree

let object_value = function
  | Oval_constr ( Oide_ident "true", [] ) -> VConst (Bool true )
  | Oval_constr ( Oide_ident "false", [] ) -> VConst (Bool false )
  | Oval_float f -> VConst (Float f)
  | Oval_int i -> VConst (Int i)
  | _ -> VConst(Err("cannot translate OCaml non-literal back to mcl"))

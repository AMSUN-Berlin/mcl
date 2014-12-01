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
open Ast_helper
open Parsetree
open Location

let lift_lid x = mknoloc (  Longident.Lident x )

let lift_ident x =
  { pexp_desc = Pexp_ident (lift_lid x) ; 		
    pexp_loc = none;
    pexp_attributes = [] }

let array_get = 
  { pexp_desc = Pexp_ident {Asttypes.txt = Longident.Ldot (Longident.Lident "Array", "get") ; loc = none ; } ; 		
    pexp_loc = none;
    pexp_attributes = [] }

open Exp

let patc  = function 
  | (c, []) -> Pat.construct (lift_lid c) None
  | (c, xs) -> Pat.construct (lift_lid c) (Some (Pat.tuple (List.map (fun x -> Pat.var (mknoloc x)) xs)))

let rec constc = function
  | Float f -> constant (Const_float (string_of_float f))
  | Int i -> constant (Const_int i)
  | Bool true -> lift_ident "true"
  | Bool false -> lift_ident "false"
  | Err e -> apply (lift_ident "raise") ["", (apply (lift_ident "Invalid_Argument") ["", (constant (Const_string (e, None)))])]

let rec mclc = function
  | Var x -> lift_ident x 
  | Host e -> e
  | Abs(x, e) -> fun_ "" None (Pat.var (mknoloc x)) (mclc e)
  | App(l,r) -> apply (mclc l) [("", (mclc r))]
  | Let(x, e, i) -> let_ Nonrecursive [{ pvb_pat = Pat.var (mknoloc x) ; pvb_expr = mclc e ; pvb_attributes = [] ; pvb_loc = none }] (mclc i)
  | Letrec(x, e, i) -> let_ Recursive [{ pvb_pat = Pat.var (mknoloc x) ; pvb_expr = mclc e ; pvb_attributes = [] ; pvb_loc = none }] (mclc i)

  | Cond(c, t, e) -> ifthenelse (mclc c) (mclc t) (Some (mclc e))
  | Const c -> constc c

  | Vec es -> array (List.map mclc (Array.to_list es)) 
  | Idx (a, i) -> apply (array_get) ["", mclc a ; "", mclc i]

and casec (patt, e) = case (patc patt) (mclc e) 
			

			 (*
  | Case(e, ps) -> fprintf fmt "@[match@ %a@ with@ %a@]" pp_expr e (pp_list pp_pat) ps
  | Get(l) -> fprintf fmt "@[%s•get@]" l
  | Put(l, e) -> fprintf fmt "@[%s•put@ %a@]" l pp_expr e
  | Return(e) -> fprintf fmt "@[return@ %a@]" pp_expr e
  | Bind(x, e1, e2) -> fprintf fmt "@[%s@ ←@ %a@ ;@ %a]" x pp_expr e1 pp_expr e2
			  *)
let lift_to_phrase x e = Ptop_def [{pstr_desc = Pstr_value (Asttypes.Nonrecursive,
							    [{ pvb_pat = {ppat_desc = Ppat_var {Asttypes.txt = x; loc = Location.none } ;
									  ppat_loc = Location.none ;
									  ppat_attributes = [] ; 
									 } ;
							       pvb_expr = e ;
							       pvb_attributes = [];
							       pvb_loc = Location.none ;								     
							   }] ) ; 
				    pstr_loc = Location.none }]

open BatResult
open Ocaml_common

let fresh_var_counter = ref 0 
let _ocaml_interpreter = ref None

let ocaml_interpreter () = !_ocaml_interpreter

let compile_and_eval_expr execute_phrase e = 
  let x = Printf.sprintf "$tmp%d" !fresh_var_counter in
  incr fresh_var_counter ;
  try 
    let {success;result} = execute_phrase true Format.str_formatter (lift_to_phrase x e) in
    let output = Format.flush_str_formatter () in

    if success then
      match result with
      | Ophr_exception (exn,_) -> Bad (Printexc.to_string exn)
      | Ophr_eval(v,_) -> Ok (x, v)
      | Ophr_signature ((_,Some(v))::_) -> Ok (x,v)
      | _ -> Bad output
    else
      Bad output
  with
  | e -> Location.report_exception Format.std_formatter e ; raise e

let _ = 
  fresh_var_counter := 0 ;  
  try 
    Ocaml_toploop.initialize_toplevel_env () ;
    _ocaml_interpreter := Some (compile_and_eval_expr Ocaml_toploop.execute_phrase)
  with
  (* bytecode interpreter unable to load, try native code interpreter *)
  | Invalid_argument _ -> 
     Ocaml_opttoploop.initialize_toplevel_env () ;
     _ocaml_interpreter := Some (compile_and_eval_expr Ocaml_opttoploop.execute_phrase)

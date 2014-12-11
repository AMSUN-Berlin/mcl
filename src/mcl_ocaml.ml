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

open Batteries
open Mcl
open Mcl_pp
open Ast_helper
open Asttypes
open Parsetree
open Location
open Exp

let lift_lid x = mknoloc (  Longident.Lident x )

let lift_ident x =
  { pexp_desc = Pexp_ident (lift_lid x) ; 		
    pexp_loc = none;
    pexp_attributes = [] }

let lift_construct ?arg:e x =
  { pexp_desc = Pexp_construct ((lift_lid x), e) ; 		
    pexp_loc = none;
    pexp_attributes = [] }


let bin_op op e1 e2 = 
  App(App((Host(lift_ident op)), e1), e2)

let rec app f e = function
    [] -> App (f, e)
  | e'::es -> app (App (f, e)) e' es

let array_get = 
  { pexp_desc = Pexp_ident {Asttypes.txt = Longident.Ldot (Longident.Lident "Array", "get") ; loc = none ; } ; 		
    pexp_loc = none;
    pexp_attributes = [] }

let array_set = 
  { pexp_desc = Pexp_ident {Asttypes.txt = Longident.Ldot (Longident.Lident "Array", "set") ; loc = none ; } ; 		
    pexp_loc = none;
    pexp_attributes = [] }

let array_copy = 
  { pexp_desc = Pexp_ident {Asttypes.txt = Longident.Ldot (Longident.Lident "Array", "copy") ; loc = none ; } ; 		
    pexp_loc = none;
    pexp_attributes = [] }

let array_append = 
  { pexp_desc = Pexp_ident {Asttypes.txt = Longident.Ldot (Longident.Lident "Array", "append") ; loc = none ; } ; 		
    pexp_loc = none;
    pexp_attributes = [] }

let array_singleton e = array [e]

let array_change = fun_ "" None (Pat.var (mknoloc "i")) (
                          fun_ "" None (Pat.var (mknoloc "e")) (
                                 fun_ "" None (Pat.var (mknoloc "a")) (
                                        sequence
                                        (apply array_set ["", lift_ident "a"; "", lift_ident "i"; "", lift_ident "e"])
                                        (lift_ident "a")
                                      )
                               )
                        )
(* update array in-place and return it *)

let array_length = 
  { pexp_desc = Pexp_ident {Asttypes.txt = Longident.Ldot (Longident.Lident "Array", "length") ; loc = none ; } ; 		
    pexp_loc = none;
    pexp_attributes = [] }

let patc  = function 
  | (c, []) -> Pat.construct (lift_lid c) None
  | (c, xs) -> Pat.construct (lift_lid c) (Some (Pat.tuple (List.map (fun x -> Pat.var (mknoloc x)) xs)))

let rec constc = function
  | Float f -> constant (Const_float (string_of_float f))
  | Int i -> constant (Const_int i)
  | Bool true -> lift_construct "true"
  | Bool false -> lift_construct "false"
  | Err e -> apply (lift_ident "raise") ["", (lift_construct ~arg:(constant (Const_string (e, None))) "Invalid_argument")]

let hidden_state = "__s"

let put l = send (lift_ident hidden_state) ("put_" ^ l)

let get l = send (lift_ident hidden_state) ("get_" ^ l)

let binding x e = { pvb_pat = Pat.var (mknoloc x) ; pvb_expr = e ; pvb_attributes = [] ; pvb_loc = none }
                 
let ocaml_unit = lift_construct "()"

let monad e = fun_ "" None (Pat.var (mknoloc hidden_state)) (
                     let state' = hidden_state ^ "'" in
                     let x = "x" in
                     let id_arg = tuple [ lift_ident hidden_state ; lift_ident state' ] in
                     let_ Nonrecursive [{ pvb_pat = Pat.tuple [Pat.var (mknoloc (state')); Pat.var (mknoloc x)];
                                          pvb_expr = e ;
                                          pvb_attributes = [] ;
                                          pvb_loc = none ;
                                        }]
                          (tuple [apply (lift_ident "type_ident") ["", id_arg] ; lift_ident x])
                   )

let type_ident = (fun_ "" None
                       (Pat.constraint_ (Pat.tuple [Pat.var (mknoloc "a") ; Pat.var (mknoloc "b")])
                                        (Typ.tuple [Typ.var "a" ; Typ.var "a"])) (lift_ident "b"))
                   
let mclc_prefix e = let_ Nonrecursive [binding "type_ident" type_ident] e
(* attach required prefix (i.e. core functions used by the compiler) to an ocaml expression *)
                         
let rec mclc = function
  | Var x -> lift_ident x 
  | Host e -> e
  | Abs(x, e) -> fun_ "" None (Pat.var (mknoloc x)) (mclc e)
  | App(l,r) -> apply (mclc l) [("", (mclc r))]
  | Let(x, e, i) -> let_ Nonrecursive [binding x (mclc e)] (mclc i)
  | Letrec(x, e, i) -> let_ Recursive [binding x (mclc e)] (mclc i)

  | Cond(c, t, e) -> ifthenelse (mclc c) (mclc t) (Some (mclc e))
  | Const c -> constc c

  | Vec es -> array (List.map mclc (Array.to_list es)) 
  | Idx (a, i) -> apply (array_get) ["", mclc a ; "", mclc i]
  | Length (e) -> apply (array_length) ["", mclc e]
  | Update(a, i, e) -> mclc (array_update a i e)
  | Tup (es) -> object_ ( Cstr.mk (Pat.any ()) (tuple_fields 1 es) )
  | Project (n, e) -> let mthd = "pj_" ^ (string_of_int n) in
                      send (mclc e) mthd 

  | Return e  -> monad (tuple [lift_ident hidden_state ; mclc e])
  | Put(l, e) -> monad (tuple [apply (put l) ["", mclc e] ; ocaml_unit])
  | Get(l) -> monad (tuple [lift_ident hidden_state ; get l])
  | Bind(x, m, e) ->
     let continue = (apply (mclc (Abs(x,e))) ["", lift_ident x ; "", lift_ident hidden_state]) in
     
     monad (let_ Nonrecursive [{ pvb_pat = Pat.tuple [Pat.var (mknoloc hidden_state); Pat.var (mknoloc x)];
                                 pvb_expr = (apply (mclc m) ["", lift_ident hidden_state]);
                                 pvb_attributes = [] ;
                                 pvb_loc = none ;
                               }]
                 continue)
                   
and array_update a i  e = Let("src", a,
                              Let("len", Length(a),
                                  Let("idx", i, 
                                      Cond(bin_op "&&" (bin_op ">=" (Var "idx") (Const (Int 0))) (bin_op "<" (Var "idx") (Var "len")), 
                                           app (Host array_change) (Var "idx") [e; App ((Host array_copy), Var("src"))],
                                           Cond(bin_op "=" (Var "idx") (Var "len"), 
                                                app (Host array_append) (Var "src")  [Host(array_singleton (mclc e))],
                                                Const(Err("Array index out of bounds"))
                                               )
                                          )
                                     )
                                 )
                             )
(* Functional array update:
   If idx > 0 && idx < length then copy & update-in-place else if idx = length append else error 
*)

and tuple_fields n = function 
  | [] -> []
  | e::r -> let x = string_of_int n in 
            (Cf.val_ (mknoloc ("val_" ^ x)) Immutable (Cfk_concrete(Fresh, mclc e))) ::
              (Cf.method_ (mknoloc ("pj_" ^ x)) Public (Cfk_concrete(Fresh, lift_ident ("val_" ^ x)))) :: (tuple_fields (n+1) r)

and state_field (x, e) = List.enum [(Cf.val_ (mknoloc x) Immutable (Cfk_concrete(Fresh, mclc e))) ; 
                                    (Cf.method_ (mknoloc ("get_" ^ x)) Public (Cfk_concrete(Fresh, lift_ident x))) ;
                                    (Cf.method_ (mknoloc ("put_" ^ x)) Public (
                                                  let x' =  x ^ "'" in
                                                  Cfk_concrete(Fresh, fun_ "" None (Pat.var (mknoloc (x'))) (override [mknoloc x, lift_ident x']) )
                                                )
                                    ) ;
                                   ]

let rec statec s = object_ ( Cstr.mk (Pat.var (mknoloc "self")) (List.of_enum (Enum.concat_map state_field (StrMap.enum s))) )

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

let ident2pat x = {ppat_desc = (* TODO: tuple *) Ppat_var {Asttypes.txt = x; loc = Location.none } ; ppat_loc = Location.none ; ppat_attributes = []}

let lift_to_elab_phrase x s state e = Ptop_def [{pstr_desc = Pstr_value (Asttypes.Nonrecursive,
							    [{ pvb_pat = {ppat_desc = Ppat_tuple [ident2pat s; ident2pat x] ;
									  ppat_loc = Location.none ;
									  ppat_attributes = [] ; 
									 } ;
							       pvb_expr = apply e [("", state)];
							       pvb_attributes = [];
							       pvb_loc = Location.none ;								     
							   }] ) ; 
				    pstr_loc = Location.none }]

open Result
open Result.Infix
open Ocaml_common
open Outcometree
  
let fresh_var_counter = ref 0 
let _ocaml_interpreter = ref None
let _ocaml_elaborator = ref None

let ocaml_interpreter () = !_ocaml_interpreter

let ocaml_elaborator () = !_ocaml_elaborator

let unpack x msg = function
  | Ophr_exception (exn,_) -> Bad (Printexc.to_string exn)
  | Ophr_eval(v,_) -> Ok (x, v)
  | Ophr_signature ((_,Some(v))::_) -> Ok (x,v)
  | _ -> Bad msg
             
let compile_and_eval_expr execute_phrase e = 
  let x = Printf.sprintf "$tmp%d" !fresh_var_counter in
  incr fresh_var_counter ;
  try 
    let {success;result} = execute_phrase true Format.str_formatter (lift_to_phrase x e) in
    let output = Format.flush_str_formatter () in

    if success then
      unpack x output result
    else
      Bad output
  with
  | e -> Location.report_exception Format.str_formatter e ; Bad (Format.flush_str_formatter ())

let compile_and_elaborate_expr execute_phrase state e = 
  let x = Printf.sprintf "$tmp%d" !fresh_var_counter in
  let s = Printf.sprintf "$state%d" !fresh_var_counter in
  
  incr fresh_var_counter ;
  try 
    let {success;result} = execute_phrase true Format.str_formatter (lift_to_elab_phrase x s state e) in
    let output = Format.flush_str_formatter () in

    if success then
      match result with
      | Ophr_exception (exn,_) -> Bad (Printexc.to_string exn)
      | _ -> let r = (execute_phrase true Format.str_formatter (lift_to_phrase "x" (lift_ident x))).result in
             unpack "x" (Format.flush_str_formatter ()) r                               
    else
      Bad output
  with
  | e -> Location.report_exception Format.str_formatter e ; Bad (Format.flush_str_formatter ())

let _ = 
  fresh_var_counter := 0 ;  
  try 
    Warnings.parse_options false "-26" ;
    Ocaml_toploop.initialize_toplevel_env () ;
    _ocaml_interpreter := Some (compile_and_eval_expr Ocaml_toploop.execute_phrase) ;
    _ocaml_elaborator := Some (compile_and_elaborate_expr Ocaml_toploop.execute_phrase)
  with
  (* bytecode interpreter unable to load, try native code interpreter *)
  | Invalid_argument _ -> 
     Ocaml_opttoploop.initialize_toplevel_env () ;
     _ocaml_interpreter := Some (compile_and_eval_expr Ocaml_opttoploop.execute_phrase) ;
     _ocaml_elaborator := Some (compile_and_elaborate_expr Ocaml_opttoploop.execute_phrase)
                              

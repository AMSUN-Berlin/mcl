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
	   | VObj of (value StrMap.t)
	   | VMonad of monad
	   | VVec of value array
	   | VHost of out_value * string
           | VTup of value list
           | VTagged of tag * value
                                    
and model_value = MEmpty
		| MField of string * monad * model_value

and monad = MGet of string 
	   | MPut of string * value
	   | MReturn of value 
	   | MChain of string * monad * expr
	   | MNew of model_value

let unit_val = VVec([||])


let rec monad_subst x e = function
    MGet l -> MGet l
  | MPut (l, e') -> MPut(l, e')
  | MReturn(e') -> MReturn e'
  | MChain(y, m, e) when y = x -> MChain(y, m, e)
  | MChain(y, m, e) -> MChain(y, monad_subst x e m, subst x e e)
  | MNew(mv) -> MNew(mv_subst x e mv)

and mv_subst x e =  function 
    MEmpty -> MEmpty
  | MField(y, m, mv) when y = x -> MField(y, m, mv)
  | MField(y, m, mv) -> MField(y, monad_subst x e m, mv_subst x e mv)

let rec pp_field fmt (x,e) = fprintf fmt "%s@ =@ %a" x pp_val e

and pp_val fmt = function 
  | VHost(v,_) -> fprintf fmt "⟪%a⟫" (!Oprint.out_value) v
  | VConst c -> fprintf fmt "@[%a@]" pp_const c
  | VAbs(x, e) -> fprintf fmt "@[(λ%s.%a)@]" x pp_expr e
  | VMonad(m) -> pp_monad fmt m
  | VVec(vs) -> fprintf fmt "@[⟦%a⟧@]" (pp_list ~sep:";" pp_val) (Array.to_list vs)
  | VTagged(tag, v) -> fprintf fmt "@[[⟨%s@ %a⟩@]" tag pp_val v
  | VObj ms -> fprintf fmt "@[⦃%a⦄@]" (pp_enum ~sep:";" pp_field) (StrMap.enum ms)
  | VTup(vs) -> fprintf fmt "@[(%a)@]" (pp_list ~sep:"," pp_val) vs
                       
and pp_model_val fmt = fprintf fmt "[@{%a}@]" pp_model_val' 

and pp_model_val' fmt = function
  | MEmpty -> ()
  | MField(x, m, v) -> fprintf fmt "@[%s@ ⇐@ %a; %a@]" x pp_monad m pp_model_val' v
		      
and pp_monad fmt = function
  | MNew(mv) -> fprintf fmt "@[new@ %a@]" pp_model_val mv
  | MReturn v -> fprintf fmt "@[return@ %a@]" pp_val v
  | MPut (l, v) -> fprintf fmt "@[%s•put@ %a@]" l pp_val v
  | MGet (l) -> fprintf fmt "@[%s•get@]" l
  | MChain (x, m, e) -> fprintf fmt "@[%s@ ←@ %a@ ;@ %a@]" x pp_monad m pp_expr e

let val2str ?max:(n=4) v = 
  Format.pp_set_max_boxes Format.str_formatter n ;
  (pp_val Format.str_formatter v) ;
  Format.flush_str_formatter ()

let mval2str ?max:(n=4) v = 
  Format.pp_set_max_boxes Format.str_formatter n ;
  (pp_model_val Format.str_formatter v) ;
  Format.flush_str_formatter ()

let monad2str ?max:(n=4) v =
  Format.pp_set_max_boxes Format.str_formatter n ;
  (pp_monad Format.str_formatter v) ;
  Format.flush_str_formatter ()

(*
let rec valeq v v' = 
  let res = 
  match v' with
    VConst(c) -> begin match v with VConst(c') -> const_eq c c' | _ -> false end
  | VAbs(s, e) -> begin match v with VAbs(s', e') when s = s' -> equal_expr e e' | _ -> false end
  | VObj(fs) -> begin match v with VObj(fs') -> StrMap.equal valeq fs fs' | _ -> false end
  | VVec (vs) -> begin match v with VVec(vs') -> Array.equal valeq vs vs' | _ -> false end
(*  | VMonad(m) -> begin match v with VMonad(m') -> monadeq m m' | _ -> false end
  | V
 *)
  in   Printf.printf "Value Equality of '%s' and '%s' = %b\n" (val2str v) (val2str v') res ;
       res
 *)

let ident x = {Asttypes.txt = Longident.Lident x ; loc = Location.none}

let rec lift_monad = function 
  | MGet s -> Get s 
  | MReturn v -> Return (lift_value v) 
  | MPut(s,v) -> Put(s, lift_value v) | MChain(x, m, e) -> Bind(x, lift_monad m, e)
		
and lift_value = function
  | VTup(vs) -> Tup(List.map lift_value vs)
  | VConst c   -> Const c 
  | VAbs (x,e) -> Abs(x,e)
  | VVec vs -> Vec (Array.map lift_value vs)
  | VTagged (tag, v) -> Tag(tag, lift_value v)
  | VMonad (m) -> lift_monad m 
  | VHost (_, x) -> Host (Ast_helper.Exp.ident  (ident x))

and lift_model_value_fields = function
  | MEmpty -> []
  | MField(x, m, f) -> Named(x, lift_monad m)::(lift_model_value_fields f)

let lift_model_value f = Model(lift_model_value_fields f)
        
let error_expected op exp got =
  VConst( Err ( Printf.sprintf "in '%s' expected: %s but got: '%s'" op exp got ) )

module StrSet = Set.Make(String)

let ocaml_interpreter = Mcl_ocaml.ocaml_interpreter ()

let rec append_fields fst snd = match fst with
    MEmpty -> snd
  | MField(x,m,f) -> MField(x, m, append_fields f snd)

let prepend x mv f = MField(x, mv, f)

open Result.Infix
let (>>|) r f = r >>= (fun a -> Result.Ok(f a))

let merror_expected op exp got =
  Result.Bad ( Printf.sprintf "in '%s' expected: %s but got: '%s'" op exp got ) 

let rec pass_error e f = match eval e with
  | VConst(Err msg) as err -> err
  | _ as v -> f v

and m_lift_error e = match eval e with
  | VConst(Err msg) -> Result.Bad msg
  | _ as v -> Result.Ok (v)

and eval_array es vs i = if i < (Array.length es) then
			   pass_error es.(i) (fun v -> (vs.(i) <- v ; eval_array es vs (i+1)))
			 else
			   VVec(vs)

and eval_list = function
    e :: r -> pass_error e (fun v -> 
                            match eval_list r with 
                              VTup(vs) -> VTup(v::vs)
                            | VConst(Err(e)) -> VConst(Err(e))
                           )
  | [] -> VTup([])

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

  | Tup (es) -> eval_list es

  | Project(n, e) as p -> pass_error e (fun v -> 
                                        match v with 
                                         | VTup(vs) when List.length vs < n -> error_expected (expr2str e) (Printf.sprintf "an %d-tuple" (List.length vs)) (val2str v)
                                         | VTup(vs) -> List.at vs (n-1) 
                                         | _ -> error_expected (expr2str p) "tuple expression" (val2str v)
                                       )

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
							 eval_host_app x (Ast_helper.Exp.constant (Asttypes.Const_float (Printf.sprintf "%.100e" f)))						 
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
							 error_expected (expr2str e2) ("valid index for '" ^ (expr2str e1) ^ "'") (string_of_int idx)
						      | VConst(Int(idx)) -> vs.(idx)
						      | _ as v -> error_expected (expr2str e2) "int value" (val2str v)
						    )
				   | _ as v -> error_expected (expr2str e1) "vector value" (val2str v)
				 )

  | Length(e) -> pass_error e (function
                                | VVec(vs) -> VConst(Int(Array.length vs))
                                | _ as v -> error_expected (expr2str e) "array value" (val2str v)
                              )

  | Update(e, i, u) ->
     let eval_update2 vs n u = pass_error u (fun v -> 
                                             if n = (Array.length vs) then 
                                               VVec(Array.append vs [|v|])
                                             else
                                               let vs' = Array.copy vs in
                                               vs'.(n) <- v ; VVec(vs') 
                                            )
     in
     let eval_update1 vs i u = pass_error i (function 
                                              | VConst(Int(n)) when n >= 0 && n <= (Array.length vs) -> eval_update2 vs n u
                                              | _ as v -> error_expected (expr2str e) "index value" (val2str v)
                                            )
     in
 
     pass_error e (function
                    | VVec(vs) -> eval_update1 vs i u
                    | _ as v -> error_expected (expr2str e) "array value" (val2str v)
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

  | New (me) -> begin match (meval nomods me) with
                      | Result.Bad(e) -> VConst(Err(e))
                      | Result.Ok(mv) -> VMonad(MNew(mv))
                end

  | _ as exp -> VConst (Err (Printf.sprintf "Don't know how to evaluate '%s'. Confused." (expr2str exp)))

and nomods = StrMap.empty

and meval_fields mods = function
  | [] -> Result.Ok MEmpty

  | Named(x, e)::r -> m_lift_error e >>= (function
                                           | VMonad mv -> (meval_fields mods r) >>| (prepend x mv)
				           | _ as v -> merror_expected (expr2str e) "monad value" (val2str v)
				         )

  | (Unnamed e)::r -> m_lift_error e >>= (function
				           | VMonad mv -> (meval_fields mods r) >>| (prepend "" mv)
				           | _ as v -> merror_expected (expr2str e) "monad value" (val2str v)
				         )

  | Replaceable(x, e)::r when StrMap.mem x mods -> begin 
						   match (StrMap.find x mods) with
						   | VMonad mv -> (meval_fields mods r) >>| (prepend "" mv)
						   | _ as v -> merror_expected ("modification for " ^ x) "monad value" (val2str v)
						 end

  | Replaceable(x,e)::r -> m_lift_error e >>= (function
					        | VMonad mv -> (meval_fields mods r) >>| (prepend x mv)
					        | _ as v -> merror_expected (expr2str e) "monad value" (val2str v)
					      )

  | (Extend m)::r -> (meval mods m) >>= (fun mv -> (meval_fields mods r) >>| (append_fields mv))		                        

and meval mods = function
  | Model(fds) -> meval_fields StrMap.empty fds 

  | MLet (x, m, m') -> meval StrMap.empty m >>= (fun mv ->
                                                 meval mods (m_subst_m x (lift_model_value mv) m') )

  | MState (x, e, m) -> meval mods m >>= (fun mv -> (m_lift_error e >>| (fun v -> MField ("", MPut(x, v), mv))))
  
  | MModify (x, e, m) -> let v = eval e in meval (StrMap.add x v mods) m 
  
  | _ as m -> Result.Bad (Printf.sprintf "Don't know how to evaluate '%s'. Confused." (model2str m))

let write_value ?max:(n=8) output v = BatIO.write_string output (val2str ~max:n v)

let state2str ?max:(n=8) = BatIO.to_string (StrMap.print ~first:"{" ~last:"}" ~sep:";" ~kvsep:" = " BatIO.write_string (write_value ~max:n))

let elab2str ?max:(n=8) (s,v) =  (state2str s) ^ " , " ^ (val2str ~max:n v)

let rec elab s = function
  | MReturn(v) -> (s, v)
  | MGet(l) when StrMap.mem l s -> (s, StrMap.find l s) (* TODO: error handling *)
  | MGet(l) -> (s, VConst(Err("No state '" ^ l ^ "' found.") ))
  | MPut(l, v) -> (StrMap.add l v s, VVec( [| |] ) ) (* TODO: error handling *)
  | MChain(x, m, e) -> 
     begin
     match elab s m with 
     | (s, VConst(Err(e))) -> (s, VConst(Err(e)))
     | (s', v) ->
        begin
          match eval (subst x (lift_value v) e) with
          | VConst(Err msg) -> (s, VConst(Err msg))
          | VMonad(m') -> elab s' m'
          | _ as v -> (s, error_expected (expr2str e) "monadic value" (val2str v))
        end
     end
  | MNew(mv) -> begin match (elab_mv s StrMap.empty mv) with
                | Result.Bad (s', e) -> (s', VConst(Err(e)))
                | Result.Ok (s', fds) -> (s', VObj(fds))
                end

and elab_mv s fds = function
    MField(x, m, mv) -> begin match elab s m with
                              | (s, VConst(Err(e))) -> Result.Bad (s, e)
                              | (s', v) -> (elab_mv s' (StrMap.add x v fds)
                                                    (mv_subst x (lift_value v) mv)
                                           )                                   
                        end
  | MEmpty -> Result.Ok (s, fds)
       

let start_elab e = match (eval e) with 
  | VConst(Err e) -> (StrMap.empty, VConst(Err e))
  | VMonad(m) -> elab StrMap.empty m 
  | _ as v -> (StrMap.empty, error_expected (expr2str e) "monadic value" (val2str v))

open Outcometree

let object_value = function
  | Oval_constr ( Oide_ident "true", [] ) -> VConst (Bool true )
  | Oval_constr ( Oide_ident "false", [] ) -> VConst (Bool false )
  | Oval_float f -> VConst (Float f)
  | Oval_int i -> VConst (Int i)
  | _ -> VConst(Err("cannot translate OCaml non-literal back to mcl"))

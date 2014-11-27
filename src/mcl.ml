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
open Map

(* pattern language, to be expanded *)
type patt = string * (string list)

(* literals *)
type const = 
	  | Float of float
	  | Int of int
	  | Err of string
	  | Bool of bool

and expr = 
  (* Lambda calculus with let (rec) - bindings *)
  | Var of string 
  | Abs of string * expr
  | App of expr * expr
  | Const of const
  | Let of string * expr * expr
  | Letrec of string * expr * expr
				
  (* meta-language (OCaml) *)
  | Host of Parsetree.expression	 
	      
  (* control flow *)
  | Cond of expr * expr * expr
	 
  (* data structures *)
  | Tup of expr list 
  | Select of int * expr
  | Idx of expr * expr
  | Vec of expr array
  | Length of expr
  | Update of expr * expr * expr
  | Case of expr * (patt * expr) list
  | Adt of string * (expr list)
		      
  (* modeling *)
  | New of model_expr
  | Method of string * expr 
  | Get of string | Put of string * expr | Return of expr | Bind of string * expr * expr

(* high level ('object-oriented') modeling *)
and model_expr = Model of model_field list
	       | MLet of string * model_expr * model_expr
	       | MState of string * expr * model_expr
               | MVar of string
               | MModify of string * expr * model_expr

(* model construction *)
and model_field = Named of string * expr
                 | Replaceable of string * expr (* replaceable (by name) fields *)
		 | Unnamed of expr
		 | Extend of model_expr

(* ignore locations for comparison *)
let rec equal_expr e1 = function
  | Host(c2) -> begin match e1 with Host(c1) -> c1 = c2 | _ -> false end
  | Var x -> e1 = Var(x)
  | Abs(x, e) -> begin match e1 with Abs(y, e') when x=y -> equal_expr e e' | _ -> false end
  | App(l, r) -> begin match e1 with App(l', r') -> (equal_expr l l') && (equal_expr r r')  | _ -> false end
  | Const c -> e1 = Const(c)
  | Let(x, e, i) ->  begin match e1 with Let(y, e', i') when x=y -> (equal_expr e e') && (equal_expr i i') | _ -> false end
  | Letrec(x, e, i) ->  begin match e1 with Letrec(y, e', i') when x=y -> (equal_expr e e') && (equal_expr i i') | _ -> false end
  | Cond(c, t, e) ->  begin match e1 with Cond(c', t', e') -> (equal_expr c c') && (equal_expr t t') && (equal_expr e e') | _ -> false end
  | Idx(e, i) -> begin match e1 with Idx(e', i') -> (equal_expr e e') && (equal_expr i i')  | _ -> false end
  | Vec(es) -> begin match e1 with Vec(es') -> Enum.fold2 (fun e e' a -> a && (equal_expr e e')) true (Array.enum es) (Array.enum es') | _ -> false end
  | Case(e, ps) -> begin match e1 with Case(e', ps') -> List.fold_left2 (fun a (p,e) (p',e') -> a && (p = p') && (equal_expr e e')) true ps ps' | _ -> false end 
  | Get(l) -> e1 = Get(l)
  | Put(l, e) -> begin match e1 with Put(l', e') when l = l' -> equal_expr e e' | _ -> false end 
  | Return(e) -> begin match e1 with Return(e') -> equal_expr e e' | _ -> false end 
  | Bind(x, l, r) -> begin match e1 with Bind(y, l', r') when x = y -> (equal_expr l l') && (equal_expr r r') | _ -> false end 
  | Adt(a, es) -> begin match e1 with Adt(a', es') when a = a' -> List.fold_left2 (fun a e e' -> a && (equal_expr e e')) true es es' | _ -> false end    
  | New m -> begin match e1 with New(m') -> equal_model_expr m m' | _ -> false end
  | Method(x, e) -> begin match e1 with Method(y,e') when x = y -> equal_expr e e' | _ -> false end 

and equal_model_field f = function
  | Extend m -> begin match f with Extend m' -> equal_model_expr m m' | _ -> false end
  | Named(x, e) -> begin match f with Named(y, e') when x = y -> equal_expr e e' | _ -> false end
  | Replaceable(x, e) -> begin match f with Replaceable(y, e') when x = y -> equal_expr e e' | _ -> false end
  | Unnamed(e) -> begin match f with Unnamed(e') -> equal_expr e e' | _ -> false end 		 

and equal_model_expr m = function
  | Model(fds) -> begin match m with Model(fds') -> Enum.fold2 (fun f f' a -> a && (equal_model_field f f')) true (List.enum fds) (List.enum fds') | _ -> false end
  | MVar(x) -> begin match m with MVar(y) -> x = y | _ -> false end
  | MLet(x, a, b) -> begin match m with MLet(y, a', b') when x = y -> (equal_model_expr a a') && (equal_model_expr b b') | _ -> false end
  | MState(x, a, b) -> begin match m with MState(y, a', b') when x = y -> (equal_expr a a') && (equal_model_expr b b') | _ -> false end
  | MModify(x, a, b) -> begin match m with MModify(y, a', b') when x = y -> (equal_expr a a') && (equal_model_expr b b') | _ -> false end
 
let rec subst x v = function
  | Var y when x = y -> v
  | Var y -> Var y
  | Abs(y,e) when x = y -> Abs(y, e)
  | Abs(y,e) -> Abs(y, subst x v e)
  | App(e1,e2) -> App(subst x v e1, subst x v e2)
  | Const c -> Const c
  | Let(y, e1, e2) when x = y -> Let(y, e1, e2)
  | Let(y, e1, e2) -> Let(y, subst x v e1, subst x v e2)
  | Letrec(y, e1, e2) when x = y -> Letrec(y, e1, e2)
  | Letrec(y, e1, e2) -> Letrec(y, subst x v e1, subst x v e2)
  | Cond(c, t, e) -> Cond(subst x v c, subst x v t, subst x v e)
  | New m -> New (m_subst_e x v m)
  | Idx(e1, e2) -> Idx(subst x v e1, subst x v e2)
  | Vec(es) -> Vec( Array.map (subst x v) es )
  | Case(e, ps) -> Case(subst x v e, List.map (pat_subst x v) ps)
  | Get(l) -> Get(l)
  | Put(l, e) -> Put(l, subst x v e)
  | Return(e) -> Return(subst x v e)
  | Bind(y, e1, e2) when x = y -> Bind(y, e1, e2)
  | Bind(y, e1, e2) -> Bind(y, subst x v e1, subst x v e2)
  | Adt(a, es) -> Adt(a, List.map (subst x v) es)
  | Host e -> Host e

and subst_m x sm = function
  | Var y -> Var y
  | Abs(y,e) when x = y -> Abs(y, e)
  | Abs(y,e) -> Abs(y, subst_m x sm e)
  | App(e1,e2) -> App(subst_m x sm e1, subst_m x sm e2)
  | Const c -> Const c
  | Let(y, e1, e2) when x = y -> Let(y, e1, e2)
  | Let(y, e1, e2) -> Let(y, subst_m x sm e1, subst_m x sm e2)
  | Letrec(y, e1, e2) when x = y -> Letrec(y, e1, e2)
  | Letrec(y, e1, e2) -> Letrec(y, subst_m x sm e1, subst_m x sm e2)
  | Cond(c, t, e) -> Cond(subst_m x sm c, subst_m x sm t, subst_m x sm e)
  | New m -> New (m_subst_m x sm m)
  | Idx(e1, e2) -> Idx(subst_m x sm e1, subst_m x sm e2)
  | Vec(es) -> Vec( Array.map (subst_m x sm) es )
  | Case(e, ps) -> Case(subst_m x sm e, List.map (pat_subst_m x sm) ps)
  | Get(l) -> Get(l)
  | Put(l, e) -> Put(l, subst_m x sm e)
  | Return(e) -> Return(subst_m x sm e)
  | Bind(y, e1, e2) when x = y -> Bind(y, e1, e2)
  | Bind(y, e1, e2) -> Bind(y, subst_m x sm e1, subst_m x sm e2)
  | Adt(a, es) -> Adt(a, List.map (subst_m x sm) es)
  | Host e -> Host e

and m_subst_e x v = function
  | MVar(y) -> MVar(y)
  | MLet(y, m, m') when x = y -> MLet(y,m,m')
  | MLet(y, m, m') -> MLet(y,m_subst_e x v m , m_subst_e x v m')
  | MState(s, e, m) -> MState(s, subst x v e , m_subst_e x v m)
  | Model(fds) -> Model(fds_subst_e x v fds)
  | MModify(x, e, m) -> MModify(x, subst x v e, m_subst_e x v m)

and fds_subst_e x v = function
  | (Extend m) :: r -> Extend (m_subst_e x v m) :: (fds_subst_e x v r)
  | Named(y,e) :: r when y = x -> Named(y,subst x v e)::r
  | Named(y,e) :: r -> Named(y, subst x v e)::(fds_subst_e x v r)
  | Unnamed(e) :: r -> Unnamed(subst x v e)::(fds_subst_e x v r)
  | Replaceable(y,e) :: r when y = x -> Replaceable(y,subst x v e)::r
  | Replaceable(y,e) :: r -> Replaceable(y, subst x v e)::(fds_subst_e x v r)
  | [] -> []

and fds_subst_m x sm = function
  | (Extend m) :: r -> Extend (m_subst_m x sm m) :: (fds_subst_m x sm r)
  | Named(y,e) :: r when y = x -> Named(y,subst_m x sm e)::r
  | Named(y,e) :: r -> Named(y, subst_m x sm e)::(fds_subst_m x sm r)
  | Unnamed(e) :: r -> Unnamed(subst_m x sm e)::(fds_subst_m x sm r)
  | Replaceable(y,e) :: r when y = x -> Replaceable(y,subst_m x sm e)::r
  | Replaceable(y,e) :: r -> Replaceable(y, subst_m x sm e)::(fds_subst_m x sm r)
  | [] -> []

and m_subst_m x sm = function
    MVar(y) when x = y -> sm
  | MVar(y) -> MVar(y)
  | MLet(y, m, m') when x = y -> MLet(y,m,m')
  | MLet(y, m, m') -> MLet(y,m_subst_m x sm m , m_subst_m x sm m')
  | MState(s, e, m) -> MState(s, subst_m x sm e , m_subst_m x sm m)
  | Model(fds) -> Model(fds_subst_m x sm fds)
  | MModify(x, e, m) -> MModify(x, subst_m x sm e, m_subst_m x sm m)
			       
and pat_subst x v ((const, vars), e) = 
  if (List.mem x vars) then 
    ((const, vars), e)
  else
    ((const, vars), subst x v e)

and pat_subst_m x v ((const, vars), e) = 
  if (List.mem x vars) then 
    ((const, vars), e)
  else
    ((const, vars), subst_m x v e)

(*
let rec freplaceables env fds = function
  | Named (x, e)::r -> freplaceables env fds r
  | Replaceable(x, e)::r -> freplaceables env ((x,e)::fds) r
  | (Unnamed e) :: r -> freplaceables env fds r
  | (Extend m) :: r -> freplaceables (replaceables env fds m) r

and replaceables env rs = function
  | Model (mfds) -> freplaceables rs mfds
  | MLet (x, m, m') -> replaceables (StrMap.add x (replaceables m env []) env) rs m'
  | MName (x) -> StrMap.mem x env
  | Modify(_,_,m) -> replaceables env rs m
 *)	      

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

type patt = string * (string list)

type const = 
	  | Float of float
	  | Int of int
	  | Err of string
	  | Bool of bool

and expr = Var of string 
	 | Abs of string * expr
	 | App of expr * expr
	 | Const of const
	 | Host of Parsetree.expression
	 | Let of string * expr * expr
	 | Letrec of string * expr * expr
	 | Cond of expr * expr * expr
	 (* | New of expr *)
	 | Idx of expr * expr
	 | Vec of expr array
	 | Case of expr * (patt * expr) list
	 | Adt of string * (expr list)
	 | Get of string | Put of string * expr | Return of expr | Bind of string * expr * expr

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
  (* | New e -> New (subst x v e) *)
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

and pat_subst x v ((const, vars), e) = 
  if (List.mem x vars) then 
    ((const, vars), e)
  else
    ((const, vars), subst x v e)
	      

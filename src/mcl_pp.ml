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
open Format
open Mcl

let rec pp_list ?(sep="") pp_element fmt = function
  | [h] -> Format.fprintf fmt "%a" pp_element h
  | h::t ->
    Format.fprintf fmt "%a%s@,%a"
      pp_element h sep (pp_list ~sep pp_element) t
  | [] -> ()

let rec pp_enum ?(sep="") pp_element fmt enum = match (Enum.get enum) with
  | Some h -> Format.fprintf fmt "%a" pp_element h ; 
	      begin match (Enum.peek enum) with
		    | None -> ()
		    | Some(h) -> Format.fprintf fmt "%s@,%a" sep (pp_enum ~sep pp_element) enum
	      end
  | None -> ()

let rec pp_const fmt = function
  | Float f -> pp_print_float fmt f
  | Int i -> pp_print_int fmt i
  | Bool b -> pp_print_bool fmt b
  | Err msg -> fprintf fmt "error: '%s'" msg 

and pp_expr fmt = function
  | Host e -> fprintf fmt "⟪@[%a@]⟫" (Printast.expression 10) e
  | Var x -> fprintf fmt "@[%s@]" x
  | Abs(x, e) -> fprintf fmt "@[(λ%s.%a)@]" x pp_expr e
  | App(e1, e2) -> fprintf fmt "@[(%a@ %a)@]" pp_expr e1 pp_expr e2
  | Const c -> fprintf fmt "@[%a@]" pp_const c
  | Let(x, e1, e2) -> fprintf fmt "@[let@ %s@ =@ %a@ in@ %a@]" x pp_expr e1 pp_expr e2
  | Letrec(x, e1, e2) -> fprintf fmt "@[let@ rec@ %s@ =@ %a@ in@ %a@]" x pp_expr e1 pp_expr e2
  | Cond(c, t, e) -> fprintf fmt "@[if@ %a@ then@ %a@ else@ %a @]" pp_expr c pp_expr t pp_expr e
  | New(m) -> fprintf fmt "@[(new@ %a)@]" pp_model m 
  | Idx(e1, e2) -> fprintf fmt "@[%a[%a]@]" pp_expr e1 pp_expr e2 
  | Vec(es) -> fprintf fmt "@[⟦%a⟧@]" (pp_list ~sep:";" pp_expr) (Array.to_list es)
  | Case(e, tes) -> fprintf fmt "@[(case@ %a@ of@ %a)@]" pp_expr e (pp_enum ~sep:"|" pp_pat) (TagMap.enum tes)
  | Get(l) -> fprintf fmt "@[%s•get@]" l
  | Put(l, e) -> fprintf fmt "@[%s•put@ %a@]" l pp_expr e
  | Return(e) -> fprintf fmt "@[return@ %a@]" pp_expr e
  | Bind(x, e1, e2) -> fprintf fmt "@[%s@ ←@ %a@ ;@ %a@]" x pp_expr e1 pp_expr e2
  | Length(e) -> fprintf fmt "@[#(%a)@]" pp_expr e
  | Update(a,i,e) -> fprintf fmt "@[⟦%a@ with@ %a@ =@ %a⟧@]" pp_expr a pp_expr i pp_expr e
  | Project(n, e) -> fprintf fmt "@[(%a.%d)@]" pp_expr e n
  | Tup(es) -> fprintf fmt "@[%a@]" (pp_list ~sep:", " pp_expr) es
                              
and pp_fd fmt = function
  | Extend m -> fprintf fmt "@[extend %a@]" pp_model m
  | Replaceable(x, e) -> fprintf fmt "@[replaceable@ %s@ ⇐@ %a@]" x pp_expr e
  | Named(x, e) -> fprintf fmt "@[%s@ ⇐@ %a@]" x pp_expr e
  | Unnamed(e) -> fprintf fmt "@[%a@]" pp_expr e
			  
and pp_model fmt = function
  | Model(fds) -> fprintf fmt "@[{%a}@]" (pp_list ~sep:";" pp_fd) fds
  | MLet (x, m, m') -> fprintf fmt "@[model@ %s@ =@ %a@ in@ %a]" x pp_model m pp_model m'
  | MState (x, e, m) -> fprintf fmt "@[state@ %s@ =@ %a@ in@ %a]" x pp_expr e pp_model m
  | MModify (x, e, m) -> fprintf fmt "@[replace@ %s@ with@ %a@ in@ %a]" x pp_expr e pp_model m
  | MVar x -> fprintf fmt "@[%s@]" x

and pp_pat fmt (a, e) = 
  fprintf fmt "@[%s →@ %a@]" a pp_expr e

let expr2str ?max:(n=8) e = 
  pp_set_max_boxes str_formatter n ;
  (pp_expr str_formatter e) ;
  flush_str_formatter ()

let model2str ?max:(n=8) m = 
  pp_set_max_boxes str_formatter n ;
  (pp_model str_formatter m) ;
  flush_str_formatter ()


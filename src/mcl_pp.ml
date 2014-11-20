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

open Format
open Mcl

let rec pp_list ?(sep="") pp_element fmt = function
  | [h] -> Format.fprintf fmt "%a" pp_element h
  | h::t ->
    Format.fprintf fmt "%a%s@,%a"
      pp_element h sep (pp_list ~sep pp_element) t
  | [] -> ()

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
  (* | New(e) -> fprintf fmt "@[(new@ %a)@]" pp_expr e  *)
  | Idx(e1, e2) -> fprintf fmt "@[%a[%a]@]" pp_expr e1 pp_expr e2 
  | Vec(es) -> fprintf fmt "@[⟦%a⟧@]" (pp_list ~sep:";" pp_expr) (Array.to_list es)
  | Case(e, ps) -> fprintf fmt "@[match@ %a@ with@ %a@]" pp_expr e (pp_list pp_pat) ps
  | Get(l) -> fprintf fmt "@[%s•get@]" l
  | Put(l, e) -> fprintf fmt "@[%s•put@ %a@]" l pp_expr e
  | Return(e) -> fprintf fmt "@[return@ %a@]" pp_expr e
  | Bind(x, e1, e2) -> fprintf fmt "@[%s@ ←@ %a@ ;@ %a]" x pp_expr e1 pp_expr e2
  | Adt(a, es) -> fprintf fmt "@[%s⟨%a⟩@]" a (pp_list ~sep:";" pp_expr) es

and pp_pat fmt ((a, xs), e) = 
  fprintf fmt "@[|@ [@%s⟨%a⟩@]@ →@ %a@]" a (pp_list pp_print_string) xs pp_expr e


let expr2str e = 
  (pp_expr Format.str_formatter e) ;
  Format.flush_str_formatter ()


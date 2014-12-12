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
open Mcl_parser
open Mcl
open Mcl_lexer
open Mcl_pp
open Mcl_ocaml

let default_state = StrMap.add "equations" (Vec [||]) (StrMap.add "states" (Vec [||]) StrMap.empty )
                                    
let _ = let s = IO.read_all IO.stdin in
        try
          let ucs = state_from_utf8_string s in
          let next () = next_token ucs in
          let last () = last_token ucs in
          let mcl_expr = expr_parser "stdin" next last in
          let ocaml_expr = mclc_prefix (mclc empty_class_env mcl_expr) in          
          Printf.printf "let model =\n%s" (Pprintast.string_of_expression ocaml_expr) ;
          Printf.printf "let state =\n%s" (Pprintast.string_of_expression (statec default_state)) ;
        with 
          SyntaxError e -> Printf.printf "Syntax Error at %s:\n%s" (show_syntax_error e) (error_message e s)


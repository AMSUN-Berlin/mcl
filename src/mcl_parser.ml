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
open Mcl_lexer

let get_token {token} = token 

let get_start src {cursor} = {Lexing.pos_fname = src ;
			      Lexing.pos_lnum = cursor.line ;
			      Lexing.pos_bol = cursor.bol ;
			      Lexing.pos_cnum = cursor.char;
			     }

let get_end src {cursor ; size} = {Lexing.pos_fname = src ;
				   Lexing.pos_lnum = cursor.line ;
				   Lexing.pos_bol = cursor.bol ;
				   Lexing.pos_cnum = cursor.char + size;
				  }

exception SyntaxError of string

let guard parser next locate = try parser next  
                             with
                               Mcl_gen_parser.Error -> raise ( SyntaxError ( locate () ) )

let expr_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Mcl_gen_parser.sole_expr)


let model_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Mcl_gen_parser.main )


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

open Mcl_gen_parser

let name_of_token = function
    EQ -> "EQ" 
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | LANGLE -> "LANGLE"
  | RANGLE -> "RANGLE"
  | LAMBDA -> "LAMBDA"
  | BULLET -> "BULLET"
  | DOT -> "DOT"
  | PLUS -> "PLUS"
  | MINUS -> "MINUS"
  | TIMES -> "TIMES"
  | DIV -> "DIV"
  | SEMICOLON -> "SEMICOLON"
  | COMMA -> "COMMA"
  | THEN -> "THEN"
  | IF -> "IF"
  | ELSE -> "ELSE"	      
  | LET -> "LET"
  | REC -> "REC"
  (*| NEW -> "NEW"*)
  | IN -> "IN"
  | LEFTARROW -> "LEFTARROW"
  | RBRACKET -> "RBRACKET"
  | RDBRACKET -> "RDBRACKET"
  | LBRACKET -> "LBRACKET"
  | LDBRACKET -> "LDBRACKET"
  | EOF -> "EOF"
  | HOST x -> Printf.sprintf "HOST (%s)" x 
  | IDENT x -> Printf.sprintf "IDENT (%s)" x 
  | FLOAT f -> Printf.sprintf "FLOAT %f" f 
  | INT i -> Printf.sprintf "INT %d" i 
  | GET -> "GET"
  | PUT -> "PUT"
  | RETURN -> "RETURN"
  | GT -> "GT"
  | LT -> "LT"
  | GEQ -> "GEQ"
  | LEQ -> "LEQ"
  | NEQ -> "NEQ"

type cursor = { 
  line : int;
  char : int;
  bol : int;
}

type tokplus = {
  token : token;
  src : string;
  size : int;
  cursor : cursor;
}

type m_cursor = {
  mutable m_line : int;
  mutable m_bol : int;
}

open Sedlexing

type lexer_state = {
  src : string ;
  buf : lexbuf;
  m_cursor : m_cursor ;
}

let digit = [%sedlex.regexp? '0'..'9']
let number = [%sedlex.regexp? Plus digit]
let letter = [%sedlex.regexp? 'a'..'z'|'A'..'Z']

let state_from_utf8_string input = {
  buf = Utf8.from_string input ;
  src = "test input" ; 
  m_cursor = { m_line = 0; m_bol = 0 } }

let next_token { src ; buf ; m_cursor } =
  let lift token = { token ; src ; size = lexeme_length buf; cursor = 
							       { line = m_cursor.m_line ; 
								 bol = m_cursor.m_bol ; 
								 char = lexeme_start buf ;
							       } 
		   } in

  let current _ = Utf8.lexeme buf in

  match%sedlex buf with
  | number -> lift ( INT ( int_of_string (current () ) ))
    | _ -> failwith "Unexpected character"

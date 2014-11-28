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

open OUnit
open Mcl_parser
open Mcl
open Mcl_lexer
open Mcl_pp
open Mcl_dynamics

let explicit_linear_ode_modeling = "

  let prepare = void ← states•put ⟦⟧ ; 
                equations•put ⟦⟧
  in

  (* states are simply numbered *)                           
  let new_state = xs ← states•get ; 
                  let j = #xs in
                  void ← states•put ⟦xs with j = 0.0⟧ ;                                    
                  return j
  in
  
  (* linear equations ft*time + fs[i].2 * x[fs[i].1] + c = dx_j *)
  let add_equation ft fs c j = eqs ← equations•get ;                               
                               let eqs' = ⟦eqs append (ft, fs, c, j)⟧ in
                               derivatives•put eqs' 
  in

  let eval_equation t xs eq = 
    let rec eval_xs n = if n > #eq.2 then 0.0 else 
                        xs[eq.2 .1] *. eq.2 .2 +. (eval_xs (n + 1))
    in 
    t *. eq.1 +. (eval_xs 0) +. eq.3  
  in

  (* simple fixed-step forward-euler *)
  let rec appl_step eqs dt t n xs = if n > #eqs then 
                                      xs 
                                    else
                                      let eq = eqs[n] in

                                      (* update state variable j by equation n *)
                                      let dxj = eval_equation t xs eq in
                                      let xs' = ⟦xs with j = xs[j] +. (dt *. dxj)⟧ in

                                      appl_step eqs dt t (n+1) xs'
  in
                                    
  let step t dt = eqs ← equations•get ;
                  xs ← states•get ;

                  let t' = t +. dt in
                  let xs' = appl_step ds dt t' 0 xs in
                  void ← states•put xs ;
                  return t'
  in

  let rec sim t stop = if t >= stop then 
                         states•get                                   
                       else 
                         t' ← step t 0.01 ;
                         sim t' stop 
  in
" 

type complex_test_case = {
  name : string ;
  input : string ;           
  expected_state : value StrMap.t ;
  expected_value : value;
}

let new_state = { name = "new state" ;
                  expected_state =  StrMap.add "equations" (VVec [||]) 
                                               (StrMap.add "states" (VVec [|VConst(Float(42.0))|]) StrMap.empty);
                  expected_value = VConst(Int(0));
                  input = explicit_linear_ode_modeling ^                            
                            "void  ← prepare ; h ← new_state ; xs ← states•get ; void ← states•put ⟦xs with h = 42.0⟧ ; return h"}

let free_fall = { name = "free fall" ; 
                  expected_state = StrMap.empty;
                  expected_value = VConst(Float(10.)) ;
                  input =
                    explicit_linear_ode_modeling ^ 
    "
     h ← new_state ;
     v ← new_state ;
     xs ← states•get ;
     void ← states•put ⟦xs with h = 10.0⟧ ;
     (* dv = -9.81 *) 
     _ ← add_equation 0.0 ⟦⟧ -9.81 v ;
     
     (* dh = v *)
     _ ← add_equation 0.0 ⟦(v, 1.0)⟧ 0.0 v ;

     (* simulate for 10 seconds *)
     sim 0.0 10.0 
    " ;
                }

let parse {name ; input} = 
  (Printf.sprintf "Test parsing '%s'" name) >:: 
    Parser_tests.expr_test input (fun e -> ignore e)

let elaborate {name ; input ; expected_state; expected_value} = 
  (Printf.sprintf "Test elaborating '%s'" name) >:: 
    Parser_tests.expr_test input (fun e -> assert_equal ~msg:"equality of elaboration" ~printer:elab2str (expected_state,expected_value) (start_elab e))
                                 

let test_cases = [ 
  elaborate new_state ;
  (* elaborate free_fall ; *)
]

let suite = "Complex Test Cases" >::: test_cases

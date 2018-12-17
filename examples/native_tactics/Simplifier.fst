(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Simplifier

open FStar.ST
open FStar.Tactics
open FStar.Tactics.Simplifier

let goal_is_true () : Tac unit =
    let g = cur_goal () in
    match term_as_formula g with
    | True_ -> trivial ()
    | _ -> fail "not syntactically true"

[@plugin]
let test_simplify () : Tac unit =
    simplify ();
    or_else goal_is_true (fun () -> dump ""; fail "simplify left open goals")

[@plugin]
let simplify_c () : Tac unit = simplify (); admit_all()

let test1 (r: ref int) =
  (r := 0;
   r := 1;
   r := 2;
   r := 3)
  <: St unit by simplify_c ()

let test2 (r: ref int) =
  (r := 0;
   r := 1;
   r := 2;
   r := 3;
   r := 4;
   r := 5;
   r := 6;
   r := 7;
   r := 8;
   r := 9;
   r := 10)
  <: St unit by simplify_c ()

// let _ = assert_by_tactic (True /\ True)
//                          test_simplify
// let _ = assert_by_tactic (True \/ True)
//                          test_simplify
// let _ = assert_by_tactic (True \/ False)
//                          test_simplify
// let _ = assert_by_tactic (False \/ True)
//                          test_simplify

// let _ = assert_by_tactic (False \/ (True /\ True))
//                          test_simplify
// let _ = assert_by_tactic ((True /\ False) \/ (True /\ True))
//                          test_simplify
// let _ = assert_by_tactic (False \/ ((True /\ False) \/ (True /\ True)))
//                          test_simplify

// let _ = assert_by_tactic (False ==> True)
//                          test_simplify
// let _ = assert_by_tactic (False ==> False)
//                          test_simplify
// let _ = assert_by_tactic (True ==> True)
//                          test_simplify

// let _ = assert_by_tactic ((False ==> False) ==> True)
//                          test_simplify
// let _ = assert_by_tactic (False ==> (False ==> False))
//                          test_simplify
// let _ = assert_by_tactic ((False ==> False) ==> (True ==> True))
//                          test_simplify
// let _ = assert_by_tactic ((True ==> True) ==> (False ==> False))
//                          test_simplify

// let _ = assert_by_tactic (~False)
//                          test_simplify
// let _ = assert_by_tactic (~(~True))
//                          test_simplify

// let _ = assert_by_tactic (forall (x:int). True)
//                          test_simplify
// let _ = assert_by_tactic (forall (x:int). ((True ==> True) ==> (False ==> False)))
//                          test_simplify

// let _ = assert_by_tactic ((exists (x:int). False) ==> False)
//                          test_simplify
// let _ = assert_by_tactic (~(exists (x:int). False))
//                          test_simplify
// let _ = assert_by_tactic (~(exists (x:int). ((True ==> True) ==> (True ==> False))))
//                          test_simplify

// let _ = assert_by_tactic (False <==> False)
//                          test_simplify
// let _ = assert_by_tactic ((False <==> False) <==> True)
//                          test_simplify
let _ = assert_by_tactic (False <==> (False <==> True))
                         test_simplify

let _ = assert_by_tactic ((exists (x:int). True) <==> True)
                         test_simplify
let _ = assert_by_tactic ((forall (x:int). False) <==> False)
                         test_simplify

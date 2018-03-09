module CanonMonoid

open FStar.Algebra.Monoid
open FStar.List
open FStar.Tactics
open FStar.Reflection

(* "A Monoid Expression Simplifier" ported from
   http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html *)

type exp (a:Type) : Type =
  | Unit : exp a
  | Var : a -> exp a
  | Mult : exp a -> exp a -> exp a

let rec exp_to_string (#a:Type) (a_to_string:a->string) (e:exp a) =
  match e with
  | Unit -> "Unit"
  | Var x -> "Var " ^ a_to_string x
  | Mult e1 e2 -> "Mult (" ^ exp_to_string a_to_string e1
                   ^ ") (" ^ exp_to_string a_to_string e2 ^ ")"

let rec mdenote (#a:Type) (m:monoid a) (e:exp a) : a =
  match e with
  | Unit -> Monoid?.unit m
  | Var x -> x
  | Mult e1 e2 -> Monoid?.mult m (mdenote m e1) (mdenote m e2)

let rec mldenote (#a:Type) (m:monoid a) (xs:list a) : a =
  match xs with
  | [] -> Monoid?.unit m
  | [x] -> x
  | x::xs' -> Monoid?.mult m x (mldenote m xs')

let rec flatten (#a:Type) (e:exp a) : list a =
  match e with
  | Unit -> []
  | Var x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

(* This proof internally uses the monoid laws; the SMT solver picks up
   on them because they are written as squashed formulas in the
   definition of monoid; need to be careful with this since these are
   quantified formulas without any patterns. Dangerous stuff! *)
let rec flatten_correct_aux (#a:Type) (m:monoid a) ml1 ml2 :
  Lemma (mldenote m (ml1 @ ml2) == Monoid?.mult m (mldenote m ml1)
                                                  (mldenote m ml2)) =
  match ml1 with
  | [] -> ()
  | e::es1' -> flatten_correct_aux m es1' ml2

let rec flatten_correct (#a:Type) (m:monoid a) (e:exp a) :
    Lemma (mdenote m e == mldenote m (flatten e)) =
  match e with
  | Unit | Var _ -> ()
  | Mult e1 e2 -> flatten_correct_aux m (flatten e1) (flatten e2);
                  flatten_correct m e1; flatten_correct m e2

let monoid_reflect (#a:Type) (m:monoid a) (e1 e2:exp a)
    (_ : squash (mldenote m (flatten e1) == mldenote m (flatten e2)))
    : squash (mdenote m e1 == mdenote m e2) =
  flatten_correct m e1; flatten_correct m e2

// This expects that mult, unit, and me have already been normalized
let rec reification_aux (#a:Type) (mult unit me : term) : Tac (exp a) =
  let hd, tl = collect_app_ref me in
  // Admitting this subtyping on lists for now, it's provable, but tedious right now
  let tl : list ((a:term{a << me}) * aqualv) = admit(); tl in
  match inspect hd, tl with
  | Tv_FVar fv, [(me1, Q_Explicit) ; (me2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then Mult (reification_aux mult unit me1) (reification_aux mult unit me2)
    else Var (unquote me)
  | _, _ ->
    if term_eq me unit
    then Unit
    else Var (unquote me)

let reification (#a:Type) (m:monoid a) (me:term) : Tac (exp a) =
    let mult = norm_term [delta] (quote (Monoid?.mult m)) in
    let unit = norm_term [delta] (quote (Monoid?.unit m)) in
    let me   = norm_term [delta] me in
    dump ("mult = " ^ term_to_string mult ^
        "; unit = " ^ term_to_string unit ^
        "; me   = " ^ term_to_string me);
    reification_aux mult unit me

private val conv : #x:Type -> #y:Type -> squash (y == x) -> x -> y
private let conv #x #y eq w = w

let change t1 =
    focus (fun () ->
        let t = mk_app (`conv) [(t1, Q_Implicit)] in
        apply t;
        norm [delta;primops;zeta];
        trefl ()
    )

let change_sq t1 =
    change (mk_e_app (`squash) [t1])

let g f = assert_by_tactic (f (3 + 5) > 0)
             (fun () -> change_sq (quote (f 8 > 0)); admit1())

assume val f:int->int
let _ = assert_by_tactic (f (3 + 5) > 0)
             (fun () -> change_sq (`(f 8 > 0)); admit1())

let canon_monoid (#a:Type) (m:monoid a) (*a_to_string:a->string*) : Tac unit =
  norm [];
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq (Some t)) me1 me2 ->
      if term_eq t (quote a) then
        let r1 = reification m me1 in
        let r2 = reification m me2 in
        // this one causes a "Tactic gets stuck!" error
        // dump ("r1=" ^ exp_to_string a_to_string r1 ^
        //     "; r2=" ^ exp_to_string a_to_string r2);
        change_sq (quote (mdenote m r1 == mdenote m r2));
        apply (`monoid_reflect);
        norm [delta_only ["CanonMonoid.mldenote";
                          "CanonMonoid.flatten";
                          "FStar.List.Tot.Base.op_At";
                          "FStar.List.Tot.Base.append"]]; dump "done"
      else fail "Goal should be an equality at the right monoid type"
  | _ -> fail "Goal should be an equality"

let lem0 (a b c d : int) =
  assert_by_tactic (0 + a + b + c + d == (0 + a) + (b + c) + d)
  (fun _ -> canon_monoid int_plus_monoid (* string_of_int *); trefl())

(* TODO: should extend this to a commutative monoid and
         sort the list to prove things like a + b = b + a;
         - even better, the user can provide the ordering *)

(* TODO: would be nice to just find all terms of monoid type in the
         goal and replace them with their canonicalization;
         basically use flatten_correct instead of monoid_reflect
         - even better, the user would have control over the place(s)
           where the canonicalization is done *)

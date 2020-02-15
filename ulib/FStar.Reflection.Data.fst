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
module FStar.Reflection.Data

open FStar.Reflection.Types

noeq
type vconst =
  | C_Unit      : vconst
  | C_Int       : int -> vconst // Not exposing the full details of our integer repr.
  | C_True      : vconst
  | C_False     : vconst
  | C_String    : string -> vconst
  | C_Range     : range -> vconst
  | C_Reify     : vconst
  | C_Reflect   : name -> vconst
  (* TODO: complete *)

// This is shadowing `pattern` from Prims (for smt_pats)
noeq
type pattern =
    | Pat_Constant : vconst -> pattern              // A built-in constant
    | Pat_Cons     : fv -> list pattern -> pattern  // A fully applied constructor
    | Pat_Var      : bv -> pattern                  // Pattern bound variable
    | Pat_Wild     : bv -> pattern                  // Wildcard (GM: why is this not Pat_var too?)
    | Pat_Dot_Term : bv -> term -> pattern          // Dot pattern: resolved by other elements in the pattern and type

type branch = pattern * term  // | pattern -> term

noeq
type aqualv =
    | Q_Implicit
    | Q_Explicit
    | Q_Meta of term

type argv = term * aqualv

noeq
type bv_view = {
    bv_ppname : string;
    bv_index : int;
    bv_sort : typ;
}

noeq
type term_view =
  | Tv_Var    : v:bv -> term_view
  | Tv_BVar   : v:bv -> term_view
  | Tv_FVar   : v:fv -> term_view
  | Tv_App    : hd:term -> a:argv -> term_view
  | Tv_Abs    : bv:binder -> body:term -> term_view
  | Tv_Arrow  : bv:binder -> c:comp -> term_view
  | Tv_Type   : unit -> term_view
  | Tv_Refine : bv:bv -> ref:term -> term_view
  | Tv_Const  : vconst -> term_view
  | Tv_Uvar   : int -> ctx_uvar_and_subst -> term_view
  | Tv_Let    : recf:bool -> bv:bv -> def:term -> body:term -> term_view
  | Tv_Match  : scrutinee:term -> brs:(list branch) -> term_view
  | Tv_AscribedT : e:term -> t:term -> tac:option term -> term_view
  | Tv_AscribedC : e:term -> c:comp -> tac:option term -> term_view  
  | Tv_Unknown  : term_view // Baked in "None"

// Very basic for now
noeq
type comp_view =
  | C_Total     : ret:typ -> decr:(option term) -> comp_view
  | C_Lemma     : term -> term -> term -> comp_view // pre & post
  | C_Unknown   : comp_view


(* *almost* copy/pasted types (from FStar.Syntax.Syntax.fs)  *)
type tscheme_view = list univ_name * typ
noeq
type action_view = {
    av_action_name:name;
    // action_unqualified_name: ident; // necessary for effect redefinitions, this name shall not contain the name of the effect
    // action_univs:univ_names;
    av_action_params: list binder;
    av_action_defn:term;
    av_action_typ: typ
}
noeq
type eff_decl_view = {
    // cattributes :list<cflag>;
    efv_mname       :name;
    // univs       :univ_names;
    efv_binders     :list binder;
    efv_signature   :term;
    efv_ret_wp      :tscheme_view;
    efv_bind_wp     :tscheme_view;
    efv_if_then_else:tscheme_view;
    efv_ite_wp      :tscheme_view;
    efv_stronger    :tscheme_view;
    efv_close_wp    :tscheme_view;
    efv_assert_p    :tscheme_view;
    efv_assume_p    :tscheme_view;
    efv_null_wp     :tscheme_view;
    efv_trivial     :tscheme_view;
    //NEW FIELDS
    //representation of the effect as pure type
    efv_repr        :term;
    //operations on the representation
    efv_return_repr :tscheme_view;
    efv_bind_repr   :tscheme_view;
    //actions for the effect
    // actions     :list<action>;
    // eff_attrs   :list<attribute>;
}
noeq
type sub_eff_view = {
  sev_source: name;
  sev_target: name;
  sev_lift_wp: option tscheme_view;
  sev_lift: option tscheme_view
}


// type sigelt_view =
//     | Sg_Let of bool * fv * list<univ_name> * typ * term
//     | Sg_Inductive of name * list<univ_name> * list<binder> * typ * list<name> // name, params, type, constructors
//     | Sg_Constructor of name * typ
//     | Unk


noeq
type sigelt_view =
  | Sg_Let :
      (r:bool) ->
      (fv:fv) ->
      (us:list univ_name) ->
      (typ:typ) ->
      (def:term) ->
      sigelt_view

  // Sg_Inductive basically coallesces the Sig_bundle used internally,
  // where the type definition and its constructors are split.
  // While that might be better for typechecking, this is probably better for metaprogrammers
  // (no mutually defined types for now)
  | Sg_Inductive :
      (nm:name) ->              // name of the inductive type being defined
      (univs:list univ_name) -> // universe variables
      (params:binders) ->       // parameters
      (typ:typ) ->              // the type annotation for the inductive, i.e., indices -> Type #u
      (cts:list name) ->        // constructor names
      sigelt_view

  | Sg_Constructor :
      (name:name) ->
      (typ:typ) ->
      sigelt_view

  | Sg_new_effect : eff_decl_view -> sigelt_view
  | Sg_new_effect_f_free : eff_decl_view -> sigelt_view
  | Sg_sub_effect : sub_eff_view -> sigelt_view
  | Sg_effect_abbrev : name -> list univ_name  -> list binder -> comp -> sigelt_view
  | UnkDEBUG_bundle
  | UnkDEBUG_declare_typ
  | UnkDEBUG_main
  | UnkDEBUG_assume
  | UnkDEBUG_pragma
  | UnkDEBUG_splice
  | Unk

let var : eqtype = nat

type exp : Type =
  | Unit : exp
  | Var : var -> exp
  | Mult : exp -> exp -> exp


type decls = list sigelt

let rec forall_list (p:'a -> Type) (l:list 'a) : Type =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

(* Comparison of a term_view to term. Allows to recurse while changing the view *)
val smaller : term_view -> term -> Type0
let smaller tv t =
    match tv with
    | Tv_App l r ->
        l << t /\ r << t /\ fst r << t

    | Tv_Abs b t'
    | Tv_Arrow b t' ->
        b << t /\ t' << t

    | Tv_Refine b t' ->
        bv << t /\ t' << t

    | Tv_Let r bv t1 t2 ->
        bv << t /\ t1 << t /\ t2 << t

    | Tv_Match t1 brs ->
        t1 << t /\ (forall_list (fun (b, t') -> t' << t) brs)

    | Tv_AscribedT e ty tac ->
      e << t /\ ty << t /\ tac << t

    | Tv_AscribedC e c tac ->
      e << t /\ c << t /\ tac << t

    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown
    | Tv_Var _
    | Tv_BVar _
    | Tv_Uvar _ _
    | Tv_FVar _ -> True

val smaller_comp : comp_view -> comp -> Type0
let smaller_comp cv c =
    match cv with
    | C_Total t md ->
        t << c /\ (match md with | Some d -> d << c | None -> True)
    | C_Lemma pre post pats ->
        pre << c /\ post << c /\ pats << c
    | C_Unknown ->
        True

val smaller_bv : bv_view -> bv -> Type0
let smaller_bv bvv bv =
    bvv.bv_sort << bv

val smaller_binder : binder -> (bv * aqualv) -> Type0
let smaller_binder b (bv, _) =
    bv << b

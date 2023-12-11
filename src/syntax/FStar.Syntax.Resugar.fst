(*
  Copyright 2008-2014 Microsoft Research

  Authors: Qunyan Mangus, Nikhil Swamy

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
module FStar.Syntax.Resugar //we should rename FStar.ToSyntax to something else
open FStar
open FStar.Compiler
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Compiler.Util
open FStar.Const
open FStar.Compiler.List
open FStar.Parser.AST

module I = FStar.Ident
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module A  = FStar.Parser.AST
module C = FStar.Parser.Const
module U = FStar.Syntax.Util
module BU = FStar.Compiler.Util
module D = FStar.Parser.ToDocument
module UF = FStar.Syntax.Unionfind
module E = FStar.Errors
module DsEnv = FStar.Syntax.DsEnv

(* Helpers to print/debug the resugaring phase *)
let doc_to_string doc = FStar.Pprint.pretty_string (float_of_string "1.0") 100 doc
let parser_term_to_string t = doc_to_string (D.term_to_document t)
let parser_pat_to_string t = doc_to_string (D.pat_to_document t)

(* A callback into FStar.Syntax.Print.term_to_string. Careful, it's mutually recursive
 * with this module and could loop, so only use it for debugging. *)
let tts (t:S.term) : string = U.tts t

let map_opt = List.filter_map

let bv_as_unique_ident (x:S.bv) : I.ident =
  let unique_name =
    if starts_with reserved_prefix (string_of_id x.ppname)
    ||  Options.print_real_names () then
      (string_of_id x.ppname) ^ (string_of_int x.index)
    else
      (string_of_id x.ppname)
  in
  I.mk_ident (unique_name, (range_of_id x.ppname))

let filter_imp a =
  (* keep typeclass args *)
  match a with
  | Some (S.Meta t) when U.is_fvar C.tcresolve_lid t -> true
  | Some (S.Implicit _)
  | Some (S.Meta _) -> false
  | _ -> true

let filter_imp_args (args:S.args) : S.args =
  args |> List.filter (function (_, None) -> true | (_, Some arg) -> not (arg.aqual_implicit))

let filter_imp_bs bs =
  bs |> List.filter (fun b -> b.binder_qual |> filter_imp)

let filter_pattern_imp xs =
  List.filter (fun (_, is_implicit) -> not is_implicit) xs

let label s t =
  if s = "" then t
  else A.mk_term (A.Labeled (t,s,true)) t.range A.Un

let rec universe_to_int n u =
  match u with
    | U_succ u -> universe_to_int (n+1) u
    | _ -> (n, u)

let universe_to_string univs =
  if (Options.print_universes()) then
    List.map (fun x -> (string_of_id x)) univs |> String.concat  ", "
  else ""

let rec resugar_universe (u:S.universe) r: A.term =
  let mk (a:A.term') r: A.term =
      //augment `a` an Unknown level (the level is unimportant ... we should maybe remove it altogether)
      A.mk_term a r A.Un
  in
  begin match u with
    | U_zero ->
      mk (A.Const(Const_int ("0", None))) r

    | U_succ _ ->
      let (n, u) = universe_to_int 0 u in
      begin match u with
      | U_zero ->
        mk (A.Const(Const_int(string_of_int n, None))) r

      | _ ->
        let e1 = mk (A.Const(Const_int(string_of_int n, None))) r in
        let e2 = resugar_universe u r in
        mk (A.Op(Ident.id_of_text "+", [e1; e2])) r
      end

    | U_max l ->
      begin match l with
      | [] -> failwith "Impossible: U_max without arguments"
      | _ ->
        let t = mk (A.Var(lid_of_path ["max"] r)) r in
        List.fold_left(fun acc x -> mk (A.App(acc, resugar_universe x r, A.Nothing)) r) t l
      end

    | U_name u -> mk (A.Uvar(u)) r
    | U_unif _ -> mk A.Wild r
    | U_bvar x ->
      (* This case can happen when trying to print a subterm of a term that is not opened.*)
      let id = I.mk_ident (strcat "uu__univ_bvar_" (string_of_int x), r) in
      mk (A.Uvar(id)) r

    | U_unknown -> mk A.Wild r (* not sure what to resugar to since it is not created by desugar *)
  end

// resugar_universe' included for consistency (it doesn't use its environment)
let resugar_universe' (env: DsEnv.env) (u:S.universe) r: A.term =
  resugar_universe u r

type expected_arity = option int

(* GM: This almost never actually returns an expected arity. It does so
only for subtraction, I think. *)
let rec resugar_term_as_op (t:S.term) : option (string*expected_arity) =
  let infix_prim_ops = [
    (C.op_Addition    , "+" );
    (C.op_Subtraction , "-" );
    (C.op_Minus       , "-" );
    (C.op_Multiply    , "*" );
    (C.op_Division    , "/" );
    (C.op_Modulus     , "%" );
    (C.read_lid       , "!" );
    (C.list_append_lid, "@" );
    (C.list_tot_append_lid,"@");
    (C.op_Eq          , "=" );
    (C.op_ColonEq     , ":=");
    (C.op_notEq       , "<>");
    (C.not_lid        , "~" );
    (C.op_And         , "&&");
    (C.op_Or          , "||");
    (C.op_LTE         , "<=");
    (C.op_GTE         , ">=");
    (C.op_LT          , "<" );
    (C.op_GT          , ">" );
    (C.op_Modulus     , "mod");
    (C.and_lid     , "/\\");
    (C.or_lid      , "\\/");
    (C.imp_lid     , "==>");
    (C.iff_lid     , "<==>");
    (C.precedes_lid, "<<");
    (C.eq2_lid     , "==");
    (C.forall_lid  , "forall");
    (C.exists_lid  , "exists");
    (C.salloc_lid  , "alloc");
    (C.calc_finish_lid, "calc_finish");
  ] in
  let fallback fv =
    match infix_prim_ops |> BU.find_opt (fun d -> fv_eq_lid fv (fst d)) with
    | Some op ->
      Some (snd op, None)
    | _ ->
      let length = String.length (nsstr fv.fv_name.v) in
      let str = if length=0 then (string_of_lid fv.fv_name.v)
          else BU.substring_from (string_of_lid fv.fv_name.v) (length+1) in
      (* Check that it is of the shape dtuple int, and return that arity *)
      if BU.starts_with str "dtuple"
         && Option.isSome (BU.safe_int_of_string (BU.substring_from str 6))
      then Some ("dtuple", BU.safe_int_of_string (BU.substring_from str 6))
      else if BU.starts_with str "tuple"
         && Option.isSome (BU.safe_int_of_string (BU.substring_from str 5))
      then Some ("tuple", BU.safe_int_of_string (BU.substring_from str 5))
      else if BU.starts_with str "try_with" then Some ("try_with", None)
      else if fv_eq_lid fv C.sread_lid then Some (string_of_lid fv.fv_name.v, None)
      else None
  in
  match (SS.compress t).n with
    | Tm_fvar fv ->
      let length = String.length (nsstr fv.fv_name.v) in
      let s = if length=0 then string_of_lid fv.fv_name.v
              else BU.substring_from (string_of_lid fv.fv_name.v) (length+1) in
      begin match string_to_op s with
        | Some t -> Some t
        | _ -> fallback fv
      end
    | Tm_uinst(e, us) ->
      resugar_term_as_op e
    | _ -> None

let is_true_pat (p:S.pat) : bool = match p.v with
    | Pat_constant (Const_bool true) -> true
    | _ -> false

let is_tuple_constructor_lid lid =
     C.is_tuple_data_lid' lid
  || C.is_dtuple_data_lid' lid

let may_shorten lid =
  match string_of_lid lid with
  | "Prims.Nil"
  | "Prims.Cons" -> false
  | _ -> not (is_tuple_constructor_lid lid)

let maybe_shorten_lid env lid : lident =
  if may_shorten lid then DsEnv.shorten_lid env lid else lid

let maybe_shorten_fv env fv : lident =
  let lid = fv.fv_name.v in
  maybe_shorten_lid env lid

(* Sizet handled below *)
let serialize_machine_integer_desc (s,w) =
  BU.format3 "FStar.%sInt%s.__%sint_to_t"
    (match s with
     | Unsigned -> "U"
     | Signed -> "")
    (match w with
     | Int8 -> "8"
     | Int16 -> "16"
     | Int32 -> "32"
     | Int64 -> "64")
    (match s with
     | Unsigned -> "u"
     | Signed -> "")

let parse_machine_integer_desc =
  let signs = [Unsigned; Signed] in
  let widths = [Int8; Int16; Int32; Int64] in
  let descs =
    ((Unsigned, Sizet), "FStar.SizeT.__uint_to_t") ::
    List.collect (fun s -> List.map (fun w -> (s, w), serialize_machine_integer_desc (s, w)) widths) signs
  in
  fun (fv:fv) ->
    List.tryFind (fun (_, d) -> d = Ident.string_of_lid (lid_of_fv fv)) descs

let can_resugar_machine_integer fv =
  Option.isSome (parse_machine_integer_desc fv)

let resugar_machine_integer fv (i:string) pos =
  match parse_machine_integer_desc fv with
  | None -> failwith "Impossible: should be guarded by can_resugar_machine_integer"
  | Some (sw, _) -> A.mk_term (A.Const (Const_int(i, Some sw))) pos A.Un

let rec resugar_term' (env: DsEnv.env) (t : S.term) : A.term =
    (* Cannot resugar term back to NamedTyp or Paren *)
    let mk (a:A.term') : A.term =
        //augment `a` with its source position
        //and an Unknown level (the level is unimportant ... we should maybe remove it altogether)
        A.mk_term a t.pos A.Un
    in
    let name a r =
        // make a Name term'
        A.Name (lid_of_path [a] r)
    in
    match (SS.compress t).n with //always call compress before case-analyzing a S.term
    | Tm_delayed _ ->
      failwith "Tm_delayed is impossible after compress"

    | Tm_lazy i ->
      resugar_term' env (U.unfold_lazy i)

    | Tm_bvar x ->
      (* this case can happen when printing a subterm of a term that is not opened *)
      let l = FStar.Ident.lid_of_ids [bv_as_unique_ident x] in
      mk (A.Var l)

    | Tm_name x -> //a lower-case identifier
      //this is is too simplistic
      //the resulting unique_name is very ugly
      //it would be better to try to use x.ppname alone, unless the suffix is deemed semantically necessary
      let l = FStar.Ident.lid_of_ids [bv_as_unique_ident x] in
      mk (A.Var l)

    | Tm_fvar fv -> //a top-level identifier, may be lowercase or upper case
      //should be A.Var if lowercase
      //and A.Name if uppercase
      let a = fv.fv_name.v in
      let length = String.length (nsstr fv.fv_name.v) in
      let s = if length=0 then string_of_lid a
          else BU.substring_from (string_of_lid a) (length+1) in
      let is_prefix = I.reserved_prefix ^ "is_" in
      if BU.starts_with s is_prefix then
        let rest = BU.substring_from s (String.length is_prefix) in
        mk (A.Discrim(lid_of_path [rest] t.pos))
      else if BU.starts_with s U.field_projector_prefix then
        let rest = BU.substring_from s (String.length U.field_projector_prefix) in
        let r = BU.split rest U.field_projector_sep in
        begin match r with
          | [fst; snd] ->
            let l = lid_of_path [fst] t.pos in
            let r = I.mk_ident (snd, t.pos) in
            mk (A.Projector(l, r ))
          | _ ->
            failwith "wrong projector format"
        end
       else if (lid_equals a C.smtpat_lid) then
         mk (A.Tvar (I.mk_ident ("SMTPat", I.range_of_lid a)))
       else if (lid_equals a C.smtpatOr_lid) then
         mk (A.Tvar (I.mk_ident ("SMTPatOr", I.range_of_lid a)))
       else if (lid_equals a C.assert_lid || lid_equals a C.assume_lid
                || Char.uppercase (String.get s 0) <> String.get s 0) then
         mk (A.Var (maybe_shorten_fv env fv))
       else // FIXME check in environment instead of checking case
         mk (A.Construct (maybe_shorten_fv env fv, []))

    | Tm_uinst(e, universes) ->
      let e = resugar_term' env e in
      if Options.print_universes() then
        let univs = List.map (fun x -> resugar_universe x t.pos) universes in
        match e with
        | { tm = A.Construct (hd, args); range = r; level = l } ->
          let args = args @ (List.map (fun u -> (u, A.UnivApp)) univs) in
          A.mk_term (A.Construct (hd, args)) r l
        | _ ->
          List.fold_left (fun acc u -> mk (A.App (acc, u, A.UnivApp))) e univs
      else
        e

    | Tm_constant c ->
      if is_teff t
      then mk (name "Effect" t.pos)
      else mk (A.Const c)

    | Tm_type u ->
      let nm, needs_app =
        match u with
        | U_zero ->  "Type0", false
        | U_unknown -> "Type", false
        | _ -> "Type", true in
      let typ = mk (name nm t.pos) in
      if needs_app && Options.print_universes ()
      then mk (A.App (typ, resugar_universe u t.pos, UnivApp))
      else typ

    | Tm_abs {bs=xs; body} -> //fun x1 .. xn -> body
      //before inspecting any syntactic form that has binding structure
      //you must call SS.open_* to replace de Bruijn indexes with names
      let xs, body = SS.open_term xs body in
      let xs = if Options.print_implicits () then xs else xs |> List.filter (fun x -> x.binder_qual |> filter_imp) in
      let body_bv = FStar.Syntax.Free.names body in
      let patterns = xs |> List.choose (fun x ->
        //x.sort contains a type annotation for the bound variable
        //the pattern `p` below only contains the variable, not the annotation
        //but, if the user wrote the annotation, then we should record that and print it back
        //additionally, if we're in verbose mode, e.g., if --print_bound_var_types is set
        //    then we should print the annotation too
        resugar_bv_as_pat env x.binder_bv x.binder_qual body_bv)
      in
      let body = resugar_term' env body in
      (* If no binders/patterns remain after filtering, drop the Abs node *)
      if List.isEmpty patterns
      then body
      else mk (A.Abs(patterns, body))

    | Tm_arrow _ ->
      (* Flatten the arrow *)
      let xs, body =
        match (SS.compress (U.canon_arrow t)).n with
        | Tm_arrow {bs=xs; comp=body} -> xs, body
        | _ -> failwith "impossible: Tm_arrow in resugar_term"
      in
      let xs, body = SS.open_comp xs body in
      let xs =
        if (Options.print_implicits())
        then xs
        else filter_imp_bs xs in
      let body = resugar_comp' env body in
      let xs = xs |> map_opt (fun b -> resugar_binder' env b t.pos) |> List.rev in
      let rec aux body = function
        | [] -> body
        | hd::tl ->
          let body = mk (A.Product([hd], body)) in
          aux body tl in
      aux body xs

    | Tm_refine {b=x; phi} ->
      (* bv * term -> binder * term *)
      let x, phi = SS.open_term [S.mk_binder x] phi in
      let b = BU.must (resugar_binder' env (List.hd x) t.pos) in
      mk (A.Refine(b, resugar_term' env phi))

    | Tm_app {hd={n=Tm_fvar fv}; args=[(e, _)]}
      when not (Options.print_implicits())
           && S.fv_eq_lid fv C.b2t_lid ->
      resugar_term' env e

    | Tm_app {hd={n=Tm_fvar fv}; args=[({n=Tm_constant (Const_int (i, None))}, _)]}
      when can_resugar_machine_integer fv ->
      resugar_machine_integer fv i t.pos

    | Tm_app {hd=e; args} ->
      (* Op("=!=", args) is desugared into Op("~", Op("==") and not resugared back as "=!=" *)
      let rec last = function
            | hd :: [] -> [hd]
            | hd :: tl -> last tl
            | _ -> failwith "last of an empty list"
      in
      let first_two_explicit args =
        let rec drop_implicits args =
          match args with
          | (_, Some ({aqual_implicit=true}))::tl -> drop_implicits tl
          | _ -> args
        in
        match drop_implicits args with
        | []
        | [_] -> failwith "not_enough explicit_arguments"
        | a1::a2::_ -> [a1;a2]
      in
      let resugar_as_app e args =
        let args =
          List.map (fun (e, qual) -> (resugar_term' env e, resugar_aqual env qual)) args in
        match resugar_term' env e with
        | { tm = A.Construct (hd, previous_args); range = r; level = l } ->
          A.mk_term (A.Construct (hd, previous_args @ args)) r l
        | e ->
          List.fold_left (fun acc (x, qual) -> mk (A.App (acc, x, qual))) e args
      in
      let args : list (S.term * S.aqual) =
        if Options.print_implicits ()
        then args
        else filter_imp_args args in
      begin match resugar_term_as_op e with
        | None->
          resugar_as_app e args

        | Some ("calc_finish", _) ->
          begin match resugar_calc env t with
          | Some r -> r
          | _ -> resugar_as_app e args
          end

        | Some ("tuple", _) ->
          let out =
              List.fold_left
                (fun out (x, _) ->
                    let x = resugar_term' env x in
                    match out with
                    | None -> Some x
                    | Some prefix ->
                      Some (mk(A.Op(Ident.id_of_text "*", [prefix; x]))))
                    None
                    args
          in
          Option.get out

(* This is wrong: It treats the first N - 1 args of dtupleN as implicit
   But, they are not *)
(*   
        | Some ("dtuple", _) when List.length args > 0 ->
          (* this is desugared from Sum(binders*term) *)
          let args = last args in
          let body = match args with
            | [(b, _)] -> b
            | _ -> failwith "wrong arguments to dtuple"
          in
          begin match (SS.compress body).n with
            | Tm_abs(xs, body, _) ->
                let xs, body = SS.open_term xs body in
                let xs =
                  if (Options.print_implicits())
                  then xs
                  else filter_imp_bs xs in
                let xs = xs |> map_opt (fun b -> resugar_binder' env b t.pos) in
                let body = resugar_term' env body in
                mk (A.Sum(List.map Inl xs, body))

            | _ ->
              let args = args |> List.map (fun (e, qual) ->
                resugar_term' env e) in
              let e = resugar_term' env e in
              List.fold_left(fun acc x -> mk (A.App(acc, x, A.Nothing))) e args
          end
*)
        | Some ("dtuple", _) ->
          resugar_as_app e args

        | Some (ref_read, _) when (ref_read = string_of_lid C.sread_lid) ->
          let (t, _) = List.hd args in
          begin match (SS.compress t).n with
            | Tm_fvar fv when (U.field_projector_contains_constructor (string_of_lid fv.fv_name.v)) ->
              let f = lid_of_path [string_of_lid fv.fv_name.v] t.pos in
              mk (A.Project(resugar_term' env t, f))
            | _ -> resugar_term' env t
          end

        | Some ("try_with", _) when List.length args > 1 ->
          (* attempt to resugar as `try .. with | ...`, but otherwise just resugar normally *)
          begin try
            (* only the first two explicit args are from original AST terms,
             * others are added by typechecker *)
            (* TODO: we need a place to store the information in the args added by the typechecker *)
            let new_args = first_two_explicit args in
            let body, handler = match new_args with
              | [(a1, _);(a2, _)] -> a1, a2 (* where a1 and a1 is Tm_abs(Tm_match)) *)
              | _ ->
                failwith("wrong arguments to try_with")
            in
            let decomp term = match (SS.compress term).n with
              | Tm_abs {bs=x; body=e} ->
                let x, e = SS.open_term x e in
                e
              | _ -> failwith("wrong argument format to try_with: " ^ term_to_string (resugar_term' env term)) in
            let body = resugar_term' env (decomp body) in
            let handler = resugar_term' env (decomp handler) in
            let rec resugar_body t = match (t.tm) with
              | A.Match(e, None, None, [(_,_,b)]) -> b
              | A.Let(_, _, b) -> b  // One branch Match that is resugared as Let
              | A.Ascribed(t1, t2, t3, use_eq) ->
                (* this case happens when the match is wrapped in Meta_Monadic which is resugared to Ascribe*)
                mk (A.Ascribed(resugar_body t1, t2, t3, use_eq))
              | _ -> failwith("unexpected body format to try_with") in
            let e = resugar_body body in
            let rec resugar_branches t = match (t.tm) with
              | A.Match(e, None, None, branches) -> branches
              | A.Ascribed(t1, t2, t3, _) ->
                (* this case happens when the match is wrapped in Meta_Monadic which is resugared to Ascribe*)
                (* TODO: where should we keep the information stored in Ascribed? *)
                resugar_branches t1
              | _ ->
                (* TODO: forall created by close_forall doesn't follow the normal forall format, not sure how to resugar back *)
                []
            in
            let branches = resugar_branches handler in
            mk (A.TryWith(e, branches))
          with
          | _ ->
            resugar_as_app e args
          end

        | Some ("try_with", _) ->
          resugar_as_app e args

        (* These have implicits, don't do the fancy printing when --print_implicits is on *)
        | Some (op, _) when (op = "="
                          || op = "=="
                          || op = "==="
                          || op = "@"
                          || op = ":="
                          || op = "|>"
                          || op = "<<")
            && Options.print_implicits () ->
          resugar_as_app e args

        | Some (op, _) 
          when starts_with op "forall"
            || starts_with op "exists" ->
          (* desugared from QForall(binders * patterns * body) to Tm_app(forall, Tm_abs(binders, Tm_meta(body, meta_pattern(list args)*)
          let rec uncurry xs pats (t:A.term) flavor_matches =
            match t.tm with
            | A.QExists(xs', (_, pats'), body)
            | A.QForall(xs', (_, pats'), body)
            | A.QuantOp(_, xs', (_, pats'), body) when flavor_matches t ->
                uncurry (xs@xs') (pats@pats') body flavor_matches
            | _ ->
                xs, pats, t
          in
          let resugar_forall_body body = match (SS.compress body).n with
            | Tm_abs {bs=xs; body} ->
                let xs, body = SS.open_term xs body in
                let xs =
                  if (Options.print_implicits())
                  then xs
                  else filter_imp_bs xs in
                let xs = xs |> map_opt (fun b -> resugar_binder' env b t.pos) in
                let pats, body = match (SS.compress body).n with
                  | Tm_meta {tm=e; meta=m} ->
                    let body = resugar_term' env e in
                    let pats, body = match m with
                      | Meta_pattern (_, pats) ->
                        List.map (fun es -> es |> List.map (fun (e, _) -> resugar_term' env e)) pats,
                        body
                      | Meta_labeled (s, r, p) ->
                        // this case can occur in typechecker when a failure is wrapped in meta_labeled
                        [], mk (A.Labeled (body, s, p))
                      | _ -> failwith "wrong pattern format for QForall/QExists"
                    in
                    pats, body
                  | _ -> [], resugar_term' env body
                in
                let decompile_op op =
                   match FStar.Parser.AST.string_to_op op with
                   | None -> op
                  | Some (op, _) -> op
                in
                let flavor_matches t =
                  match t.tm, op with
                  | A.QExists _, "exists"
                  | A.QForall _, "forall" -> true
                  | A.QuantOp(id, _, _, _), _ ->
                    Ident.string_of_id id = op
                  | _ -> false
                in
                let xs, pats, body = uncurry xs pats body flavor_matches in
                let binders = A.idents_of_binders xs t.pos in
                if op = "forall"
                then mk (A.QForall(xs, (binders, pats), body))
                else if op = "exists"
                then mk (A.QExists(xs, (binders, pats), body))
                else mk (A.QuantOp(Ident.id_of_text op, xs, (binders, pats), body))
                 
            | _ ->
              (*forall added by typechecker.normalize doesn't not have Tm_abs as body*)
              (*TODO:  should we resugar them back as forall/exists or just as the term of the body *)
              if op = "forall" then mk (A.QForall([], ([], []), resugar_term' env body))
              else mk (A.QExists([], ([], []), resugar_term' env body))
          in
          (* only the last arg is from original AST terms, others are added by typechecker *)
          (* TODO: we need a place to store the information in the args added by the typechecker *)
          if List.length args > 0 then
            let args = last args in
            begin match args with
              | [(b, _)] -> resugar_forall_body b
              | _ -> failwith "wrong args format to QForall"
            end
          else
            resugar_as_app e args

        | Some ("alloc", _) ->
          let (e, _ ) = List.hd args in
          resugar_term' env e

        | Some (op, expected_arity) ->
          let op = Ident.id_of_text op in
          let resugar args = args |> List.map (fun (e, qual) ->
            resugar_term' env e, resugar_aqual env qual)
          in
           (* ignore the arguments added by typechecker *)
          (* TODO: we need a place to store the information in the args added by the typechecker *)
          //NS: this seems to produce the wrong output on things like
          begin
          match expected_arity with
          | None ->
            let resugared_args = resugar args in
            let expect_n = D.handleable_args_length op in
            if List.length resugared_args >= expect_n
            then let op_args, rest = BU.first_N expect_n resugared_args in
                 let head = mk (A.Op(op, List.map fst op_args)) in
                 List.fold_left
                        (fun head (arg, qual) -> mk (A.App (head, arg, qual)))
                        head
                        rest
            else resugar_as_app e args
          | Some n when List.length args = n -> mk (A.Op(op, List.map fst (resugar args)))
          | _ -> resugar_as_app e args
          end
    end

    | Tm_match {scrutinee=e; ret_opt=None; brs=[(pat, wopt, t)]} ->
      (* for match expressions that have exactly 1 branch, instead of printing them as `match e with | P -> e1`
        it would be better to print it as `let P = e in e1`. *)
      (* only do it when pat is not Pat_disj since ToDocument only expects disjunctivePattern in Match and TryWith *)
      let pat, wopt, t = SS.open_branch (pat, wopt, t) in
      let branch_bv = FStar.Syntax.Free.names t in
      let bnds = [None, (resugar_pat' env pat branch_bv, resugar_term' env e)] in
      let body = resugar_term' env t in
      mk (A.Let(A.NoLetQualifier, bnds, body))

    (* | Tm_match(e, asc_opt, [(pat1, _, t1); (pat2, _, t2)], _) *)
    (*   when is_true_pat pat1 && is_wild_pat pat2 -> *)
    (*   let asc_opt = resugar_match_returns env e t.pos asc_opt in *)
    (*   mk (A.If(resugar_term' env e, *)
    (*            None, *)
    (*            asc_opt, *)
    (*            resugar_term' env t1, *)
    (*            resugar_term' env t2)) *)

    | Tm_match {scrutinee=e; ret_opt=asc_opt; brs=branches} ->
      let resugar_branch (pat, wopt,b) =
        let pat, wopt, b = SS.open_branch (pat, wopt, b) in
        let branch_bv = FStar.Syntax.Free.names b in
        let pat = resugar_pat' env pat branch_bv in
        let wopt = match wopt with
          | None -> None
          | Some e -> Some (resugar_term' env e) in
        let b = resugar_term' env b in
        (pat, wopt, b) in
      let asc_opt = resugar_match_returns env e t.pos asc_opt in
      mk (A.Match(resugar_term' env e,
                  None, asc_opt,
                  List.map resugar_branch branches))

    | Tm_ascribed {tm=e; asc} ->
      let asc, tac_opt, b = resugar_ascription env asc in
      mk (A.Ascribed (resugar_term' env e, asc, tac_opt, b))

    | Tm_let {lbs=(is_rec, source_lbs); body} ->
      let mk_pat a = A.mk_pattern a t.pos in
      let source_lbs, body = SS.open_let_rec source_lbs body in
      let resugar_one_binding bnd =
        (* TODO : some stuff are open twice there ! (may have already been opened in open_let_rec) *)
        let attrs_opt =
            match bnd.lbattrs with
            | [] -> None
            | tms -> Some (List.map (resugar_term' env) tms)
        in
        let univs, td = SS.open_univ_vars bnd.lbunivs (U.mk_conj bnd.lbtyp bnd.lbdef) in
        let typ, def = match (SS.compress td).n with
          | Tm_app {args=[(t, _); (d, _)]} -> t, d
          | _ -> failwith "wrong let binding format"
        in
        let binders, term, is_pat_app = match (SS.compress def).n with
          | Tm_abs {bs=b; body=t} ->
            let b, t = SS.open_term b t in
            let b =
              if (Options.print_implicits())
              then b
              else filter_imp_bs b in
            b, t, true
          | _ -> [], def, false
        in
        let pat, term = match bnd.lbname with
          | Inr fv -> mk_pat (A.PatName fv.fv_name.v), term
          | Inl bv ->
            mk_pat (A.PatVar (bv_as_unique_ident bv, None, [])), term
        in
        attrs_opt,
        (if is_pat_app then
          let args = binders |> map_opt (fun b ->
            BU.map_opt
              (resugar_bqual env b.binder_qual)
              (fun q ->
               mk_pat(A.PatVar (bv_as_unique_ident b.binder_bv,
                                q,
                                b.binder_attrs |> List.map (resugar_term' env))))) in
          (mk_pat (A.PatApp (pat, args)), resugar_term' env term), (universe_to_string univs)
        else
          (pat, resugar_term' env term), (universe_to_string univs))
      in
      let r = List.map (resugar_one_binding) source_lbs in
      let bnds =
          let f (attrs, (pb, univs)) =
            if not (Options.print_universes ()) then attrs, pb
            (* Print bound universes as a comment *)
            else attrs, (fst pb, label univs (snd pb))
          in
          List.map f r
      in
      let body = resugar_term' env body in
      mk (A.Let((if is_rec then A.Rec else A.NoLetQualifier), bnds, body))

    | Tm_uvar (u, _) ->
      let s = "?u" ^ (UF.uvar_id u.ctx_uvar_head |> string_of_int) in
      (* TODO : should we put a pretty_non_parseable option for these cases ? *)
      label s (mk A.Wild)

    | Tm_quoted (tm, qi) ->
      let qi = match qi.qkind with
               | Quote_static -> Static
               | Quote_dynamic -> Dynamic
      in
      mk (A.Quote (resugar_term' env tm, qi))

    | Tm_meta {tm=e; meta=m} ->
       let resugar_meta_desugared = function
          | Sequence ->
              let term = resugar_term' env e in
              let rec resugar_seq t = match t.tm with
                | A.Let(_, [_, (p, t1)], t2) ->
                   mk (A.Seq(t1, t2))
                | A.Ascribed(t1, t2, t3, use_eq) ->
                   (* this case happens when the let is wrapped in Meta_Monadic which is resugared to Ascribe*)
                   mk (A.Ascribed(resugar_seq t1, t2, t3, use_eq))
                | _ ->
                   (* this case happens in typechecker.normalize when Tm_let is_pure_effect, then
                      only the body of Tm_let is used. *)
                   (* TODO: How should it be resugared *)
                   t
              in
              resugar_seq term
          | Machine_integer (_,_)
          | Primop (* doesn't seem to be generated by desugar *)
          | Masked_effect (* doesn't seem to be generated by desugar *)
          | Meta_smt_pat -> (* nothing special, just resugar the term *)
              resugar_term' env e
      in
      begin match m with
      | Meta_pattern (_, pats) ->
        // This case is possible in TypeChecker when creating "haseq" for Sig_inductive_typ whose Sig_datacon has no binders.
        let pats = List.flatten pats |> List.map (fun (x, _) -> resugar_term' env x) in
        // Is it correct to resugar it to Attributes.
        mk (A.Attributes pats)

      | Meta_labeled _ ->
          (* Ignore the label, we don't want to print it *)
          resugar_term' env e
      | Meta_desugared i ->
          resugar_meta_desugared i
      | Meta_named t ->
          mk (A.Name t)
      | Meta_monadic _
      | Meta_monadic_lift _ -> resugar_term' env e
      end

    | Tm_unknown -> mk A.Wild

and resugar_ascription env (asc, tac_opt, b) =
  (match asc with
   | Inl n -> (* term *)
     resugar_term' env n
   | Inr n -> (* comp *)
     resugar_comp' env n),
  BU.map_opt tac_opt (resugar_term' env),
  b

(* This entire function is of course very tied to the the desugaring
of calc expressions in ToSyntax. This only really works for fully
elaborated terms, sorry. *)
and resugar_calc (env:DsEnv.env) (t0:S.term) : option A.term =
  let mk (a:A.term') : A.term =
    A.mk_term a t0.pos A.Un
  in
  (* Returns the non-resugared final relation and the calc_pack *)
  let resugar_calc_finish (t:S.term) : option (S.term * S.term) =
    let hd, args = U.head_and_args t in
    match (SS.compress (U.un_uinst hd)).n, args with
    | Tm_fvar fv, [(_, Some { aqual_implicit = true }); // type
                   (rel, None);                         // top relation
                   (_, Some { aqual_implicit = true }); // x
                   (_, Some { aqual_implicit = true }); // y
                   (_, Some { aqual_implicit = true }); // rs
                   (pf, None)]                          // pf : unit -> Tot (calc_pack rs x y)
        when S.fv_eq_lid fv C.calc_finish_lid ->
        let pf = U.unthunk pf in
        Some (rel, pf)

    | _ ->
        None
  in
  (* Un-eta expand a relation. Return it as-is if cannot be done. *)
  let un_eta_rel (rel:S.term) : option S.term =
    let bv_eq_tm (b:bv) (t:S.term) : bool =
      match (SS.compress t).n with
      | Tm_name b' when S.bv_eq b b' -> true
      | _ -> false
    in
    match (SS.compress rel).n with
    | Tm_abs {bs=[b1;b2]; body} ->
        let ([b1;b2], body) = SS.open_term [b1;b2] body in
        let body = U.unascribe body in
        let body = match (U.unb2t body) with
                   | Some body -> body
                   | None -> body
        in
        begin match (SS.compress body).n with
        | Tm_app {hd=e; args} when List.length args >= 2 ->
          begin match List.rev args with
          | (a1, None)::(a2, None)::rest ->
            if bv_eq_tm b1.binder_bv a2 && bv_eq_tm b2.binder_bv a1 // mind the flip
            then Some <| U.mk_app e (List.rev rest)
            else Some rel
          | _ ->
            Some rel
          end
        | _ -> Some rel
        end

    | _ ->
        Some rel
  in
  (* Resugars an application of calc_step, returning the term, the relation,
   * the justifcation, and the rest of the proof. *)
  let resugar_step (pack:S.term) : option (S.term * S.term * S.term * S.term) =
    let hd, args = U.head_and_args pack in
    match (SS.compress (U.un_uinst hd)).n, args with
    | Tm_fvar fv, [(_, Some ({ aqual_implicit = true })); // type
                   (_, Some ({ aqual_implicit = true })); // x
                   (_, Some ({ aqual_implicit = true })); // y
                   (rel, None);              // relation
                   (z, None);                // z, next val
                   (_, Some ({ aqual_implicit = true })); //rs
                   (pf, None);               // pf, rest of proof (thunked)
                   (j, None)]                // justification (thunked)
        when S.fv_eq_lid fv C.calc_step_lid ->
        let pf = U.unthunk pf in
        let j = U.unthunk j in
        Some (z, rel, j, pf)

    | _ ->
        None
  in
  (* Resugar an application of calc_init *)
  let resugar_init (pack:S.term) : option S.term =
    let hd, args = U.head_and_args pack in
    match (SS.compress (U.un_uinst hd)).n, args with
    | Tm_fvar fv, [(_, Some ({ aqual_implicit = true })); // type
                   (x, None)]                // initial value
        when S.fv_eq_lid fv C.calc_init_lid ->
        Some x

    | _ ->
        None
  in
  (* Repeats the above function until it returns none; what remains should be a calc_init *)
  let rec resugar_all_steps (pack:S.term) : option (list (S.term * S.term * S.term) * S.term) =
    match resugar_step pack with
    | Some (t, r, j, k) ->
        BU.bind_opt (resugar_all_steps k) (fun (steps, k) ->
        Some ((t, r, j)::steps, k))
    | None ->
        Some ([], pack)
  in
  let resugar_rel (rel:S.term) : A.term =
    (* Try to un-eta, don't worry if not *)
    let rel = match un_eta_rel rel with
              | Some rel -> rel
              | None -> rel
    in
    let fallback () =
        mk (A.Paren (resugar_term' env rel))
    in
    let hd, args = U.head_and_args rel in
    if Options.print_implicits ()
    && List.existsb (fun (_, q) -> S.is_aqual_implicit q) args
    then fallback ()
    else
      begin match resugar_term_as_op hd with
      | Some (s, None)
      | Some (s, Some 2) -> mk (A.Op (Ident.id_of_text s, []))
      | _ -> fallback ()
      end
  in
  let build_calc (rel:S.term) (x0:S.term) (steps : list (S.term * S.term * S.term)) : A.term =
    let r = resugar_term' env in
    mk (CalcProof (resugar_rel rel, r x0,
                    List.map (fun (z, rel, j) -> CalcStep (resugar_rel rel, r j, r z)) steps))
  in

  BU.bind_opt (resugar_calc_finish t0) (fun (rel, pack) ->
  BU.bind_opt (resugar_all_steps pack) (fun (steps, k) ->
  BU.bind_opt (resugar_init k) (fun x0 ->
  Some <| build_calc rel x0 (List.rev steps))))

and resugar_match_returns env scrutinee r asc_opt =
  match asc_opt with
  | None -> None
  | Some (b, asc) ->
    let bopt, asc =
      let bs, asc = SS.open_ascription [b] asc in
      let b = List.hd bs in
      //trying to be a little smart,
      //  if the binder name is the reserved prefix, then don't emit it
      //but we need to substitute binder with scrutinee,
      //  basically reverse of what ToSyntax does
      if string_of_id b.binder_bv.ppname = C.match_returns_def_name
      then match (SS.compress scrutinee |> U.unascribe).n with
           | Tm_name sbv ->
             None, SS.subst_ascription [NT (b.binder_bv, S.bv_to_name sbv)] asc
           | _ -> None, asc
      else Some b, asc in
    let bopt = BU.map_option (fun b ->
      BU.must (resugar_binder' env b r)
      |> A.ident_of_binder r) bopt in
    let asc, use_eq =
      match resugar_ascription env asc with
      | asc, None, use_eq -> asc, use_eq
      | _ -> failwith "resugaring does not support match return annotation with a tactic" in
    Some (bopt, asc, use_eq)


and resugar_comp' (env: DsEnv.env) (c:S.comp) : A.term =
  let mk (a:A.term') : A.term =
        //augment `a` with its source position
        //and an Unknown level (the level is unimportant ... we should maybe remove it altogether)
        A.mk_term a c.pos A.Un
  in
  match (c.n) with
  | Total typ ->
    let t = resugar_term' env typ in
    if not (Options.print_implicits())
    then t
    else mk (A.Construct(C.effect_Tot_lid, [(t, A.Nothing)]))

  | GTotal typ ->
    let t = resugar_term' env typ in
    mk (A.Construct(C.effect_GTot_lid, [(t, A.Nothing)]))

  | Comp c ->
    let result = (resugar_term' env c.result_typ, A.Nothing) in
    let mk_decreases (fl : list cflag) : list A.term =
      let rec aux l = function
       | [] -> l
       | hd::tl ->
          match hd with
          | DECREASES dec_order ->
            let d =
              match dec_order with
              | Decreases_lex [t] -> // special casing for single term
                resugar_term' env t
              | Decreases_lex ts ->
                mk (LexList (ts |> List.map (resugar_term' env)))
              | Decreases_wf (rel, e) ->
                mk (WFOrder (resugar_term' env rel, resugar_term' env e)) in
            let e = mk (Decreases (d, None)) in
            aux (e::l) tl
          | _ -> aux l tl
      in
      aux [] fl
    in
    if lid_equals c.effect_name C.effect_Lemma_lid && List.length c.effect_args = 3 then
      let args = List.map(fun (e,_) -> (resugar_term' env e, A.Nothing)) c.effect_args in
      let pre, post, pats =
        match c.effect_args with
        | (pre, _)::(post, _)::(pats, _)::[] ->
          pre, post, pats
        | _ -> failwith "impossible"
      in
      let pre = (if U.is_fvar C.true_lid pre then [] else [pre]) in
      let post = U.unthunk_lemma_post post in
      let pats = if U.is_fvar C.nil_lid (U.head_of pats) then [] else [pats] in

      let pre = List.map (fun t -> mk (Requires (resugar_term' env t, None))) pre in
      let post = mk (Ensures (resugar_term' env post, None)) in
      let pats = List.map (resugar_term' env) pats in
      let decrease = mk_decreases c.flags in

      mk (A.Construct(maybe_shorten_lid env c.effect_name, List.map (fun t -> (t, A.Nothing)) (pre@post::decrease@pats)))

    else if (Options.print_effect_args()) then
      (* let universe = List.map (fun u -> resugar_universe u) c.comp_univs in *)
      let args = List.map(fun (e,_) -> (resugar_term' env e, A.Nothing)) c.effect_args in
      let decrease = List.map (fun t -> (t, A.Nothing)) (mk_decreases c.flags) in
      mk (A.Construct(maybe_shorten_lid env c.effect_name, result::decrease@args))
    else
      mk (A.Construct(maybe_shorten_lid env c.effect_name, [result]))

and resugar_binder' env (b:S.binder) r : option A.binder =
  BU.map_opt (resugar_bqual env b.binder_qual) begin fun imp ->
    let e = resugar_term' env b.binder_bv.sort in
    match (e.tm) with
    | A.Wild ->
      A.mk_binder (A.Variable(bv_as_unique_ident b.binder_bv)) r A.Type_level imp
    | _ ->
      if S.is_null_bv b.binder_bv then
        A.mk_binder (A.NoName e) r A.Type_level imp
      else
        A.mk_binder (A.Annotated (bv_as_unique_ident b.binder_bv, e)) r A.Type_level imp
  end

and resugar_bv_as_pat' env (v: S.bv) aqual (body_bv: Set.set bv) typ_opt =
  let mk a = A.mk_pattern a (S.range_of_bv v) in
  let used = Set.mem v body_bv in
  let pat =
    mk (if used
        then A.PatVar (bv_as_unique_ident v, aqual, [])
        else A.PatWild (aqual, [])) in
  match typ_opt with
  | None | Some { n = Tm_unknown } -> pat
  | Some typ -> if Options.print_bound_var_types ()
               then mk (A.PatAscribed (pat, (resugar_term' env typ, None)))
               else pat

and resugar_bv_as_pat env (x:S.bv) qual body_bv: option A.pattern =
  BU.map_opt
   (resugar_bqual env qual)
   (fun bq -> resugar_bv_as_pat' env x bq body_bv (Some <| SS.compress x.sort))

and resugar_pat' env (p:S.pat) (branch_bv: Set.set bv) : A.pattern =
  (* We lose information when desugar PatAscribed to able to resugar it back *)
  let mk a = A.mk_pattern a p.p in
  let to_arg_qual bopt = // FIXME do (Some false) and None mean the same thing?
    BU.bind_opt bopt (fun b -> if b then Some A.Implicit else None) in
  let may_drop_implicits args =
    not (Options.print_implicits ()) &&
    not (List.existsML (fun (pattern, is_implicit) ->
      //FIXME
             let might_be_used =
               match pattern.v with
               | Pat_var bv -> Set.mem bv branch_bv
               | _ -> true in
             is_implicit && might_be_used) args) in
  let resugar_plain_pat_cons' fv args =
    mk (A.PatApp (mk (A.PatName fv.fv_name.v), args)) in
  let rec resugar_plain_pat_cons fv args =
    let args =
      if may_drop_implicits args
      then filter_pattern_imp args
      else args in
    let args = List.map (fun (p, b) -> aux p (Some b)) args in
    resugar_plain_pat_cons' fv args
  and aux (p:S.pat) (imp_opt:option bool)=
    match p.v with
    | Pat_constant c -> mk (A.PatConst c)

    | Pat_cons (fv, _, []) ->
      mk (A.PatName fv.fv_name.v)

    | Pat_cons(fv, _, args) when (lid_equals fv.fv_name.v C.nil_lid
                               && may_drop_implicits args) ->
      if not (List.isEmpty (filter_pattern_imp args)) then
        E.log_issue p.p (E.Warning_NilGivenExplicitArgs, "Prims.Nil given explicit arguments");
      mk (A.PatList [])

    | Pat_cons(fv, _, args) when (lid_equals fv.fv_name.v C.cons_lid
                               && may_drop_implicits args) ->
      (match filter_pattern_imp args with
       | [(hd, false); (tl, false)] ->
         let hd' = aux hd (Some false) in
         (match aux tl (Some false) with
          | { pat = A.PatList tl'; prange = p } -> A.mk_pattern (A.PatList (hd' :: tl')) p
          | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
       | args' ->
         E.log_issue p.p (E.Warning_ConsAppliedExplicitArgs,
           (Util.format1 "Prims.Cons applied to %s explicit arguments"
             (string_of_int <| List.length args')));
         resugar_plain_pat_cons fv args)

    | Pat_cons(fv, _, args) when (is_tuple_constructor_lid fv.fv_name.v
                               && may_drop_implicits args) ->
      let args =
        args |>
        List.filter_map (fun (p, is_implicit) ->
            if is_implicit then None else Some (aux p (Some false))) in
      let is_dependent_tuple = C.is_dtuple_data_lid' fv.fv_name.v in
      mk (A.PatTuple (args, is_dependent_tuple))

    | Pat_cons({fv_qual=Some (Record_ctor(name, fields))}, _, args) ->
      // reverse the fields and args list to match them since the args added by the type checker
      // are inserted in the front of the args list.
      let fields = fields |> List.map (fun f -> FStar.Ident.lid_of_ids [f]) |> List.rev in
      let args = args |> List.map (fun (p, b) -> aux p (Some b)) |> List.rev in
      // make sure the fields and args are of the same length.
      let rec map2 l1 l2  = match (l1, l2) with
        | ([], []) -> []
        | ([], hd::tl) -> [] (* new args could be added by the type checker *)
        | (hd::tl, []) -> (hd, mk (A.PatWild (None, []))) :: map2 tl [] (* no new fields should be added*)
        | (hd1::tl1, hd2::tl2) -> (hd1, hd2) :: map2 tl1 tl2
      in
      // reverse back the args list
      let args = map2 fields args |> List.rev in
      mk (A.PatRecord(args))

    | Pat_cons (fv, _, args) ->
      resugar_plain_pat_cons fv args

    | Pat_var v ->
      // both A.PatTvar and A.PatVar are desugared to S.Pat_var. A PatTvar in the original file coresponds
      // to some type variable which is implicitly bound to the enclosing toplevel declaration.
      // When resugaring it will be just a normal (explicitly bound) variable.
      begin match string_to_op (string_of_id v.ppname) with
       | Some (op, _) -> mk (A.PatOp (Ident.mk_ident (op, (range_of_id v.ppname))))
       | None -> resugar_bv_as_pat' env v (to_arg_qual imp_opt) branch_bv None
      end

    // FIXME: detect unused patterns
    (* | Pat_wild _ -> mk (A.PatWild (to_arg_qual imp_opt, [])) *)

    | Pat_dot_term _ -> mk (A.PatWild (Some A.Implicit, []))
  in
  aux p None
// FIXME inspect uses of resugar_arg_qual and resugar_imp
(* If resugar_arg_qual returns None, the corresponding binder should *not* be resugared *)
and resugar_bqual env (q:S.bqual) : option (option A.arg_qualifier) =
  match q with
  | None -> Some None
  | Some (S.Implicit b) ->
    (* TODO : set an option to print these inaccessible patterns at least with a comment *)
    if b then None
    else Some (Some A.Implicit)
  | Some S.Equality -> Some (Some A.Equality)
  | Some (S.Meta t) when U.is_fvar C.tcresolve_lid t ->
    Some (Some (A.TypeClassArg))
  | Some (S.Meta t) ->
    Some (Some (A.Meta (resugar_term' env t)))

and resugar_aqual env (q:S.aqual) : A.imp =
  match q with
  | None -> A.Nothing
  | Some a -> if a.aqual_implicit then A.Hash else A.Nothing

let resugar_qualifier : S.qualifier -> option A.qualifier = function
  | S.Assumption -> Some A.Assumption
  | S.InternalAssumption -> None
  | S.New -> Some A.New
  | S.Private -> Some A.Private
  | S.Unfold_for_unification_and_vcgen -> Some A.Unfold_for_unification_and_vcgen
  (* TODO : Find the correct option to display this *)
  | Visible_default -> if true then None else Some A.Visible
  | S.Irreducible -> Some A.Irreducible
  | S.Inline_for_extraction -> Some A.Inline_for_extraction
  | S.NoExtract -> Some A.NoExtract
  | S.Noeq -> Some A.Noeq
  | S.Unopteq -> Some A.Unopteq
  | S.TotalEffect -> Some A.TotalEffect
  (* TODO : Find the correct option to display this *)
  | S.Logic -> if true then None else Some A.Logic
  | S.Reifiable -> Some A.Reifiable
  | S.Reflectable _ -> Some A.Reflectable
  | S.Discriminator _ -> None
  | S.Projector _ -> None
  | S.RecordType _ -> None
  | S.RecordConstructor _ -> None
  | S.Action _ -> None
  | S.ExceptionConstructor -> None
  | S.HasMaskedEffect -> None
  | S.Effect -> Some A.Effect_qual
  | S.OnlyName -> None


let resugar_pragma = function
  | S.SetOptions s -> A.SetOptions s
  | S.ResetOptions s -> A.ResetOptions s
  | S.PushOptions s -> A.PushOptions s
  | S.PopOptions -> A.PopOptions
  | S.RestartSolver -> A.RestartSolver
  | S.PrintEffectsGraph -> A.PrintEffectsGraph

let resugar_typ env datacon_ses se : sigelts * A.tycon =
  match se.sigel with
  | Sig_inductive_typ {lid=tylid;us=uvs;params=bs;t;ds=datacons} ->
      let current_datacons, other_datacons = datacon_ses |> List.partition (fun se -> match se.sigel with
        | Sig_datacon {ty_lid=inductive_lid} -> lid_equals inductive_lid tylid
        | _ -> failwith "unexpected" )
      in
      assert (List.length current_datacons = List.length datacons) ;
      let bs =
        if (Options.print_implicits())
        then bs
        else filter_imp_bs bs in
      let bs = bs |> map_opt (fun b -> resugar_binder' env b t.pos) in
      let tyc =
        if se.sigquals |> BU.for_some (function | RecordType _ -> true | _ -> false)
        then
          (* Resugar as a record *)
          let resugar_datacon_as_fields fields se = match se.sigel with
            | Sig_datacon {us=univs; t=term; num_ty_params=num} ->
              (* Todo: resugar univs *)
              begin match (SS.compress term).n with
                | Tm_arrow {bs} ->
                  let mfields =
                    bs
                    |> List.collect (fun b ->
                          match resugar_bqual env b.binder_qual with
                          | None -> [] //inaccessible argument
                          | Some q ->
                           [(bv_as_unique_ident b.binder_bv, q, b.binder_attrs |> List.map (resugar_term' env), resugar_term' env b.binder_bv.sort)]) in
                  mfields@fields
                | _ -> failwith "unexpected"
              end
            | _ -> failwith "unexpected"
          in
          let fields =  List.fold_left resugar_datacon_as_fields [] current_datacons in
          A.TyconRecord(ident_of_lid tylid, bs, None, map (resugar_term' env) se.sigattrs, fields)
        else
          (* Resugar as a variant *)
          let resugar_datacon constructors se = match se.sigel with
            | Sig_datacon {lid=l; us=univs; t=term; num_ty_params=num} ->
              (* Todo: resugar univs *)
              let c = (ident_of_lid l, Some (VpArbitrary (resugar_term' env term)), map (resugar_term' env) se.sigattrs)  in
              c::constructors
            | _ -> failwith "unexpected"
          in
          let constructors =  List.fold_left resugar_datacon [] current_datacons in
          A.TyconVariant(ident_of_lid tylid, bs, None, constructors)
      in
      other_datacons, tyc
  | _ -> failwith "Impossible : only Sig_inductive_typ can be resugared as types"

let mk_decl r q d' =
  {
    d = d' ;
    drange = r ;
    quals = List.choose resugar_qualifier q ;
    (* TODO : are these stocked up somewhere ? *)
    attrs = [] ;
  }

let decl'_to_decl se d' =
  mk_decl se.sigrng se.sigquals d'

let resugar_tscheme'' env name (ts:S.tscheme) =
  let (univs, typ) = ts in
  let name = I.mk_ident (name, typ.pos) in
  mk_decl typ.pos [] (A.Tycon(false, false, [(A.TyconAbbrev(name, [], None, resugar_term' env typ))]))

let resugar_tscheme' env (ts:S.tscheme) =
  resugar_tscheme'' env "tscheme" ts

let resugar_wp_eff_combinators env for_free combs =
  let resugar_opt name tsopt =
    match tsopt with
    | Some ts -> [resugar_tscheme'' env name ts]
    | None -> [] in

  let repr = resugar_opt "repr" combs.repr in
  let return_repr = resugar_opt "return_repr" combs.return_repr in
  let bind_repr = resugar_opt "bind_repr" combs.bind_repr in

  if for_free then repr@return_repr@bind_repr
  else
    (resugar_tscheme'' env "ret_wp" combs.ret_wp)::
    (resugar_tscheme'' env "bind_wp" combs.bind_wp)::
    (resugar_tscheme'' env "stronger" combs.stronger)::
    (resugar_tscheme'' env "if_then_else" combs.if_then_else)::
    (resugar_tscheme'' env "ite_wp" combs.ite_wp)::
    (resugar_tscheme'' env "close_wp" combs.close_wp)::
    (resugar_tscheme'' env "trivial" combs.trivial)::
    (repr@return_repr@bind_repr)

let resugar_layered_eff_combinators env combs =
  let resugar name (ts, _, _) = resugar_tscheme'' env name ts in
  let resugar2 name (ts, _) = resugar_tscheme'' env name ts in

  (resugar2 "repr"         combs.l_repr)::
  (resugar2 "return"       combs.l_return)::
  (resugar  "bind"         combs.l_bind)::
  (resugar  "subcomp"      combs.l_subcomp)::
  (resugar  "if_then_else" combs.l_if_then_else)::[]

let resugar_combinators env combs =
  match combs with
  | Primitive_eff combs -> resugar_wp_eff_combinators env false combs
  | DM4F_eff combs -> resugar_wp_eff_combinators env true combs
  | Layered_eff combs -> resugar_layered_eff_combinators env combs

let resugar_eff_decl' env r q ed =
  let resugar_action d for_free =
    let action_params = SS.open_binders d.action_params in
    let bs, action_defn = SS.open_term action_params d.action_defn in
    let bs, action_typ = SS.open_term action_params d.action_typ in
    let action_params =
      if (Options.print_implicits())
      then action_params
      else filter_imp_bs action_params in
    let action_params = action_params |> map_opt (fun b -> resugar_binder' env b r) |> List.rev in
    let action_defn = resugar_term' env action_defn in
    let action_typ = resugar_term' env action_typ in
    if for_free then
      let a = A.Construct ((I.lid_of_str "construct"), [(action_defn, A.Nothing);(action_typ, A.Nothing)]) in
      let t = A.mk_term a r A.Un in
      mk_decl r q (A.Tycon(false, false, [(A.TyconAbbrev(ident_of_lid d.action_name, action_params, None, t ))]))
    else
      mk_decl r q (A.Tycon(false, false, [(A.TyconAbbrev(ident_of_lid d.action_name, action_params, None, action_defn))]))
  in
  let eff_name = ident_of_lid ed.mname in
  let eff_binders, eff_typ =
    let sig_ts = U.effect_sig_ts ed.signature in
    SS.open_term ed.binders (sig_ts |> snd) in
  let eff_binders =
    if (Options.print_implicits())
    then eff_binders
    else filter_imp_bs eff_binders in
  let eff_binders = eff_binders |> map_opt (fun b -> resugar_binder' env b r) |> List.rev in
  let eff_typ = resugar_term' env eff_typ in

  let mandatory_members_decls = resugar_combinators env ed.combinators in

  let actions = ed.actions |> List.map (fun a -> resugar_action a false) in
  let decls = mandatory_members_decls@actions in
  mk_decl r q (A.NewEffect(DefineEffect(eff_name, eff_binders, eff_typ, decls)))

let resugar_sigelt' env se : option A.decl =
  match se.sigel with
  | Sig_bundle {ses} ->
    let decl_typ_ses, datacon_ses = ses |> List.partition
      (fun se -> match se.sigel with
        | Sig_inductive_typ _ | Sig_declare_typ _ -> true
        | Sig_datacon _ -> false
        | _ -> failwith "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"
      )
    in
    let retrieve_datacons_and_resugar (datacon_ses, tycons) se =
      let datacon_ses, tyc = resugar_typ env datacon_ses se in
      datacon_ses, tyc::tycons
    in
    let leftover_datacons, tycons = List.fold_left retrieve_datacons_and_resugar (datacon_ses, []) decl_typ_ses in
    begin match leftover_datacons with
      | [] -> //true
        (* TODO : documentation should be retrieved from the desugaring environment at some point *)
        Some (decl'_to_decl se (Tycon (false, false, tycons)))
      | [se] ->
        //assert (se.sigquals |> BU.for_some (function | ExceptionConstructor -> true | _ -> false));
        (* Exception constructor declaration case *)
        begin match se.sigel with
        | Sig_datacon {lid=l} ->
          Some (decl'_to_decl se (A.Exception (ident_of_lid l, None)))
        | _ -> failwith "wrong format for resguar to Exception"
        end
      | _ ->
        failwith "Should not happen hopefully"
    end

  | Sig_fail _ ->
    None

  | Sig_let {lbs} ->
    if (se.sigquals |> BU.for_some (function S.Projector(_,_) | S.Discriminator _ -> true | _ -> false)) then
      None
    else
      let mk e = S.mk e se.sigrng in
      let dummy = mk Tm_unknown in
      (* This function turns each resolved top-level lid being defined into an
       * ident without a path, so it gets printed correctly. *)
      let nopath_lbs ((is_rec, lbs) : letbindings) : letbindings =
        let nopath fv = lid_as_fv (lid_of_ids [ident_of_lid (lid_of_fv fv)]) None in
        let lbs = List.map (fun lb ->  { lb with lbname = Inr (nopath <| right lb.lbname)} ) lbs in
        (is_rec, lbs)
      in
      let lbs = nopath_lbs lbs in
      let desugared_let = mk (Tm_let {lbs; body=dummy}) in
      let t = resugar_term' env desugared_let in
      begin match t.tm with
        | A.Let(isrec, lets, _) ->
          Some (decl'_to_decl se (TopLevelLet (isrec, List.map snd lets)))
        | _ -> failwith "Should not happen hopefully"
      end

  | Sig_assume {lid; phi=fml} ->
    Some (decl'_to_decl se (Assume (ident_of_lid lid, resugar_term' env fml)))

  | Sig_new_effect ed ->
    Some (resugar_eff_decl' env se.sigrng se.sigquals ed)

  | Sig_sub_effect e ->
    let src = e.source in
    let dst = e.target in
    let lift_wp = match e.lift_wp with
      | Some (_, t) ->
          Some (resugar_term' env t)
      | _ -> None
    in
    let lift = match e.lift with
      | Some (_, t) ->
          Some (resugar_term' env t)
      | _ -> None
    in
    let op = match (lift_wp, lift) with
      | Some t, None -> A.NonReifiableLift t
      | Some wp, Some t -> A.ReifiableLift (wp, t)
      | None, Some t -> A.LiftForFree t
      | _ -> failwith "Should not happen hopefully"
    in
    Some (decl'_to_decl se (A.SubEffect({msource=src; mdest=dst; lift_op=op; braced=false})))

  | Sig_effect_abbrev {lid; us=vs; bs; comp=c; cflags=flags} ->
    let bs, c = SS.open_comp bs c in
    let bs =
      if (Options.print_implicits())
      then bs
      else filter_imp_bs bs in
    let bs = bs |> map_opt (fun b -> resugar_binder' env b se.sigrng) in
    Some (decl'_to_decl se (A.Tycon(false, false, [A.TyconAbbrev(ident_of_lid lid, bs, None, resugar_comp' env c)])))

  | Sig_pragma p ->
    Some (decl'_to_decl se (A.Pragma (resugar_pragma p)))

  | Sig_declare_typ {lid; us=uvs; t} ->
    if (se.sigquals |> BU.for_some (function S.Projector(_,_) | S.Discriminator _ -> true | _ -> false)) then
      None
    else
      let t' =
        if not (Options.print_universes ()) || isEmpty uvs then resugar_term' env t
        else
          let uvs, t = SS.open_univ_vars uvs t in
          let universes = universe_to_string uvs in
          label universes (resugar_term' env t)
      in
      Some (decl'_to_decl se (A.Val (ident_of_lid lid,t')))

  | Sig_splice {is_typed; lids=ids; tac=t} ->
    Some (decl'_to_decl se (A.Splice (is_typed, List.map (fun l -> ident_of_lid l) ids, resugar_term' env t)))

  (* Already desugared in one of the above case or non-relevant *)
  | Sig_inductive_typ _
  | Sig_datacon _ -> None

  | Sig_polymonadic_bind {m_lid=m; n_lid=n; p_lid=p; tm=(_, t)} ->
    Some (decl'_to_decl se (A.Polymonadic_bind (m, n, p, resugar_term' env t)))

  | Sig_polymonadic_subcomp {m_lid=m; n_lid=n; tm=(_, t)} ->
    Some (decl'_to_decl se (A.Polymonadic_subcomp (m, n, resugar_term' env t)))

(* Old interface: no envs *)

let empty_env = DsEnv.empty_env FStar.Parser.Dep.empty_deps //dep graph not needed for resugaring

let noenv (f: DsEnv.env -> 'a) : 'a =
  f empty_env

let resugar_term (t : S.term) : A.term =
  noenv resugar_term' t

let resugar_sigelt se : option A.decl =
  noenv resugar_sigelt' se

let resugar_comp (c:S.comp) : A.term =
  noenv resugar_comp' c

let resugar_pat (p:S.pat) (branch_bv: Set.set bv) : A.pattern =
  noenv resugar_pat' p branch_bv

let resugar_binder (b:S.binder) r : option A.binder =
  noenv resugar_binder' b r

let resugar_tscheme (ts:S.tscheme) =
  noenv resugar_tscheme' ts

let resugar_eff_decl r q ed =
  noenv resugar_eff_decl' r q ed

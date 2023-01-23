module STLC.Core
module T = FStar.Tactics
module R = FStar.Reflection
module L = FStar.List.Tot
module RT = Refl.Typing

type linearity = 
  | Zero | One | Any

and stlc_ty =
  | TUnit
  | TArrow : linearity -> stlc_ty -> stlc_ty -> stlc_ty

let var = nat
let index = nat

noeq
type stlc_exp =
  | EUnit : stlc_exp
  | EBVar : index -> stlc_exp
  | EVar  : var -> stlc_exp
  | ELam  : stlc_ty -> stlc_exp -> stlc_exp
  | EApp  : stlc_exp -> stlc_exp -> stlc_exp

let rec size (e:stlc_exp) 
  : nat
  = match e with
    | EUnit
    | EBVar _ 
    | EVar _ -> 1
    | ELam _ e -> 1 + size e
    | EApp e1 e2 -> 1 + size e1 + size e2

let rec ln' (e:stlc_exp) (n:int)
  : bool
  = match e with
    | EUnit
    | EVar _ -> true
    | EBVar m -> m <= n
    | ELam _ e -> ln' e (n + 1)
    | EApp e1 e2 -> ln' e1 n && ln' e2 n

let ln e = ln' e (-1)

let rec open_exp' (e:stlc_exp) (v:var) (n:index)
  : e':stlc_exp { size e == size e'}
  = match e with
    | EUnit -> EUnit
    | EVar m -> EVar m
    | EBVar m -> if m = n then EVar v else EBVar m
    | ELam t e -> ELam t (open_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (open_exp' e1 v n) (open_exp' e2 v n)

let rec close_exp' (e:stlc_exp) (v:var) (n:nat)
  : e':stlc_exp { size e == size e'}
  = match e with
    | EUnit -> EUnit
    | EVar m -> if m = v then EBVar n else EVar m
    | EBVar m -> EBVar m
    | ELam t e -> ELam t (close_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (close_exp' e1 v n) (close_exp' e2 v n)

let open_exp e v = open_exp' e v 0
let close_exp e v = close_exp' e v 0

let rec open_close' (e:stlc_exp) (x:var) (n:nat { ln' e (n - 1) })
  : Lemma (open_exp' (close_exp' e x n) x n == e)
  = match e with
    | EUnit -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | ELam _ e -> open_close' e x (n + 1)
    | EApp e1 e2 -> 
      open_close' e1 x n; 
      open_close' e2 x n

let open_close (e:stlc_exp) (x:var)
  : Lemma 
    (requires ln e)
    (ensures open_exp (close_exp e x) x == e)
    [SMTPat (open_exp (close_exp e x) x)]
  = open_close' e x 0

let rec open_exp_ln (e:stlc_exp) (v:var) (n:index) (m:int)
  : Lemma 
    (requires ln' e n /\
              m == n - 1)
    (ensures ln' (open_exp' e v n) m)
    [SMTPat (ln' e n);
     SMTPat (ln' (open_exp' e v n) m)]
  = match e with
    | EUnit -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | ELam _ e -> open_exp_ln e v (n + 1) (m + 1)
    | EApp e1 e2 -> open_exp_ln e1 v n m; open_exp_ln e2 v n m

let rec close_exp_ln (e:stlc_exp) (v:var) (n:nat)
  : Lemma 
    (requires ln' e (n - 1))
    (ensures ln' (close_exp' e v n) n)
    [SMTPat (ln' (close_exp' e v n) n)]
  = match e with
    | EUnit -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | ELam _ e -> close_exp_ln e v (n + 1)
    | EApp e1 e2 -> close_exp_ln e1 v n; close_exp_ln e2 v n
    



let stlc_env = list (var & (linearity & stlc_ty))

let lookup (e:list (var & 'a)) (x:var)
  : option 'a
  = L.assoc x e

let max (n1 n2:nat) = if n1 < n2 then n2 else n1

let rec fresh (e:list (var & 'a))
  : var
  = match e with
    | [] -> 0
    | hd :: tl -> 
      max (fresh tl) (fst hd) + 1

let rec fresh_not_mem (e:list (var & 'a)) (elt: (var & 'a))
  : Lemma (ensures L.memP elt e ==> fresh e > fst elt)
  = match e with
    | [] -> ()
    | hd :: tl -> fresh_not_mem tl elt
  
let rec lookup_mem (e:list (var & 'a)) (x:var)
  : Lemma
    (requires Some? (lookup e x))
    (ensures exists elt. L.memP elt e /\ fst elt == x)
  = match e with
    | [] -> ()
    | hd :: tl -> 
      match lookup tl x with
      | None -> assert (L.memP hd e)
      | _ -> 
        lookup_mem tl x;
        eliminate exists elt. L.memP elt tl /\ fst elt == x
        returns _
        with _ . ( 
          introduce exists elt. L.memP elt e /\ fst elt == x
          with elt
          and ()
        )

let fresh_is_fresh (e:list (var & 'a))
  : Lemma (None? (lookup e (fresh e)))
  =  match lookup e (fresh e) with
     | None -> ()
     | Some _ ->
       lookup_mem e (fresh e);
       FStar.Classical.forall_intro (fresh_not_mem e)

// let env_use_var (e: stlc_env)

// noeq type env_app (l: linearity): stlc_env -> stlc_env -> stlc_env -> Type
//  = | EA_Nil: env_app [] [] []
//    | EA_Cons:
//      -> e_lam:stlc_env
//      -> e_arg:stlc_env
//      -> e_res:stlc_env
//      -> l_arg:linearity
//      -> l_lam:linearity
//      -> t1:stlc_ty
//      -> env_app l e_lam e_arg e_res
//      -> env_app l ()

let mul_lin (l1 l2: linearity): linearity
  = match l1, l2 with
  | Zero, _ | _, Zero -> Zero
  | One, One -> One
  | _ -> Any
  
let add_lin (l1 l2: linearity): linearity
  = match l1, l2 with
  | Zero, x | x, Zero -> x
  | _ -> Any

open FStar.List.Tot

let forget_lin (e: stlc_env): list (var * stlc_ty)
  = map (fun (v, (_, t)) -> (v, t)) e

let ( ≌ ) (e1 e2: stlc_env) = forget_lin e1 = forget_lin e2

let rec mul_env (l: linearity) (e: stlc_env): r: stlc_env {e ≌ r}
  = admit ();
    L.map (fun (v, (l', t)) -> (v, (mul_lin l l', t))) e
    
let rec union_env (e1: stlc_env) 
                  (e2: stlc_env {e1 ≌ e2})
  : r: option stlc_env {match r with | Some r -> e1 ≌ r | None -> True}
  = match e1, e2 with
  | (v1, (l1, t1))::te1, (v2, (l2, t2))::te2 ->
       if v1 = v2 && t1 = t2
       then ( match union_env te1 te2 with
            | Some tres ->
                Some ((v1, (add_lin l1 l2, t1))::tres)
            | None -> None
            )
       else None
  | [], [] -> Some []
  | _ -> None

// let x 
//   = let e_f = [ (0, (One, TArrow One TUnit TUnit))
//               ; (1, (Zero, TUnit))
//               ] in
//     let e_x = [ (0, (Zero, TArrow One TUnit TUnit))
//               ; (1, (One, TUnit))
//               ] in
//     union_env e_f e_x //(mul_env One e_x)

[@@erasable]
noeq
type stlc_typing : stlc_env -> stlc_exp -> stlc_ty -> Type =
  | T_Unit :
      g:stlc_env ->
      stlc_typing g EUnit TUnit
  
  | T_Var  :
      g:stlc_env ->
      x:var { match lookup g x with
            | Some (Zero, _) | None -> False
            | _ -> True
            } ->
      stlc_typing g (EVar x) (snd (Some?.v (lookup g x)))

  | T_Lam  :
      g:stlc_env ->
      lin:linearity ->
      t:stlc_ty ->
      e:stlc_exp ->
      t':stlc_ty ->
      x:var { None? (lookup g x) } ->
      stlc_typing ((x,(lin,t))::g) (open_exp e x) t' ->
      stlc_typing g (ELam t e) (TArrow lin t t')

  | T_App  :
      l:linearity ->
      g_lam:stlc_env ->
      g_arg:stlc_env { g_lam ≌ g_arg } ->
      g_res:stlc_env { g_res ≌ g_lam /\ Some g_res == union_env g_lam (mul_env l g_arg) } ->
      
      e1:stlc_exp ->
      e2:stlc_exp ->
      t:stlc_ty ->
      t':stlc_ty ->
      stlc_typing g_lam e1 (TArrow l t t') ->
      stlc_typing g_arg e2 t ->
      stlc_typing (g_res) (EApp e1 e2) t'

let tun = R.pack_ln R.Tv_Unknown


let lin_to_string =
  function | Zero -> "0"
           | One -> "1"
           | Any -> "ω"

let rec ty_to_string' should_paren (t:stlc_ty)
  : Tot string (decreases t)
  = match t with
    | TUnit -> "unit"
    | TArrow l t1 t2 -> 
      let t = Printf.sprintf "%s -%s-> %s"
                 (ty_to_string' true t1)
                 (lin_to_string l)
                 (ty_to_string' false t2) in
      if should_paren 
      then Printf.sprintf "(%s)" t
      else t
      
let ty_to_string = ty_to_string' false

// let rec zip (l1: list 'a) (l2: list 'b) // TODO, same lengths
//   = match l1, l2 with
//     | hd1::tl1, hd2::tl2 -> (hd1,hd2)::(zip tl1 tl2)
//     | _ -> []

// let combine_env 
//     (env_type:list (var & stlc_ty))
//     (env_lin:list (var & linearity))
//     // TODO check sanity
//   = zip (map fst env_type) (zip (map snd env_lin) (map snd env_type))

let map'' f l = map (fun (v, t) -> (v, (f v t, t))) l

let rec lemma_map (g:list (var & stlc_ty)) f
  : Lemma (forget_lin (map'' f g) == g)
  // : Lemma (forget_lin (map (fun (v, t) -> (v, (f v t, t))) g) == g)
  = match g with
  | [] -> ()
  | hd::tl -> lemma_map tl f

let map' f l
  : r:stlc_env {forget_lin r == l} 
  = let r: stlc_env = map'' f l in
    lemma_map l f;
    r

let rec check //(g:R.env)
              (sg:list (var & stlc_ty))
              (e:stlc_exp { ln e })
  : T.Tac (el_res:stlc_env {forget_lin el_res == sg} & t:stlc_ty & stlc_typing el_res e t)
  = match e with
    | EUnit ->
      // let g' = map (fun (v, t) -> (v, (Zero, t))) sg in
      let g': stlc_env = map' (fun v t -> Zero) sg in
      let d = T_Unit g' in
      (| g', TUnit, d |)
    
    | EVar n ->
      begin
      // let g' = map (fun (v, t) -> (v, ((if v = n then One else Zero), t))) sg in
      let g' = map' (fun v t -> if v = n then One else Zero) sg in
      match lookup g' n with
      | Some (One, t) ->
        let d = T_Var g' n in
        (| g', t, d |)
      | Some _ -> T.fail "IMPOSSIBLE" // todo prove me
      | _ -> T.fail "Ill-typed"
      end

    | ELam t e ->
      let x = fresh sg in
      fresh_is_fresh sg;
      
      let (| g', tbody, dbody |) = check  ((x,t)::sg) (open_exp e x) in
      begin match g' with
      | (x',(l,t'))::tg' -> 
        if not (x' = x && t' = t) then T.fail "Aarrrrgh";
        if Some? (lookup tg' x) then T.fail "todo, Aarrrrgh";
        (| tg',
           TArrow l t tbody, 
           T_Lam tg' l t e tbody x dbody |)
      | _ -> T.fail ""
      end
      
    | EApp e1 e2 ->
      let (| g1, t1, d1 |) = check  sg e1 in
      let (| g2, t2, d2 |) = check  sg e2 in
      if not (g1 ≌ g2) then T.fail "imcompatible envs";
      match t1 with
      | TArrow l t2' t ->
        if t2' = t2
        then match union_env g1 (mul_env l g2) with
           | Some g_res -> (| g_res, t, T_App l g1 g2 g_res e1 e2 t2 t d1 d2 |)
           | None -> T.fail "union_env, None"
        else T.fail 
               (Printf.sprintf "Expected argument of type %s got %s"
                               (ty_to_string t2')
                               (ty_to_string t2))
      | _ -> 
        T.fail (Printf.sprintf "Expected an arrow, got %s"
                               (ty_to_string t1))

let rec elab_ty (t:stlc_ty) 
  : R.term 
  = let open R in
    match t with
    | TUnit -> 
      R.pack_ln (R.Tv_FVar (R.pack_fv unit_lid))
      
    | TArrow _ t1 t2 ->
      let t1 = elab_ty t1 in
      let t2 = elab_ty t2 in

      R.pack_ln 
        (R.Tv_Arrow
          (RT.mk_binder "x" 0 t1 R.Q_Explicit)
          (R.pack_comp (C_Total t2)))
  
let rec elab_exp (e:stlc_exp)
  : Tot R.term (decreases (size e))
  = let open R in
    match e with
    | EUnit -> 
      pack_ln (Tv_Const C_Unit)

    | EBVar n -> 
      let bv = R.pack_bv (RT.make_bv n tun) in
      R.pack_ln (Tv_BVar bv)
      
    | EVar n ->
      // tun because type does not matter at a use site
      let bv = R.pack_bv (RT.make_bv n tun) in
      R.pack_ln (Tv_Var bv)

    | ELam t e ->
      let t = elab_ty t in
      let e = elab_exp e in
      R.pack_ln (Tv_Abs (RT.mk_binder "x" 0 t R.Q_Explicit) e)
             
    | EApp e1 e2 ->
      let e1 = elab_exp e1 in
      let e2 = elab_exp e2 in
      R.pack_ln (Tv_App e1 (e2, Q_Explicit))

let extend_env_l (g:R.env) (sg:stlc_env) = 
  L.fold_right (fun (x, t) g -> RT.extend_env g x (elab_ty t)) (forget_lin sg) g
  
let rec extend_env_l_lookup_bvar (g:R.env) (sg:stlc_env) (x:var)
  : Lemma 
    (requires (forall x. RT.lookup_bvar g x == None))
    (ensures (
      match lookup sg x with
      | Some (_, t) -> RT.lookup_bvar (extend_env_l g sg) x == Some (elab_ty t)
      | None -> RT.lookup_bvar (extend_env_l g sg) x == None))
    (decreases sg)
    [SMTPat (RT.lookup_bvar (extend_env_l g sg) x)]
  = match sg with
    | [] -> ()
    | hd :: tl -> extend_env_l_lookup_bvar g tl x

open FStar.Calc

//key lemma about STLC types: Their elaborations are closed
let rec stlc_types_are_closed_core (ty:stlc_ty) (x:RT.open_or_close) (n:nat)
  : Lemma (ensures RT.open_or_close_term' (elab_ty ty) x n == elab_ty ty)
          (decreases ty)
          [SMTPat (RT.open_or_close_term' (elab_ty ty) x n)]

  = match ty with
    | TUnit -> ()
    | TArrow _ t1 t2 ->
      stlc_types_are_closed_core t1 x n;
      stlc_types_are_closed_core t2 x (n + 1)

let stlc_types_are_closed1 (ty:stlc_ty) (v:R.term)
  : Lemma (RT.open_with (elab_ty ty) v == elab_ty ty)
          [SMTPat (RT.open_with (elab_ty ty) v)]
  = stlc_types_are_closed_core ty (RT.OpenWith v) 0;
    RT.open_with_spec (elab_ty ty) v

let stlc_types_are_closed2 (ty:stlc_ty) (x:R.var)
  : Lemma (RT.close_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.close_term (elab_ty ty) x)]
  = stlc_types_are_closed_core ty (RT.CloseVar x) 0;
    RT.close_term_spec (elab_ty ty) x

let stlc_types_are_closed3 (ty:stlc_ty) (x:R.var)
  : Lemma (RT.open_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.open_term (elab_ty ty) x)]
  = stlc_types_are_closed_core ty (RT.OpenWith (RT.var_as_term x)) 0;
    RT.open_term_spec (elab_ty ty) x

let rec elab_open_commute' (e:stlc_exp) (x:var) (n:nat)
  : Lemma (ensures
              RT.open_or_close_term' (elab_exp e) (RT.open_with_var x) n ==
              elab_exp (open_exp' e x n))
          (decreases e)
  = match e with
    | EUnit -> ()
    | EBVar _ -> ()
    | EVar _ -> ()
    | EApp e1 e2 -> 
      elab_open_commute' e1 x n;
      elab_open_commute' e2 x n
    | ELam t e ->
      calc (==) {
        elab_exp (open_exp' (ELam t e) x n);
      (==) {}
        elab_exp (ELam t (open_exp' e x (n + 1)));      
      (==) {  }
        R.(pack_ln (Tv_Abs (RT.as_binder 0 (elab_ty t)) (elab_exp (open_exp' e x (n + 1)))));
      (==) { elab_open_commute' e x (n + 1) } 
        R.(pack_ln (Tv_Abs (RT.as_binder 0 (elab_ty t))
                           (RT.open_or_close_term' (elab_exp e) RT.(open_with_var x) (n + 1))));
      (==) { stlc_types_are_closed_core t (RT.open_with_var x) n }
        RT.open_or_close_term'
          R.(pack_ln (Tv_Abs (RT.as_binder 0 (elab_ty t)) (elab_exp e)))
          RT.(open_with_var x)
          n;
      }

let elab_open_commute (e:stlc_exp) (x:var)
  : Lemma (RT.open_term (elab_exp e) x == elab_exp (open_exp e x))
          [SMTPat (RT.open_term (elab_exp e) x)]
  = elab_open_commute' e x 0;
    RT.open_term_spec (elab_exp e) x

let rec extend_env_l_lookup_fvar (g:R.env) (sg:stlc_env) (fv:R.fv)
  : Lemma 
    (ensures
      RT.lookup_fvar (extend_env_l g sg) fv ==
      RT.lookup_fvar g fv)
    [SMTPat (RT.lookup_fvar (extend_env_l g sg) fv)]
  = match sg with
    | [] -> ()
    | hd::tl -> extend_env_l_lookup_fvar g tl fv
   
let rec elab_ty_soundness (g:RT.fstar_top_env)
                          (sg:stlc_env)
                          (t:stlc_ty)
  : GTot (RT.typing (extend_env_l g sg) (elab_ty t) (RT.tm_type RT.u_zero))
         (decreases t)
  = match t with
    | TUnit -> 
      RT.T_FVar _ RT.unit_fv
      
    | TArrow l t1 t2 ->
      let t1_ok = elab_ty_soundness g sg t1 in
      let x = fresh sg in
      fresh_is_fresh sg;
      let t2_ok = elab_ty_soundness g ((x, (l, t1))::sg) t2 in
      let arr_max 
        : RT.typing 
               (extend_env_l g sg)
               (elab_ty t)
               (RT.tm_type RT.(u_max u_zero u_zero))
            =  RT.T_Arrow _ x (elab_ty t1) (elab_ty t2) 
                          _ _ "x" R.Q_Explicit t1_ok t2_ok
      in
      RT.simplify_umax arr_max
  
let rec soundness (#sg:stlc_env) 
                  (#se:stlc_exp)
                  (#st:stlc_ty)
                  (dd:stlc_typing sg se st)
                  (g:RT.fstar_top_env)
  : GTot (RT.typing (extend_env_l g sg)
                    (elab_exp se)
                    (elab_ty st))
         (decreases dd)
  = match dd with
    | T_Unit _ ->
      RT.T_Const _ _ _ RT.CT_Unit

    | T_Var _ x ->
      RT.T_Var _ (R.pack_bv (RT.make_bv x tun))

    | T_Lam _ l t e t' x de ->
      let de : RT.typing (extend_env_l g ((x,(l,t))::sg))
                         (elab_exp (open_exp e x))
                         (elab_ty t')
            = soundness de g 
      in    
      let de : RT.typing (RT.extend_env (extend_env_l g sg) x (elab_ty t))
                         (elab_exp (open_exp e x))
                         (elab_ty t')
             = de
      in
      fresh_is_fresh sg;
      let dd
        : RT.typing (extend_env_l g sg)
                    (R.pack_ln (R.Tv_Abs (RT.as_binder 0 (elab_ty t)) (elab_exp e)))
                    (elab_ty (TArrow l t t'))
        = RT.T_Abs (extend_env_l g sg)
                   x
                   (elab_ty t) 
                   (elab_exp e)
                   (elab_ty t')
                   _
                   "x"
                   R.Q_Explicit
                   (elab_ty_soundness g sg t)
                   de
      in
      dd
    | T_App l g_lam g_arg g_res e1 e2 t t' d1 d2 ->
      let dt1 
        : RT.typing (extend_env_l g g_lam)
                    (elab_exp e1)
                    (elab_ty (TArrow l t t'))
        = soundness d1 g
      in
      let dt2
        : RT.typing (extend_env_l g g_arg)
                    (elab_exp e2)
                    (elab_ty t)
        = soundness d2 g
      in
      let dt :
        RT.typing (extend_env_l g g_res)
                  (elab_exp (EApp e1 e2))
                  (RT.open_with (elab_ty t') (elab_exp e2))
        = RT.T_App _ _ _ _ _ dt1 dt2
      in
      dt
  
let soundness_lemma (sg:stlc_env) 
                    (se:stlc_exp)
                    (st:stlc_ty)
                    (g:RT.fstar_top_env)
  : Lemma
    (requires stlc_typing sg se st)
    (ensures  RT.typing (extend_env_l g sg)
                        (elab_exp se)
                        (elab_ty st))
  = FStar.Squash.bind_squash 
      #(stlc_typing sg se st)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness dd g))

let main (src:stlc_exp) : RT.dsl_tac_t =
  fun g ->
  if ln src
  then
    let (| g', src_ty, d |) = check [] src in
    soundness_lemma [] src src_ty g;
    elab_exp src, elab_ty src_ty
  else T.fail "Not locally nameless"

let e = ELam TUnit (EBVar 0)
// let e = ELam TUnit (
//     EApp (
//          EApp (EVar 123) (EBVar 0)
//       ) (EBVar 0)
//   )

// let r: (el_res:stlc_env & t:stlc_ty & stlc_typing el_res e t) = _ by (
//   let r = check [(123, TArrow One TUnit (TArrow One TUnit TUnit))] e in
//   T.exact (quote r)
// )

(***** Tests *****)

// #set-options "--ugly"

%splice_t[foo] (main e)

#push-options "--no_smt"
let test_id () = assert (foo () == ()) by (T.compute ())
#pop-options

// let bar_s = (ELam TUnit (ELam TUnit (EBVar 1)))
// %splice_t[bar] (main bar_s)

// let baz_s : stlc_exp = EApp bar_s EUnit
// %splice_t[baz] (main bar_s)

module STLC.Core
module T = FStar.Tactics
module R = FStar.Reflection
module L = FStar.List.Tot
module RT = Refl.Typing

type stlc_ty =
  | TUnit
  | TLinArr : stlc_ty -> stlc_ty -> stlc_ty
  | TPair: stlc_ty -> stlc_ty -> stlc_ty
  | TBang: stlc_ty -> stlc_ty
  | TStar: stlc_ty -> stlc_ty

let var = nat
let index = nat

noeq
type stlc_exp =
  | EUnit : stlc_exp
  | EBVar : index -> stlc_exp
  | EVar  : var -> stlc_exp
  | ELam  : stlc_ty -> stlc_exp -> stlc_exp 
  | EApp  : stlc_exp -> stlc_exp -> stlc_exp
  
  | EPair : stlc_exp -> stlc_exp -> stlc_exp
  | EDPair: stlc_ty -> stlc_exp -> stlc_ty -> stlc_exp -> stlc_exp

  | EUnitElim: stlc_exp -> stlc_ty -> stlc_exp -> stlc_exp

  | EBang : stlc_exp -> stlc_exp
  | ELetBang: stlc_ty -> stlc_exp -> stlc_ty -> stlc_exp -> stlc_exp
  | EBorrow: stlc_exp -> stlc_exp
  | ECopy: stlc_ty -> stlc_exp -> stlc_ty -> stlc_exp -> stlc_exp
  | EUnique: stlc_exp -> stlc_exp

let rec size (e:stlc_exp) 
  : nat
  = match e with
    | EUnit
    | EBVar _ 
    | EVar _ -> 1
    | EBang e | EBorrow e | EUnique e | ELam _ e
           -> 1 + size e
    | EApp e1 e2 | EPair e1 e2 | EDPair _ e1 _ e2 | EUnitElim e1 _ e2 | ELetBang _ e1 _ e2 | ECopy _ e1 _ e2
           -> 1 + size e1 + size e2

let rec ln' (e:stlc_exp) (n:int)
  : bool
  = match e with
    | EUnit
    | EVar _ -> true
    | EBVar m -> m <= n
    
    | EBang e | EBorrow e | EUnique e
           -> ln' e n
    
    | ELam _ e -> ln' e (n + 1)
    
    | EUnitElim e1 _ e2
    | EApp e1 e2 | EPair e1 e2
           -> ln' e1 n && ln' e2 n
    | EDPair _ e1 _ e2 | ELetBang _ e1 _ e2 | ECopy _ e1 _ e2
           -> ln' e1 n && ln' e2 (n + 1)
           
let ln e = ln' e (-1)

let rec open_exp' (e:stlc_exp) (v:var) (n:index)
  : e':stlc_exp { size e == size e'}
  = match e with
    | EUnit -> EUnit
    | EVar m -> EVar m
    | EBVar m -> if m = n then EVar v else EBVar m
    | ELam t e -> ELam t (open_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (open_exp' e1 v n) (open_exp' e2 v n)
    
    | EBang   e -> EBang   (open_exp' e v n)
    | EBorrow e -> EBorrow (open_exp' e v n)
    | EUnique e -> EUnique (open_exp' e v n)
    | EUnitElim e1 t e2 -> EUnitElim (open_exp' e1 v n) t (open_exp' e2 v n)
    
    | EPair e1 e2 -> EPair (open_exp' e1 v n) (open_exp' e2 v n)
    | EDPair t1 e1 t2 e2 -> EDPair t1 (open_exp' e1 v n) t2 (open_exp' e2 v (n+1))
    | ELetBang t1 e1 t2 e2 -> ELetBang t1 (open_exp' e1 v n) t2 (open_exp' e2 v (n+1))
    | ECopy t1 e1 t2 e2 -> ECopy t1 (open_exp' e1 v n) t2 (open_exp' e2 v (n+1))

let rec close_exp' (e:stlc_exp) (v:var) (n:nat)
  : e':stlc_exp { size e == size e'}
  = match e with
    | EUnit -> EUnit
    | EVar m -> if m = v then EBVar n else EVar m
    | EBVar m -> EBVar m
    | ELam t e -> ELam t (close_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (close_exp' e1 v n) (close_exp' e2 v n)
    | EBang   e -> EBang   (close_exp' e v n)
    | EBorrow e -> EBorrow (close_exp' e v n)
    | EUnique e -> EUnique (close_exp' e v n)
    
    | EPair e1 e2 -> EPair (close_exp' e1 v n) (close_exp' e2 v n)
    | EDPair t1 e1 t2 e2 -> EDPair t1 (close_exp' e1 v n) t2 (close_exp' e2 v (n+1))
    | EUnitElim e1 t e2 -> EUnitElim (close_exp' e1 v n) t (close_exp' e2 v n)
    | ELetBang t1 e1 t2 e2 -> ELetBang t1 (close_exp' e1 v n) t2 (close_exp' e2 v (n+1))
    | ECopy t1 e1 t2 e2 -> ECopy t1 (close_exp' e1 v n) t2 (close_exp' e2 v (n+1))

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
    | EBang   e -> open_close' e x n
    | EBorrow e -> open_close' e x n
    | EUnique e -> open_close' e x n
    
    | EUnitElim e1 _ e2 -> open_close' e1 x n; open_close' e2 x n
    | EPair e1 e2 -> open_close' e1 x n; open_close' e2 x n
    | EDPair _ e1 _ e2 -> open_close' e1 x n; open_close' e2 x (n+1)
    | ELetBang _ e1 _ e2 -> open_close' e1 x n; open_close' e2 x (n+1)
    | ECopy _ e1 _ e2 -> open_close' e1 x n; open_close' e2 x (n+1)

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
    
    | EBang e | EBorrow e | EUnique e -> open_exp_ln e v n m
    
    | EPair e1 e2 | EUnitElim e1 _ e2 -> open_exp_ln e1 v n m; open_exp_ln e2 v n m
    | EDPair _ e1 _ e2 | ELetBang _ e1 _ e2 | ECopy _ e1 _ e2 
       -> open_exp_ln e1 v n m; open_exp_ln e2 v (n+1) (m+1)

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
    
    | EBang e | EBorrow e | EUnique e -> close_exp_ln e v n
    
    | EPair e1 e2 | EUnitElim e1 _ e2 -> close_exp_ln e1 v n; close_exp_ln e2 v n
    | EDPair _ e1 _ e2 | ELetBang _ e1 _ e2 | ECopy _ e1 _ e2 
       -> close_exp_ln e1 v n; close_exp_ln e2 v (n+1)

type is_linear = bool
let stlc_env = list (var & (is_linear & stlc_ty))

let lookup (e:list (var & 'a)) (x:var)
  : option 'a
  = L.assoc x e

let non_linear_env e = forall x. match lookup e x with
           | Some (l, _) -> l = false
           | None -> True
let rec is_non_linear_env (e:stlc_env): r:bool {
  r <==> ( forall x. match lookup e x with
           | Some (l, _) -> l = false
           | None -> True
       )
} = match e with
  | (_, (true, _))::_ -> false
  | (_, (false, _))::tl -> admit (); is_non_linear_env tl
  | [] -> true

// Non-linear
let stlc_env_nl = e:stlc_env {non_linear_env e}

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

open FStar.List.Tot

let forget_lin (g: stlc_env): list (var & stlc_ty)
  = map (fun (v, (_, t)) -> v, t) g

let (≡) g1 g2 = forget_lin g1 = forget_lin g2

let dom (e: stlc_env): list var = map fst e
let (∩) (#a:eqtype) (l1 l2: list a): list a
  = filter (fun x -> mem x l2) l1

let (⊕) (e1 e2: stlc_env): option stlc_env
  = if for_all (fun x -> 
         match lookup e1 x, lookup e2 x with
       | Some (false, t1), Some (false, t2) -> t1 = t2
       | _ -> false
       ) (dom e1 ∩ dom e2)
    then Some (e1 @ e2)
    else None

[@@erasable]
noeq
type stlc_typing : stlc_env -> stlc_exp -> stlc_ty -> Type =
  | T_Var:
    g:stlc_env {non_linear_env g} ->
    x:var {Some? (lookup g x)} ->
    stlc_typing g (EVar x) (snd (Some?.v (lookup g x)))

  | T_Lam:
    g:stlc_env ->
    x:var {None? (lookup g x)} ->
    tx:stlc_ty ->
    e:stlc_exp ->
    te:stlc_ty ->
    stlc_typing ((x,(true,tx))::g) (open_exp e x) te ->
    stlc_typing g (ELam te e) (TLinArr tx te)

  | T_App:
    g1:stlc_env ->
    g2:stlc_env ->
    g3:stlc_env {Some g3 == g1 ⊕ g2} ->
    e1:stlc_exp ->
    e2:stlc_exp ->
    t:stlc_ty ->
    t':stlc_ty ->
    stlc_typing g1 e1 (TLinArr t t') ->
    stlc_typing g2 e2 t ->
    stlc_typing g3 (EApp e1 e2) t'

  | BangIntro:
    g:stlc_env {non_linear_env g} ->
    e:stlc_exp ->
    t:stlc_ty ->
    stlc_typing g e t ->
    stlc_typing g (EBang e) (TBang t)

  | BangElim:
    g1:stlc_env ->
    g2:stlc_env ->
    g3:stlc_env {Some g3 == g1 ⊕ g2} ->
    x:var {None? (lookup g2 x)} ->
    t1:stlc_ty ->
    t2:stlc_ty ->
    e1:stlc_exp ->
    e2:stlc_exp ->
    stlc_typing g1 e1 (TBang t1) ->
    stlc_typing ((x,(false,t1))::g2) (open_exp e2 x) t2 ->
    stlc_typing g3 (ELetBang t1 e1 t2 e2) t2

  | BangDereliction:
    g:stlc_env ->
    x:var {None? (lookup g x)} ->
    tx:stlc_ty ->
    e:stlc_exp ->
    te:stlc_ty ->
    stlc_typing ((x,(true,tx))::g) (open_exp e x) te ->
    stlc_typing ((x,(false,tx))::g) (open_exp e x) te
    
  | T_Borrow:
    g:stlc_env ->
    e:stlc_exp ->
    t:stlc_ty ->
    stlc_typing g (EUnique e) (TStar t) ->
    stlc_typing g (EBorrow e) (TBang t)

  | T_Copy:
    g1:stlc_env ->
    g2:stlc_env ->
    g3:stlc_env {Some g3 == g1 ⊕ g2} ->
    x:var {None? (lookup g2 x)} ->
    t1:stlc_ty ->
    t2:stlc_ty ->
    e1:stlc_exp ->
    e2:stlc_exp ->
    stlc_typing g1 e1 (TBang t1) ->
    stlc_typing ((x,(false,TStar t1))::g2) (open_exp e2 x) (TBang t2) ->
    stlc_typing g3 (ECopy t1 e1 t2 e2) (TBang t2)

  | T_Nec:
    g:stlc_env {non_linear_env g} ->
    e:stlc_exp ->
    t:stlc_ty ->
    stlc_typing [] e t ->
    stlc_typing g (EUnique e) (TStar t)
  
  | T_Unit:
    g:stlc_env {non_linear_env g} ->
    stlc_typing g EUnit TUnit

  | T_UnitElim:
    g1:stlc_env ->
    g2:stlc_env ->
    g3:stlc_env {Some g3 == g1 ⊕ g2} ->
    e1:stlc_exp ->
    e2:stlc_exp ->
    t:stlc_ty ->
    stlc_typing g1 e1 TUnit ->
    stlc_typing g2 e2 t ->
    stlc_typing g3 (EUnitElim e1 t e2) t

  | T_PairIntro:
    g1:stlc_env ->
    g2:stlc_env ->
    g3:stlc_env {Some g3 == g1 ⊕ g2} ->
    e1:stlc_exp ->
    e2:stlc_exp ->
    t1:stlc_ty ->
    t2:stlc_ty ->
    stlc_typing g1 e1 t1 ->
    stlc_typing g2 e2 t2 ->
    stlc_typing g3 (EPair e1 e2) (TPair t1 t2)

  | T_PairElim:
    g1:stlc_env ->
    g2:stlc_env ->
    g3:stlc_env {Some g3 == g1 ⊕ g2} ->
    x:var {None? (lookup g2 x)} ->
    y:var {None? (lookup g2 y) /\ x <> y} ->
    t1:stlc_ty ->
    t2:stlc_ty ->
    t3:stlc_ty ->
    e1:stlc_exp ->
    e2:stlc_exp ->
    stlc_typing g1 e1 (TPair t1 t2) ->
    stlc_typing ((y,(true,TStar t2))::(x,(true,TStar t1))::g2) 
                (open_exp (open_exp e2 x) y)
                t3 ->
    stlc_typing g3 (EDPair t1 e1 t2 e2) t3

let tun = R.pack_ln R.Tv_Unknown

let rec ty_to_string' should_paren (t:stlc_ty)
  : Tot string (decreases t)
  = match t with
    | TUnit -> "unit"
    | TLinArr t1 t2 -> 
      let t = Printf.sprintf "%s ⊸ %s"
                 (ty_to_string' true t1)
                 (ty_to_string' false t2) in
      if should_paren 
      then Printf.sprintf "(%s)" t
      else t
    | TPair x y -> Printf.sprintf "(%s * %s)" (ty_to_string' true x) (ty_to_string' true y)
    | TBang x -> Printf.sprintf "!%s" (ty_to_string' true x)
    | TStar x -> Printf.sprintf "*%s" (ty_to_string' true x)

let ty_to_string = ty_to_string' false

let rec emap (f: var -> stlc_ty -> is_linear) 
         (l: list (var & stlc_ty))
         : r:stlc_env {
           forget_lin r == l
         } 
  = match l with
  | (v, t)::tl -> (v, (f v t, t))::emap f tl
  | [] -> []

let rec as_non_linear_env (l: list (var & stlc_ty))
                          : r:stlc_env{non_linear_env r /\ forget_lin r == l}
  = match l with
  | (v, t)::tl -> (v, (false, t))::as_non_linear_env tl
  | [] -> []

let some_of (x: option 'a): T.Tac 'a
  = match x with
  | Some x -> x
  | None   -> T.fail "Expected (Some _) got None"

let rec check (g:R.env)
              (sg:list (var & stlc_ty))
              (e:stlc_exp { ln e })
  : T.Tac ( r:stlc_env {forget_lin r == sg}
          & t:stlc_ty 
          & stlc_typing r e t)
  = match e with
    | EUnit ->
      let sg = as_non_linear_env sg in
      let d = T_Unit sg in
      (| sg, TUnit, d |)
    | EVar n ->
      let sg = as_non_linear_env sg in
      begin
      match lookup sg n with
      | None -> T.fail "Ill-typed"
      | Some (_, t) ->
        let d = T_Var sg n in
        (| sg, t, d |)
      end
    | EApp e1 e2 ->
      let (| g1, t1, d1 |) = check g sg e1 in
      let (| g2, t2, d2 |) = check g sg e2 in
      let g3 = some_of (g1 ⊕ g2) in
      (|g3, TLinArr t1 t2, T_App g1 g2 g3 e1 e2 t1 t2 d1 d2|)
    | _ -> admit ()
      
    | _ -> admit ()

    | ELam t e ->
      let x = fresh sg in
      fresh_is_fresh sg;
      let (| tbody, dbody |) = check g ((x,t)::sg) (open_exp e x) in
      (| TArrow t tbody, 
         T_Lam sg t e tbody x dbody |)
           
    | EApp e1 e2 ->
      let (| t1, d1 |) = check g sg e1 in
      let (| t2, d2 |) = check g sg e2 in
      match t1 with
      | TArrow t2' t ->
        if t2' = t2
        then (| t, T_App _ _ _ _ _ d1 d2 |)
        else T.fail 
               (Printf.sprintf "Expected argument of type %s got %s"
                               (ty_to_string t2')
                               (ty_to_string t2))
        
      | _ -> 
        T.fail (Printf.sprintf "Expected an arrow, got %s"
                               (ty_to_string t1))


let rec check (g:R.env)
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

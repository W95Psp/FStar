open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
  
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> normalize [] e t 
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string 
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g  ->
    let uu____68781 =
      let uu____68782 = FStar_Tactics_Types.goal_env g  in
      let uu____68783 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____68782 uu____68783  in
    FStar_Tactics_Types.goal_with_type g uu____68781
  
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun projectee  -> match projectee with | { tac_f;_} -> tac_f 
let mk_tac :
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f  -> { tac_f = f } 
let run :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p 
let run_safe :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t  ->
    fun p  ->
      let uu____68897 = FStar_Options.tactics_failhard ()  in
      if uu____68897
      then run t p
      else
        (try (fun uu___640_68907  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____68916,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____68920,msg,uu____68922) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | e -> FStar_Tactics_Result.Failed (e, p))
  
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
  
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____69002 = run t1 p  in
           match uu____69002 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____69009 = t2 a  in run uu____69009 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (idtac : unit tac) = ret () 
let (get_uvar_solved :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    let uu____69032 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____69032 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____69054 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____69056 =
      let uu____69058 = check_goal_solved g  in
      match uu____69058 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____69064 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____69064
       in
    FStar_Util.format2 "%s%s\n" uu____69054 uu____69056
  
let (goal_to_string :
  Prims.string ->
    (Prims.int * Prims.int) FStar_Pervasives_Native.option ->
      FStar_Tactics_Types.proofstate ->
        FStar_Tactics_Types.goal -> Prims.string)
  =
  fun kind  ->
    fun maybe_num  ->
      fun ps  ->
        fun g  ->
          let w =
            let uu____69111 = FStar_Options.print_implicits ()  in
            if uu____69111
            then
              let uu____69115 = FStar_Tactics_Types.goal_env g  in
              let uu____69116 = FStar_Tactics_Types.goal_witness g  in
              tts uu____69115 uu____69116
            else
              (let uu____69119 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____69119 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____69125 = FStar_Tactics_Types.goal_env g  in
                   let uu____69126 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____69125 uu____69126)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____69149 = FStar_Util.string_of_int i  in
                let uu____69151 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____69149 uu____69151
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____69169 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____69172 =
                 let uu____69174 = FStar_Tactics_Types.goal_env g  in
                 tts uu____69174
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____69169 w uu____69172)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____69201 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____69201
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____69226 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____69226
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69258 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____69258
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____69268) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____69278) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____69298 =
      let uu____69299 = FStar_Tactics_Types.goal_env g  in
      let uu____69300 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____69299 uu____69300  in
    FStar_Syntax_Util.un_squash uu____69298
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____69309 = get_phi g  in FStar_Option.isSome uu____69309 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____69333  ->
    bind get
      (fun ps  ->
         let uu____69341 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____69341)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____69356  ->
    match uu____69356 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____69388 =
          let uu____69392 =
            let uu____69396 =
              let uu____69398 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____69398
                msg
               in
            let uu____69401 =
              let uu____69405 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____69409 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____69409
                else ""  in
              let uu____69415 =
                let uu____69419 =
                  let uu____69421 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____69421
                  then
                    let uu____69426 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____69426
                  else ""  in
                [uu____69419]  in
              uu____69405 :: uu____69415  in
            uu____69396 :: uu____69401  in
          let uu____69436 =
            let uu____69440 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____69460 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____69440 uu____69460  in
          FStar_List.append uu____69392 uu____69436  in
        FStar_String.concat "" uu____69388
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____69494 =
        let uu____69495 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____69495  in
      let uu____69496 =
        let uu____69501 =
          let uu____69502 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____69502  in
        FStar_Syntax_Print.binders_to_json uu____69501  in
      FStar_All.pipe_right uu____69494 uu____69496  in
    let uu____69503 =
      let uu____69511 =
        let uu____69519 =
          let uu____69525 =
            let uu____69526 =
              let uu____69534 =
                let uu____69540 =
                  let uu____69541 =
                    let uu____69543 = FStar_Tactics_Types.goal_env g  in
                    let uu____69544 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____69543 uu____69544  in
                  FStar_Util.JsonStr uu____69541  in
                ("witness", uu____69540)  in
              let uu____69547 =
                let uu____69555 =
                  let uu____69561 =
                    let uu____69562 =
                      let uu____69564 = FStar_Tactics_Types.goal_env g  in
                      let uu____69565 = FStar_Tactics_Types.goal_type g  in
                      tts uu____69564 uu____69565  in
                    FStar_Util.JsonStr uu____69562  in
                  ("type", uu____69561)  in
                [uu____69555;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____69534 :: uu____69547  in
            FStar_Util.JsonAssoc uu____69526  in
          ("goal", uu____69525)  in
        [uu____69519]  in
      ("hyps", g_binders) :: uu____69511  in
    FStar_Util.JsonAssoc uu____69503
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____69619  ->
    match uu____69619 with
    | (msg,ps) ->
        let uu____69629 =
          let uu____69637 =
            let uu____69645 =
              let uu____69653 =
                let uu____69661 =
                  let uu____69667 =
                    let uu____69668 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____69668  in
                  ("goals", uu____69667)  in
                let uu____69673 =
                  let uu____69681 =
                    let uu____69687 =
                      let uu____69688 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____69688  in
                    ("smt-goals", uu____69687)  in
                  [uu____69681]  in
                uu____69661 :: uu____69673  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____69653
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____69645  in
          let uu____69722 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____69738 =
                let uu____69744 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____69744)  in
              [uu____69738]
            else []  in
          FStar_List.append uu____69637 uu____69722  in
        FStar_Util.JsonAssoc uu____69629
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____69784  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____69815 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____69815 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____69888 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____69888
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____69902 . Prims.string -> Prims.string -> 'Auu____69902 tac
  =
  fun msg  ->
    fun x  -> let uu____69919 = FStar_Util.format1 msg x  in fail uu____69919
  
let fail2 :
  'Auu____69930 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____69930 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____69954 = FStar_Util.format2 msg x y  in fail uu____69954
  
let fail3 :
  'Auu____69967 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____69967 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69998 = FStar_Util.format3 msg x y z  in fail uu____69998
  
let fail4 :
  'Auu____70013 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____70013 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____70051 = FStar_Util.format4 msg x y z w  in
            fail uu____70051
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____70086 = run t ps  in
         match uu____70086 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_70110 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_70110.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_70110.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_70110.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_70110.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_70110.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_70110.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_70110.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_70110.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_70110.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_70110.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_70110.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_70110.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____70149 = run t ps  in
         match uu____70149 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____70197 = catch t  in
    bind uu____70197
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____70224 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_70256  ->
              match () with
              | () -> let uu____70261 = trytac t  in run uu____70261 ps) ()
         with
         | FStar_Errors.Err (uu____70277,msg) ->
             (log ps
                (fun uu____70283  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____70289,msg,uu____70291) ->
             (log ps
                (fun uu____70296  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____70333 = run t ps  in
           match uu____70333 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Types.TacticFailure msg,q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Types.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e,q) ->
               FStar_Tactics_Result.Failed (e, q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____70357  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_70372 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_70372.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_70372.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_70372.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_70372.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_70372.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_70372.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_70372.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_70372.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_70372.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_70372.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_70372.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_70372.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____70396 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____70396
         then
           let uu____70400 = FStar_Syntax_Print.term_to_string t1  in
           let uu____70402 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____70400
             uu____70402
         else ());
        (try
           (fun uu___871_70413  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____70421 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70421
                    then
                      let uu____70425 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____70427 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____70429 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____70425
                        uu____70427 uu____70429
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____70440 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____70440 (fun uu____70445  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____70455,msg) ->
             mlog
               (fun uu____70461  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____70464  -> ret false)
         | FStar_Errors.Error (uu____70467,msg,r) ->
             mlog
               (fun uu____70475  ->
                  let uu____70476 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____70476) (fun uu____70480  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_70494 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_70494.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_70494.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_70494.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_70497 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_70497.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_70497.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_70497.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_70497.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_70497.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_70497.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_70497.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_70497.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_70497.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_70497.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_70497.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_70497.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____70524  ->
             (let uu____70526 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____70526
              then
                (FStar_Options.push ();
                 (let uu____70531 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____70535 = __do_unify env t1 t2  in
              bind uu____70535
                (fun r  ->
                   (let uu____70546 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70546 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_70560 = ps  in
         let uu____70561 =
           FStar_List.filter
             (fun g  ->
                let uu____70567 = check_goal_solved g  in
                FStar_Option.isNone uu____70567) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_70560.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_70560.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_70560.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70561;
           FStar_Tactics_Types.smt_goals =
             (uu___916_70560.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_70560.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_70560.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_70560.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_70560.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_70560.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_70560.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_70560.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_70560.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70585 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____70585 with
      | FStar_Pervasives_Native.Some uu____70590 ->
          let uu____70591 =
            let uu____70593 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____70593  in
          fail uu____70591
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____70614 = FStar_Tactics_Types.goal_env goal  in
      let uu____70615 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____70614 solution uu____70615
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____70622 =
         let uu___929_70623 = p  in
         let uu____70624 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_70623.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_70623.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_70623.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70624;
           FStar_Tactics_Types.smt_goals =
             (uu___929_70623.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_70623.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_70623.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_70623.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_70623.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_70623.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_70623.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_70623.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_70623.FStar_Tactics_Types.local_state)
         }  in
       set uu____70622)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____70646  ->
           let uu____70647 =
             let uu____70649 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____70649  in
           let uu____70650 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____70647 uu____70650)
        (fun uu____70655  ->
           let uu____70656 = trysolve goal solution  in
           bind uu____70656
             (fun b  ->
                if b
                then bind __dismiss (fun uu____70668  -> remove_solved_goals)
                else
                  (let uu____70671 =
                     let uu____70673 =
                       let uu____70675 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____70675 solution  in
                     let uu____70676 =
                       let uu____70678 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70679 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____70678 uu____70679  in
                     let uu____70680 =
                       let uu____70682 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70683 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____70682 uu____70683  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____70673 uu____70676 uu____70680
                      in
                   fail uu____70671)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70700 = set_solution goal solution  in
      bind uu____70700
        (fun uu____70704  ->
           bind __dismiss (fun uu____70706  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_70725 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_70725.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_70725.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_70725.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_70725.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_70725.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_70725.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_70725.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_70725.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_70725.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_70725.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_70725.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_70725.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_70744 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_70744.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_70744.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_70744.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_70744.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_70744.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_70744.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_70744.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_70744.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_70744.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_70744.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_70744.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_70744.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____70771 = FStar_Options.defensive ()  in
    if uu____70771
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____70781 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____70781)
         in
      let b2 =
        b1 &&
          (let uu____70785 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____70785)
         in
      let rec aux b3 e =
        let uu____70800 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____70800 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____70820 =
        (let uu____70824 = aux b2 env  in Prims.op_Negation uu____70824) &&
          (let uu____70827 = FStar_ST.op_Bang nwarn  in
           uu____70827 < (Prims.parse_int "5"))
         in
      (if uu____70820
       then
         ((let uu____70853 =
             let uu____70854 = FStar_Tactics_Types.goal_type g  in
             uu____70854.FStar_Syntax_Syntax.pos  in
           let uu____70857 =
             let uu____70863 =
               let uu____70865 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____70865
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____70863)  in
           FStar_Errors.log_issue uu____70853 uu____70857);
          (let uu____70869 =
             let uu____70871 = FStar_ST.op_Bang nwarn  in
             uu____70871 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____70869))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_70940 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_70940.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_70940.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_70940.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_70940.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_70940.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_70940.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_70940.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_70940.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_70940.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_70940.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_70940.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_70940.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_70961 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_70961.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_70961.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_70961.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_70961.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_70961.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_70961.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_70961.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_70961.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_70961.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_70961.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_70961.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_70961.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_70982 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_70982.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_70982.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_70982.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_70982.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_70982.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_70982.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_70982.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_70982.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_70982.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_70982.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_70982.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_70982.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_71003 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_71003.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_71003.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_71003.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_71003.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_71003.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_71003.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_71003.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_71003.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_71003.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_71003.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_71003.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_71003.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____71015  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____71046 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____71046 with
        | (u,ctx_uvar,g_u) ->
            let uu____71084 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____71084
              (fun uu____71093  ->
                 let uu____71094 =
                   let uu____71099 =
                     let uu____71100 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____71100  in
                   (u, uu____71099)  in
                 ret uu____71094)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____71121 = FStar_Syntax_Util.un_squash t1  in
    match uu____71121 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____71133 =
          let uu____71134 = FStar_Syntax_Subst.compress t'1  in
          uu____71134.FStar_Syntax_Syntax.n  in
        (match uu____71133 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____71139 -> false)
    | uu____71141 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____71154 = FStar_Syntax_Util.un_squash t  in
    match uu____71154 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____71165 =
          let uu____71166 = FStar_Syntax_Subst.compress t'  in
          uu____71166.FStar_Syntax_Syntax.n  in
        (match uu____71165 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____71171 -> false)
    | uu____71173 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____71186  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____71198 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____71198 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____71205 = goal_to_string_verbose hd1  in
                    let uu____71207 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____71205 uu____71207);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____71220 =
      bind get
        (fun ps  ->
           let uu____71226 = cur_goal ()  in
           bind uu____71226
             (fun g  ->
                (let uu____71233 =
                   let uu____71234 = FStar_Tactics_Types.goal_type g  in
                   uu____71234.FStar_Syntax_Syntax.pos  in
                 let uu____71237 =
                   let uu____71243 =
                     let uu____71245 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____71245
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____71243)  in
                 FStar_Errors.log_issue uu____71233 uu____71237);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____71220
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____71268  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_71279 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_71279.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_71279.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_71279.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_71279.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_71279.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_71279.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_71279.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_71279.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_71279.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_71279.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_71279.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_71279.FStar_Tactics_Types.local_state)
           }  in
         let uu____71281 = set ps1  in
         bind uu____71281
           (fun uu____71286  ->
              let uu____71287 = FStar_BigInt.of_int_fs n1  in ret uu____71287))
  
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate ->
          Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label1  ->
            let typ =
              let uu____71325 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____71325 phi  in
            let uu____71326 = new_uvar reason env typ  in
            bind uu____71326
              (fun uu____71341  ->
                 match uu____71341 with
                 | (uu____71348,ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label1
                        in
                     ret goal)
  
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____71395  ->
                let uu____71396 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71396)
             (fun uu____71401  ->
                let e1 =
                  let uu___1049_71403 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_71403.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_71403.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_71403.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_71403.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_71403.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_71403.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_71403.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_71403.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_71403.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_71403.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_71403.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_71403.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_71403.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_71403.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_71403.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_71403.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_71403.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_71403.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_71403.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_71403.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_71403.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_71403.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_71403.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_71403.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_71403.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_71403.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_71403.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_71403.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_71403.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_71403.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_71403.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_71403.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_71403.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_71403.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_71403.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_71403.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_71403.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_71403.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_71403.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_71403.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_71403.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_71403.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_71415  ->
                     match () with
                     | () ->
                         let uu____71424 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____71424) ()
                with
                | FStar_Errors.Err (uu____71451,msg) ->
                    let uu____71455 = tts e1 t  in
                    let uu____71457 =
                      let uu____71459 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71459
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71455 uu____71457 msg
                | FStar_Errors.Error (uu____71469,msg,uu____71471) ->
                    let uu____71474 = tts e1 t  in
                    let uu____71476 =
                      let uu____71478 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71478
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71474 uu____71476 msg))
  
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____71531  ->
                let uu____71532 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____71532)
             (fun uu____71537  ->
                let e1 =
                  let uu___1070_71539 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_71539.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_71539.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_71539.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_71539.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_71539.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_71539.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_71539.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_71539.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_71539.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_71539.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_71539.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_71539.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_71539.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_71539.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_71539.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_71539.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_71539.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_71539.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_71539.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_71539.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_71539.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_71539.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_71539.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_71539.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_71539.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_71539.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_71539.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_71539.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_71539.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_71539.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_71539.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_71539.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_71539.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_71539.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_71539.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_71539.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_71539.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_71539.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_71539.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_71539.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_71539.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_71539.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_71554  ->
                     match () with
                     | () ->
                         let uu____71563 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____71563 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71601,msg) ->
                    let uu____71605 = tts e1 t  in
                    let uu____71607 =
                      let uu____71609 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71609
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71605 uu____71607 msg
                | FStar_Errors.Error (uu____71619,msg,uu____71621) ->
                    let uu____71624 = tts e1 t  in
                    let uu____71626 =
                      let uu____71628 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71628
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71624 uu____71626 msg))
  
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____71681  ->
                let uu____71682 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71682)
             (fun uu____71688  ->
                let e1 =
                  let uu___1095_71690 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_71690.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_71690.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_71690.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_71690.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_71690.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_71690.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_71690.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_71690.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_71690.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_71690.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_71690.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_71690.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_71690.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_71690.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_71690.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_71690.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_71690.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_71690.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_71690.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_71690.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_71690.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_71690.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_71690.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_71690.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_71690.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_71690.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_71690.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_71690.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_71690.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_71690.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_71690.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_71690.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_71690.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_71690.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_71690.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_71690.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_71690.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_71690.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_71690.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_71690.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_71690.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_71690.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_71693 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_71693.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_71693.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_71693.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_71693.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_71693.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_71693.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_71693.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_71693.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_71693.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_71693.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_71693.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_71693.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_71693.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_71693.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_71693.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_71693.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_71693.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_71693.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_71693.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_71693.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_71693.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_71693.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_71693.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_71693.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_71693.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_71693.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_71693.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_71693.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_71693.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_71693.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_71693.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_71693.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_71693.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_71693.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_71693.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_71693.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_71693.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_71693.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_71693.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_71693.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_71693.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_71693.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_71708  ->
                     match () with
                     | () ->
                         let uu____71717 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____71717 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71755,msg) ->
                    let uu____71759 = tts e2 t  in
                    let uu____71761 =
                      let uu____71763 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71763
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71759 uu____71761 msg
                | FStar_Errors.Error (uu____71773,msg,uu____71775) ->
                    let uu____71778 = tts e2 t  in
                    let uu____71780 =
                      let uu____71782 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71782
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71778 uu____71780 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____71816  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_71835 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_71835.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_71835.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_71835.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_71835.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_71835.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_71835.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_71835.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_71835.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_71835.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_71835.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_71835.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_71835.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____71860 = get_guard_policy ()  in
      bind uu____71860
        (fun old_pol  ->
           let uu____71866 = set_guard_policy pol  in
           bind uu____71866
             (fun uu____71870  ->
                bind t
                  (fun r  ->
                     let uu____71874 = set_guard_policy old_pol  in
                     bind uu____71874 (fun uu____71878  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____71882 = let uu____71887 = cur_goal ()  in trytac uu____71887  in
  bind uu____71882
    (fun uu___609_71894  ->
       match uu___609_71894 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____71900 = FStar_Options.peek ()  in ret uu____71900)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____71925  ->
             let uu____71926 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____71926)
          (fun uu____71931  ->
             let uu____71932 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____71932
               (fun uu____71936  ->
                  bind getopts
                    (fun opts  ->
                       let uu____71940 =
                         let uu____71941 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____71941.FStar_TypeChecker_Env.guard_f  in
                       match uu____71940 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____71945 = istrivial e f  in
                           if uu____71945
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____71958 =
                                          let uu____71964 =
                                            let uu____71966 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____71966
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____71964)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____71958);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____71972  ->
                                           let uu____71973 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____71973)
                                        (fun uu____71978  ->
                                           let uu____71979 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____71979
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_71987 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_71987.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_71987.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_71987.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_71987.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____71991  ->
                                           let uu____71992 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____71992)
                                        (fun uu____71997  ->
                                           let uu____71998 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____71998
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_72006 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_72006.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_72006.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_72006.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_72006.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____72010  ->
                                           let uu____72011 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____72011)
                                        (fun uu____72015  ->
                                           try
                                             (fun uu___1170_72020  ->
                                                match () with
                                                | () ->
                                                    let uu____72023 =
                                                      let uu____72025 =
                                                        let uu____72027 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____72027
                                                         in
                                                      Prims.op_Negation
                                                        uu____72025
                                                       in
                                                    if uu____72023
                                                    then
                                                      mlog
                                                        (fun uu____72034  ->
                                                           let uu____72035 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____72035)
                                                        (fun uu____72039  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_72044 ->
                                               mlog
                                                 (fun uu____72049  ->
                                                    let uu____72050 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____72050)
                                                 (fun uu____72054  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____72066 =
      let uu____72069 = cur_goal ()  in
      bind uu____72069
        (fun goal  ->
           let uu____72075 =
             let uu____72084 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____72084 t  in
           bind uu____72075
             (fun uu____72095  ->
                match uu____72095 with
                | (uu____72104,typ,uu____72106) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____72066
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label1  ->
            let uu____72146 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____72146 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____72158  ->
    let uu____72161 = cur_goal ()  in
    bind uu____72161
      (fun goal  ->
         let uu____72167 =
           let uu____72169 = FStar_Tactics_Types.goal_env goal  in
           let uu____72170 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____72169 uu____72170  in
         if uu____72167
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____72176 =
              let uu____72178 = FStar_Tactics_Types.goal_env goal  in
              let uu____72179 = FStar_Tactics_Types.goal_type goal  in
              tts uu____72178 uu____72179  in
            fail1 "Not a trivial goal: %s" uu____72176))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____72230 =
               try
                 (fun uu___1226_72253  ->
                    match () with
                    | () ->
                        let uu____72264 =
                          let uu____72273 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____72273
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____72264) ()
               with | uu___1225_72284 -> fail "divide: not enough goals"  in
             bind uu____72230
               (fun uu____72321  ->
                  match uu____72321 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_72347 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_72347.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_72347.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_72347.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_72347.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_72347.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_72347.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_72347.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_72347.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_72347.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_72347.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_72347.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____72348 = set lp  in
                      bind uu____72348
                        (fun uu____72356  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_72372 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_72372.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_72372.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_72372.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_72372.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_72372.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_72372.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_72372.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_72372.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_72372.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_72372.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_72372.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____72373 = set rp  in
                                     bind uu____72373
                                       (fun uu____72381  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_72397 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_List.append
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_72397.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____72398 = set p'
                                                       in
                                                    bind uu____72398
                                                      (fun uu____72406  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____72412 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____72434 = divide FStar_BigInt.one f idtac  in
    bind uu____72434
      (fun uu____72447  -> match uu____72447 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____72485::uu____72486 ->
             let uu____72489 =
               let uu____72498 = map tau  in
               divide FStar_BigInt.one tau uu____72498  in
             bind uu____72489
               (fun uu____72516  ->
                  match uu____72516 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____72558 =
        bind t1
          (fun uu____72563  ->
             let uu____72564 = map t2  in
             bind uu____72564 (fun uu____72572  -> ret ()))
         in
      focus uu____72558
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____72582  ->
    let uu____72585 =
      let uu____72588 = cur_goal ()  in
      bind uu____72588
        (fun goal  ->
           let uu____72597 =
             let uu____72604 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____72604  in
           match uu____72597 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____72613 =
                 let uu____72615 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____72615  in
               if uu____72613
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____72624 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____72624 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____72638 = new_uvar "intro" env' typ'  in
                  bind uu____72638
                    (fun uu____72655  ->
                       match uu____72655 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____72679 = set_solution goal sol  in
                           bind uu____72679
                             (fun uu____72685  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____72687 =
                                  let uu____72690 = bnorm_goal g  in
                                  replace_cur uu____72690  in
                                bind uu____72687 (fun uu____72692  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____72697 =
                 let uu____72699 = FStar_Tactics_Types.goal_env goal  in
                 let uu____72700 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____72699 uu____72700  in
               fail1 "goal is not an arrow (%s)" uu____72697)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____72585
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____72718  ->
    let uu____72725 = cur_goal ()  in
    bind uu____72725
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____72744 =
            let uu____72751 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____72751  in
          match uu____72744 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____72764 =
                let uu____72766 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____72766  in
              if uu____72764
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____72783 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____72783
                    in
                 let bs =
                   let uu____72794 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____72794; b]  in
                 let env' =
                   let uu____72820 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____72820 bs  in
                 let uu____72821 =
                   let uu____72828 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____72828  in
                 bind uu____72821
                   (fun uu____72848  ->
                      match uu____72848 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____72862 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____72865 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____72862
                              FStar_Parser_Const.effect_Tot_lid uu____72865
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____72883 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____72883 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____72905 =
                                   let uu____72906 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____72906.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____72905
                                  in
                               let uu____72922 = set_solution goal tm  in
                               bind uu____72922
                                 (fun uu____72931  ->
                                    let uu____72932 =
                                      let uu____72935 =
                                        bnorm_goal
                                          (let uu___1291_72938 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_72938.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_72938.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_72938.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_72938.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____72935  in
                                    bind uu____72932
                                      (fun uu____72945  ->
                                         let uu____72946 =
                                           let uu____72951 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____72951, b)  in
                                         ret uu____72946)))))
          | FStar_Pervasives_Native.None  ->
              let uu____72960 =
                let uu____72962 = FStar_Tactics_Types.goal_env goal  in
                let uu____72963 = FStar_Tactics_Types.goal_type goal  in
                tts uu____72962 uu____72963  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____72960))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____72983 = cur_goal ()  in
    bind uu____72983
      (fun goal  ->
         mlog
           (fun uu____72990  ->
              let uu____72991 =
                let uu____72993 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____72993  in
              FStar_Util.print1 "norm: witness = %s\n" uu____72991)
           (fun uu____72999  ->
              let steps =
                let uu____73003 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____73003
                 in
              let t =
                let uu____73007 = FStar_Tactics_Types.goal_env goal  in
                let uu____73008 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____73007 uu____73008  in
              let uu____73009 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____73009))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____73034 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____73042 -> g.FStar_Tactics_Types.opts
                 | uu____73045 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____73050  ->
                    let uu____73051 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____73051)
                 (fun uu____73056  ->
                    let uu____73057 = __tc_lax e t  in
                    bind uu____73057
                      (fun uu____73078  ->
                         match uu____73078 with
                         | (t1,uu____73088,uu____73089) ->
                             let steps =
                               let uu____73093 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____73093
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____73099  ->
                                  let uu____73100 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____73100)
                               (fun uu____73104  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____73034
  
let (refine_intro : unit -> unit tac) =
  fun uu____73117  ->
    let uu____73120 =
      let uu____73123 = cur_goal ()  in
      bind uu____73123
        (fun g  ->
           let uu____73130 =
             let uu____73141 = FStar_Tactics_Types.goal_env g  in
             let uu____73142 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____73141
               uu____73142
              in
           match uu____73130 with
           | (uu____73145,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____73171 =
                 let uu____73176 =
                   let uu____73181 =
                     let uu____73182 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____73182]  in
                   FStar_Syntax_Subst.open_term uu____73181 phi  in
                 match uu____73176 with
                 | (bvs,phi1) ->
                     let uu____73207 =
                       let uu____73208 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____73208  in
                     (uu____73207, phi1)
                  in
               (match uu____73171 with
                | (bv1,phi1) ->
                    let uu____73227 =
                      let uu____73230 = FStar_Tactics_Types.goal_env g  in
                      let uu____73231 =
                        let uu____73232 =
                          let uu____73235 =
                            let uu____73236 =
                              let uu____73243 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____73243)  in
                            FStar_Syntax_Syntax.NT uu____73236  in
                          [uu____73235]  in
                        FStar_Syntax_Subst.subst uu____73232 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____73230 uu____73231 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____73227
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____73252  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____73120
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____73275 = cur_goal ()  in
      bind uu____73275
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____73284 = FStar_Tactics_Types.goal_env goal  in
               let uu____73285 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____73284 uu____73285
             else FStar_Tactics_Types.goal_env goal  in
           let uu____73288 = __tc env t  in
           bind uu____73288
             (fun uu____73307  ->
                match uu____73307 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____73322  ->
                         let uu____73323 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____73325 =
                           let uu____73327 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____73327
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____73323 uu____73325)
                      (fun uu____73331  ->
                         let uu____73332 =
                           let uu____73335 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____73335 guard  in
                         bind uu____73332
                           (fun uu____73338  ->
                              mlog
                                (fun uu____73342  ->
                                   let uu____73343 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____73345 =
                                     let uu____73347 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____73347
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____73343 uu____73345)
                                (fun uu____73351  ->
                                   let uu____73352 =
                                     let uu____73356 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____73357 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____73356 typ uu____73357  in
                                   bind uu____73352
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____73367 =
                                             let uu____73369 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73369 t1  in
                                           let uu____73370 =
                                             let uu____73372 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73372 typ  in
                                           let uu____73373 =
                                             let uu____73375 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73376 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____73375 uu____73376  in
                                           let uu____73377 =
                                             let uu____73379 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73380 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____73379 uu____73380  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____73367 uu____73370
                                             uu____73373 uu____73377)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____73406 =
          mlog
            (fun uu____73411  ->
               let uu____73412 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____73412)
            (fun uu____73417  ->
               let uu____73418 =
                 let uu____73425 = __exact_now set_expected_typ1 tm  in
                 catch uu____73425  in
               bind uu____73418
                 (fun uu___611_73434  ->
                    match uu___611_73434 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____73445  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____73449  ->
                             let uu____73450 =
                               let uu____73457 =
                                 let uu____73460 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____73460
                                   (fun uu____73465  ->
                                      let uu____73466 = refine_intro ()  in
                                      bind uu____73466
                                        (fun uu____73470  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____73457  in
                             bind uu____73450
                               (fun uu___610_73477  ->
                                  match uu___610_73477 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____73486  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____73489  -> ret ())
                                  | FStar_Util.Inl uu____73490 ->
                                      mlog
                                        (fun uu____73492  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____73495  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____73406
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____73547 = f x  in
          bind uu____73547
            (fun y  ->
               let uu____73555 = mapM f xs  in
               bind uu____73555 (fun ys  -> ret (y :: ys)))
  
let rec (__try_match_by_application :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
    FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  =
  fun acc  ->
    fun e  ->
      fun ty1  ->
        fun ty2  ->
          let uu____73627 = do_unify e ty1 ty2  in
          bind uu____73627
            (fun uu___612_73641  ->
               if uu___612_73641
               then ret acc
               else
                 (let uu____73661 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____73661 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____73682 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____73684 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____73682
                        uu____73684
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____73701 =
                        let uu____73703 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____73703  in
                      if uu____73701
                      then fail "Codomain is effectful"
                      else
                        (let uu____73727 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____73727
                           (fun uu____73754  ->
                              match uu____73754 with
                              | (uvt,uv) ->
                                  let typ = comp_to_typ c  in
                                  let typ' =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT
                                         ((FStar_Pervasives_Native.fst b),
                                           uvt)] typ
                                     in
                                  __try_match_by_application
                                    ((uvt, (FStar_Pervasives_Native.snd b),
                                       uv) :: acc) e typ' ty2))))
  
let (try_match_by_application :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
          FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  = fun e  -> fun ty1  -> fun ty2  -> __try_match_by_application [] e ty1 ty2 
let (t_apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____73844 =
        mlog
          (fun uu____73849  ->
             let uu____73850 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____73850)
          (fun uu____73855  ->
             let uu____73856 = cur_goal ()  in
             bind uu____73856
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____73864 = __tc e tm  in
                  bind uu____73864
                    (fun uu____73885  ->
                       match uu____73885 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____73898 =
                             let uu____73909 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____73909  in
                           bind uu____73898
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____73947)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____73951 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____73974  ->
                                       fun w  ->
                                         match uu____73974 with
                                         | (uvt,q,uu____73992) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____74024 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____74041  ->
                                       fun s  ->
                                         match uu____74041 with
                                         | (uu____74053,uu____74054,uv) ->
                                             let uu____74056 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____74056) uvs uu____74024
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____74066 = solve' goal w  in
                                bind uu____74066
                                  (fun uu____74071  ->
                                     let uu____74072 =
                                       mapM
                                         (fun uu____74089  ->
                                            match uu____74089 with
                                            | (uvt,q,uv) ->
                                                let uu____74101 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____74101 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____74106 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____74107 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____74107
                                                     then ret ()
                                                     else
                                                       (let uu____74114 =
                                                          let uu____74117 =
                                                            bnorm_goal
                                                              (let uu___1452_74120
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_74120.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_74120.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_74120.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____74117]  in
                                                        add_goals uu____74114)))
                                         uvs
                                        in
                                     bind uu____74072
                                       (fun uu____74125  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____73844
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____74153 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____74153
    then
      let uu____74162 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____74177 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____74230 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____74162 with
      | (pre,post) ->
          let post1 =
            let uu____74263 =
              let uu____74274 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____74274]  in
            FStar_Syntax_Util.mk_app post uu____74263  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____74305 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____74305
       then
         let uu____74314 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____74314
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let rec fold_left :
  'a 'b . ('a -> 'b -> 'b tac) -> 'b -> 'a Prims.list -> 'b tac =
  fun f  ->
    fun e  ->
      fun xs  ->
        match xs with
        | [] -> ret e
        | x::xs1 ->
            let uu____74393 = f x e  in
            bind uu____74393 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____74408 =
      let uu____74411 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____74418  ->
                  let uu____74419 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____74419)
               (fun uu____74425  ->
                  let is_unit_t t =
                    let uu____74433 =
                      let uu____74434 = FStar_Syntax_Subst.compress t  in
                      uu____74434.FStar_Syntax_Syntax.n  in
                    match uu____74433 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____74440 -> false  in
                  let uu____74442 = cur_goal ()  in
                  bind uu____74442
                    (fun goal  ->
                       let uu____74448 =
                         let uu____74457 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____74457 tm  in
                       bind uu____74448
                         (fun uu____74472  ->
                            match uu____74472 with
                            | (tm1,t,guard) ->
                                let uu____74484 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____74484 with
                                 | (bs,comp) ->
                                     let uu____74517 = lemma_or_sq comp  in
                                     (match uu____74517 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____74537 =
                                            fold_left
                                              (fun uu____74599  ->
                                                 fun uu____74600  ->
                                                   match (uu____74599,
                                                           uu____74600)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____74751 =
                                                         is_unit_t b_t  in
                                                       if uu____74751
                                                       then
                                                         FStar_All.pipe_left
                                                           ret
                                                           (((FStar_Syntax_Util.exp_unit,
                                                               aq) :: uvs),
                                                             imps,
                                                             ((FStar_Syntax_Syntax.NT
                                                                 (b,
                                                                   FStar_Syntax_Util.exp_unit))
                                                             :: subst1))
                                                       else
                                                         (let uu____74874 =
                                                            let uu____74881 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____74881 b_t
                                                             in
                                                          bind uu____74874
                                                            (fun uu____74912 
                                                               ->
                                                               match uu____74912
                                                               with
                                                               | (t1,u) ->
                                                                   FStar_All.pipe_left
                                                                    ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst1)))))
                                              ([], [], []) bs
                                             in
                                          bind uu____74537
                                            (fun uu____75098  ->
                                               match uu____75098 with
                                               | (uvs,implicits,subst1) ->
                                                   let implicits1 =
                                                     FStar_List.rev implicits
                                                      in
                                                   let uvs1 =
                                                     FStar_List.rev uvs  in
                                                   let pre1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 pre
                                                      in
                                                   let post1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 post
                                                      in
                                                   let uu____75186 =
                                                     let uu____75190 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____75191 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____75192 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____75190
                                                       uu____75191
                                                       uu____75192
                                                      in
                                                   bind uu____75186
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____75203 =
                                                            let uu____75205 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____75205
                                                              tm1
                                                             in
                                                          let uu____75206 =
                                                            let uu____75208 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75209 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____75208
                                                              uu____75209
                                                             in
                                                          let uu____75210 =
                                                            let uu____75212 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75213 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____75212
                                                              uu____75213
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____75203
                                                            uu____75206
                                                            uu____75210
                                                        else
                                                          (let uu____75217 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____75217
                                                             (fun uu____75225
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____75251
                                                                    =
                                                                    let uu____75254
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____75254
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____75251
                                                                     in
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun u  ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                   in
                                                                let appears
                                                                  uv goals =
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun g' 
                                                                    ->
                                                                    let uu____75290
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____75290)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____75307
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____75307
                                                                  with
                                                                  | (hd1,uu____75326)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____75353)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____75370
                                                                    -> false)
                                                                   in
                                                                let uu____75372
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let t1 =
                                                                    FStar_Util.now
                                                                    ()  in
                                                                    let uu____75415
                                                                    = imp  in
                                                                    match uu____75415
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____75426
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____75426
                                                                    with
                                                                    | 
                                                                    (hd1,uu____75448)
                                                                    ->
                                                                    let uu____75473
                                                                    =
                                                                    let uu____75474
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____75474.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____75473
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____75482)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_75502
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_75502.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_75502.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_75502.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_75502.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____75505
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____75511
                                                                     ->
                                                                    let uu____75512
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____75514
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____75512
                                                                    uu____75514)
                                                                    (fun
                                                                    uu____75521
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_75523
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_75523.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____75526
                                                                    =
                                                                    let uu____75529
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____75533
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____75535
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____75533
                                                                    uu____75535
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____75541
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____75529
                                                                    uu____75541
                                                                    g_typ  in
                                                                    bind
                                                                    uu____75526
                                                                    (fun
                                                                    uu____75545
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____75372
                                                                  (fun
                                                                    sub_goals
                                                                     ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals
                                                                     in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____75609
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____75609
                                                                    then
                                                                    let uu____75614
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____75614
                                                                    else
                                                                    filter' f
                                                                    xs1  in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____75629
                                                                    =
                                                                    let uu____75631
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____75631
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____75629)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____75632
                                                                    =
                                                                    let uu____75635
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____75635
                                                                    guard  in
                                                                    bind
                                                                    uu____75632
                                                                    (fun
                                                                    uu____75639
                                                                     ->
                                                                    let uu____75640
                                                                    =
                                                                    let uu____75643
                                                                    =
                                                                    let uu____75645
                                                                    =
                                                                    let uu____75647
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____75648
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____75647
                                                                    uu____75648
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____75645
                                                                     in
                                                                    if
                                                                    uu____75643
                                                                    then
                                                                    let uu____75652
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____75652
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____75640
                                                                    (fun
                                                                    uu____75657
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____74411  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____74408
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75681 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____75681 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____75691::(e1,uu____75693)::(e2,uu____75695)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____75756 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75781 = destruct_eq' typ  in
    match uu____75781 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____75811 = FStar_Syntax_Util.un_squash typ  in
        (match uu____75811 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____75880 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____75880 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____75938 = aux e'  in
               FStar_Util.map_opt uu____75938
                 (fun uu____75969  ->
                    match uu____75969 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____75995 = aux e  in
      FStar_Util.map_opt uu____75995
        (fun uu____76026  ->
           match uu____76026 with
           | (e',bv,bvs) -> (e', bv, (FStar_List.rev bvs)))
  
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_left
        (fun e1  -> fun b  -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
  
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option)
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let uu____76100 =
            let uu____76111 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____76111  in
          FStar_Util.map_opt uu____76100
            (fun uu____76129  ->
               match uu____76129 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_76151 = bv  in
                     let uu____76152 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_76151.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_76151.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____76152
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_76160 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____76161 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____76170 =
                       let uu____76173 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____76173  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_76160.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____76161;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____76170;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_76160.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_76160.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_76160.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_76160.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_76174 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_76174.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_76174.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_76174.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_76174.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____76185 =
      let uu____76188 = cur_goal ()  in
      bind uu____76188
        (fun goal  ->
           let uu____76196 = h  in
           match uu____76196 with
           | (bv,uu____76200) ->
               mlog
                 (fun uu____76208  ->
                    let uu____76209 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____76211 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____76209
                      uu____76211)
                 (fun uu____76216  ->
                    let uu____76217 =
                      let uu____76228 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____76228  in
                    match uu____76217 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____76255 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____76255 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____76270 =
                               let uu____76271 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____76271.FStar_Syntax_Syntax.n  in
                             (match uu____76270 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_76288 = bv2  in
                                    let uu____76289 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_76288.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_76288.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76289
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_76297 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____76298 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____76307 =
                                      let uu____76310 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____76310
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_76297.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____76298;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____76307;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_76297.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_76297.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_76297.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_76297.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_76313 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_76313.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_76313.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_76313.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_76313.FStar_Tactics_Types.label)
                                     })
                              | uu____76314 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____76316 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____76185
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____76346 =
        let uu____76349 = cur_goal ()  in
        bind uu____76349
          (fun goal  ->
             let uu____76360 = b  in
             match uu____76360 with
             | (bv,uu____76364) ->
                 let bv' =
                   let uu____76370 =
                     let uu___1688_76371 = bv  in
                     let uu____76372 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____76372;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_76371.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_76371.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____76370  in
                 let s1 =
                   let uu____76377 =
                     let uu____76378 =
                       let uu____76385 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____76385)  in
                     FStar_Syntax_Syntax.NT uu____76378  in
                   [uu____76377]  in
                 let uu____76390 = subst_goal bv bv' s1 goal  in
                 (match uu____76390 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____76346
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____76412 =
      let uu____76415 = cur_goal ()  in
      bind uu____76415
        (fun goal  ->
           let uu____76424 = b  in
           match uu____76424 with
           | (bv,uu____76428) ->
               let uu____76433 =
                 let uu____76444 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____76444  in
               (match uu____76433 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____76471 = FStar_Syntax_Util.type_u ()  in
                    (match uu____76471 with
                     | (ty,u) ->
                         let uu____76480 = new_uvar "binder_retype" e0 ty  in
                         bind uu____76480
                           (fun uu____76499  ->
                              match uu____76499 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_76509 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_76509.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_76509.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____76513 =
                                      let uu____76514 =
                                        let uu____76521 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____76521)  in
                                      FStar_Syntax_Syntax.NT uu____76514  in
                                    [uu____76513]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_76533 = b1  in
                                         let uu____76534 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_76533.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_76533.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____76534
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____76541  ->
                                       let new_goal =
                                         let uu____76543 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____76544 =
                                           let uu____76545 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____76545
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____76543 uu____76544
                                          in
                                       let uu____76546 = add_goals [new_goal]
                                          in
                                       bind uu____76546
                                         (fun uu____76551  ->
                                            let uu____76552 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____76552
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____76412
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____76578 =
        let uu____76581 = cur_goal ()  in
        bind uu____76581
          (fun goal  ->
             let uu____76590 = b  in
             match uu____76590 with
             | (bv,uu____76594) ->
                 let uu____76599 =
                   let uu____76610 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____76610  in
                 (match uu____76599 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____76640 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____76640
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_76645 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_76645.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_76645.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____76647 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____76647))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____76578
  
let (revert : unit -> unit tac) =
  fun uu____76660  ->
    let uu____76663 = cur_goal ()  in
    bind uu____76663
      (fun goal  ->
         let uu____76669 =
           let uu____76676 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76676  in
         match uu____76669 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____76693 =
                 let uu____76696 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____76696  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____76693
                in
             let uu____76711 = new_uvar "revert" env' typ'  in
             bind uu____76711
               (fun uu____76727  ->
                  match uu____76727 with
                  | (r,u_r) ->
                      let uu____76736 =
                        let uu____76739 =
                          let uu____76740 =
                            let uu____76741 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____76741.FStar_Syntax_Syntax.pos  in
                          let uu____76744 =
                            let uu____76749 =
                              let uu____76750 =
                                let uu____76759 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____76759  in
                              [uu____76750]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____76749  in
                          uu____76744 FStar_Pervasives_Native.None
                            uu____76740
                           in
                        set_solution goal uu____76739  in
                      bind uu____76736
                        (fun uu____76780  ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label
                              in
                           replace_cur g)))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____76794 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____76794
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____76810 = cur_goal ()  in
    bind uu____76810
      (fun goal  ->
         mlog
           (fun uu____76818  ->
              let uu____76819 = FStar_Syntax_Print.binder_to_string b  in
              let uu____76821 =
                let uu____76823 =
                  let uu____76825 =
                    let uu____76834 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____76834  in
                  FStar_All.pipe_right uu____76825 FStar_List.length  in
                FStar_All.pipe_right uu____76823 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____76819 uu____76821)
           (fun uu____76855  ->
              let uu____76856 =
                let uu____76867 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____76867  in
              match uu____76856 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____76912 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____76912
                        then
                          let uu____76917 =
                            let uu____76919 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____76919
                             in
                          fail uu____76917
                        else check1 bvs2
                     in
                  let uu____76924 =
                    let uu____76926 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____76926  in
                  if uu____76924
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____76933 = check1 bvs  in
                     bind uu____76933
                       (fun uu____76939  ->
                          let env' = push_bvs e' bvs  in
                          let uu____76941 =
                            let uu____76948 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____76948  in
                          bind uu____76941
                            (fun uu____76958  ->
                               match uu____76958 with
                               | (ut,uvar_ut) ->
                                   let uu____76967 = set_solution goal ut  in
                                   bind uu____76967
                                     (fun uu____76972  ->
                                        let uu____76973 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____76973))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____76981  ->
    let uu____76984 = cur_goal ()  in
    bind uu____76984
      (fun goal  ->
         let uu____76990 =
           let uu____76997 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76997  in
         match uu____76990 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____77006) ->
             let uu____77011 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____77011)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____77024 = cur_goal ()  in
    bind uu____77024
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____77034 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____77034  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____77037  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____77050 = cur_goal ()  in
    bind uu____77050
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____77060 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____77060  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____77063  -> add_goals [g']))
  
let rec (tac_fold_env :
  FStar_Tactics_Types.direction ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun d  ->
    fun f  ->
      fun env  ->
        fun t  ->
          let tn =
            let uu____77104 = FStar_Syntax_Subst.compress t  in
            uu____77104.FStar_Syntax_Syntax.n  in
          let uu____77107 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_77114 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_77114.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_77114.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____77107
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____77131 =
                   let uu____77132 = FStar_Syntax_Subst.compress t1  in
                   uu____77132.FStar_Syntax_Syntax.n  in
                 match uu____77131 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____77163 = ff hd1  in
                     bind uu____77163
                       (fun hd2  ->
                          let fa uu____77189 =
                            match uu____77189 with
                            | (a,q) ->
                                let uu____77210 = ff a  in
                                bind uu____77210 (fun a1  -> ret (a1, q))
                             in
                          let uu____77229 = mapM fa args  in
                          bind uu____77229
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____77311 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____77311 with
                      | (bs1,t') ->
                          let uu____77320 =
                            let uu____77323 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____77323 t'  in
                          bind uu____77320
                            (fun t''  ->
                               let uu____77327 =
                                 let uu____77328 =
                                   let uu____77347 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____77356 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____77347, uu____77356, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____77328  in
                               ret uu____77327))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____77431 = ff hd1  in
                     bind uu____77431
                       (fun hd2  ->
                          let ffb br =
                            let uu____77446 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____77446 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____77478 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____77478  in
                                let uu____77479 = ff1 e  in
                                bind uu____77479
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____77494 = mapM ffb brs  in
                          bind uu____77494
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____77538;
                          FStar_Syntax_Syntax.lbtyp = uu____77539;
                          FStar_Syntax_Syntax.lbeff = uu____77540;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____77542;
                          FStar_Syntax_Syntax.lbpos = uu____77543;_}::[]),e)
                     ->
                     let lb =
                       let uu____77571 =
                         let uu____77572 = FStar_Syntax_Subst.compress t1  in
                         uu____77572.FStar_Syntax_Syntax.n  in
                       match uu____77571 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____77576) -> lb
                       | uu____77592 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____77602 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77602
                         (fun def1  ->
                            ret
                              (let uu___1875_77608 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_77608.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_77608.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_77608.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_77608.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_77608.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_77608.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77609 = fflb lb  in
                     bind uu____77609
                       (fun lb1  ->
                          let uu____77619 =
                            let uu____77624 =
                              let uu____77625 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____77625]  in
                            FStar_Syntax_Subst.open_term uu____77624 e  in
                          match uu____77619 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____77655 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____77655  in
                              let uu____77656 = ff1 e1  in
                              bind uu____77656
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____77703 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77703
                         (fun def  ->
                            ret
                              (let uu___1893_77709 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_77709.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_77709.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_77709.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_77709.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_77709.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_77709.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77710 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____77710 with
                      | (lbs1,e1) ->
                          let uu____77725 = mapM fflb lbs1  in
                          bind uu____77725
                            (fun lbs2  ->
                               let uu____77737 = ff e1  in
                               bind uu____77737
                                 (fun e2  ->
                                    let uu____77745 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____77745 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____77816 = ff t2  in
                     bind uu____77816
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____77847 = ff t2  in
                     bind uu____77847
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____77854 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_77861 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_77861.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_77861.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let (pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    unit tac ->
      FStar_Options.optionstate ->
        Prims.string ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun label1  ->
          fun env  ->
            fun t  ->
              let uu____77908 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_77917 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_77917.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_77917.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_77917.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_77917.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_77917.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_77917.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_77917.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_77917.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_77917.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_77917.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_77917.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_77917.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_77917.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_77917.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_77917.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_77917.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_77917.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_77917.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_77917.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_77917.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_77917.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_77917.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_77917.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_77917.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_77917.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_77917.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_77917.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_77917.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_77917.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_77917.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_77917.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_77917.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_77917.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_77917.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_77917.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_77917.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_77917.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_77917.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_77917.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_77917.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_77917.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_77917.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____77908 with
              | (t1,lcomp,g) ->
                  let uu____77924 =
                    (let uu____77928 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____77928) ||
                      (let uu____77931 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____77931)
                     in
                  if uu____77924
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____77942 = new_uvar "pointwise_rec" env typ  in
                       bind uu____77942
                         (fun uu____77959  ->
                            match uu____77959 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____77972  ->
                                      let uu____77973 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____77975 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____77973 uu____77975);
                                 (let uu____77978 =
                                    let uu____77981 =
                                      let uu____77982 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____77982
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____77981 opts label1
                                     in
                                  bind uu____77978
                                    (fun uu____77986  ->
                                       let uu____77987 =
                                         bind tau
                                           (fun uu____77993  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____77999  ->
                                                   let uu____78000 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____78002 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____78000 uu____78002);
                                              ret ut1)
                                          in
                                       focus uu____77987))))
                        in
                     let uu____78005 = catch rewrite_eq  in
                     bind uu____78005
                       (fun x  ->
                          match x with
                          | FStar_Util.Inl (FStar_Tactics_Types.TacticFailure
                              "SKIP") -> ret t1
                          | FStar_Util.Inl e -> traise e
                          | FStar_Util.Inr x1 -> ret x1))
  
type ctrl = FStar_BigInt.t
let (keepGoing : ctrl) = FStar_BigInt.zero 
let (proceedToNextSubtree : FStar_BigInt.bigint) = FStar_BigInt.one 
let (globalStop : FStar_BigInt.bigint) =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool
let (skipThisTerm : Prims.bool) = false 
let (rewroteThisTerm : Prims.bool) = true 
type 'a ctrl_tac = ('a * ctrl) tac
let rec (ctrl_tac_fold :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun f  ->
    fun env  ->
      fun ctrl  ->
        fun t  ->
          let keep_going c =
            if c = proceedToNextSubtree then keepGoing else c  in
          let maybe_continue ctrl1 t1 k =
            if ctrl1 = globalStop
            then ret (t1, globalStop)
            else
              if ctrl1 = proceedToNextSubtree
              then ret (t1, keepGoing)
              else k t1
             in
          let uu____78223 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____78223
            (fun t1  ->
               let uu____78231 =
                 f env
                   (let uu___2007_78240 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_78240.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_78240.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____78231
                 (fun uu____78256  ->
                    match uu____78256 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____78279 =
                               let uu____78280 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____78280.FStar_Syntax_Syntax.n  in
                             match uu____78279 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____78317 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____78317
                                   (fun uu____78342  ->
                                      match uu____78342 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____78358 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____78358
                                            (fun uu____78385  ->
                                               match uu____78385 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_78415 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_78415.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_78415.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____78457 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____78457 with
                                  | (bs1,t') ->
                                      let uu____78472 =
                                        let uu____78479 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____78479 ctrl1 t'
                                         in
                                      bind uu____78472
                                        (fun uu____78497  ->
                                           match uu____78497 with
                                           | (t'',ctrl2) ->
                                               let uu____78512 =
                                                 let uu____78519 =
                                                   let uu___2000_78522 = t4
                                                      in
                                                   let uu____78525 =
                                                     let uu____78526 =
                                                       let uu____78545 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____78554 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____78545,
                                                         uu____78554, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____78526
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____78525;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_78522.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_78522.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____78519, ctrl2)  in
                                               ret uu____78512))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____78607 -> ret (t3, ctrl1))))

and (ctrl_tac_fold_args :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl ->
        FStar_Syntax_Syntax.arg Prims.list ->
          FStar_Syntax_Syntax.arg Prims.list ctrl_tac)
  =
  fun f  ->
    fun env  ->
      fun ctrl  ->
        fun ts  ->
          match ts with
          | [] -> ret ([], ctrl)
          | (t,q)::ts1 ->
              let uu____78654 = ctrl_tac_fold f env ctrl t  in
              bind uu____78654
                (fun uu____78678  ->
                   match uu____78678 with
                   | (t1,ctrl1) ->
                       let uu____78693 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____78693
                         (fun uu____78720  ->
                            match uu____78720 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      unit tac ->
        FStar_Options.optionstate ->
          Prims.string ->
            FStar_TypeChecker_Env.env ->
              FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps  ->
    fun ctrl  ->
      fun rewriter  ->
        fun opts  ->
          fun label1  ->
            fun env  ->
              fun t  ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let uu____78814 =
                  let uu____78822 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____78822
                    (fun uu____78833  ->
                       let uu____78834 = ctrl t1  in
                       bind uu____78834
                         (fun res  ->
                            let uu____78861 = trivial ()  in
                            bind uu____78861 (fun uu____78870  -> ret res)))
                   in
                bind uu____78814
                  (fun uu____78888  ->
                     match uu____78888 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____78917 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_78926 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_78926.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_78926.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_78926.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_78926.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_78926.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_78926.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_78926.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_78926.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_78926.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_78926.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_78926.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_78926.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_78926.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_78926.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_78926.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_78926.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_78926.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_78926.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_78926.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_78926.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_78926.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_78926.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_78926.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_78926.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_78926.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_78926.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_78926.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_78926.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_78926.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_78926.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_78926.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_78926.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_78926.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_78926.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_78926.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_78926.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_78926.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_78926.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_78926.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_78926.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_78926.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_78926.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____78917 with
                            | (t2,lcomp,g) ->
                                let uu____78937 =
                                  (let uu____78941 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____78941) ||
                                    (let uu____78944 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____78944)
                                   in
                                if uu____78937
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____78960 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____78960
                                     (fun uu____78981  ->
                                        match uu____78981 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____78998  ->
                                                  let uu____78999 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____79001 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____78999 uu____79001);
                                             (let uu____79004 =
                                                let uu____79007 =
                                                  let uu____79008 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____79008 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____79007 opts label1
                                                 in
                                              bind uu____79004
                                                (fun uu____79016  ->
                                                   let uu____79017 =
                                                     bind rewriter
                                                       (fun uu____79031  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____79037 
                                                               ->
                                                               let uu____79038
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____79040
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____79038
                                                                 uu____79040);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____79017)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____79086 =
        bind get
          (fun ps  ->
             let uu____79096 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79096 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79134  ->
                       let uu____79135 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____79135);
                  bind dismiss_all
                    (fun uu____79140  ->
                       let uu____79141 =
                         let uu____79148 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79148
                           keepGoing gt1
                          in
                       bind uu____79141
                         (fun uu____79160  ->
                            match uu____79160 with
                            | (gt',uu____79168) ->
                                (log ps
                                   (fun uu____79172  ->
                                      let uu____79173 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____79173);
                                 (let uu____79176 = push_goals gs  in
                                  bind uu____79176
                                    (fun uu____79181  ->
                                       let uu____79182 =
                                         let uu____79185 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____79185]  in
                                       add_goals uu____79182)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____79086
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____79210 =
        bind get
          (fun ps  ->
             let uu____79220 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79220 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79258  ->
                       let uu____79259 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____79259);
                  bind dismiss_all
                    (fun uu____79264  ->
                       let uu____79265 =
                         let uu____79268 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79268 gt1
                          in
                       bind uu____79265
                         (fun gt'  ->
                            log ps
                              (fun uu____79276  ->
                                 let uu____79277 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____79277);
                            (let uu____79280 = push_goals gs  in
                             bind uu____79280
                               (fun uu____79285  ->
                                  let uu____79286 =
                                    let uu____79289 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____79289]  in
                                  add_goals uu____79286))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____79210
  
let (trefl : unit -> unit tac) =
  fun uu____79302  ->
    let uu____79305 =
      let uu____79308 = cur_goal ()  in
      bind uu____79308
        (fun g  ->
           let uu____79326 =
             let uu____79331 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____79331  in
           match uu____79326 with
           | FStar_Pervasives_Native.Some t ->
               let uu____79339 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____79339 with
                | (hd1,args) ->
                    let uu____79378 =
                      let uu____79391 =
                        let uu____79392 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____79392.FStar_Syntax_Syntax.n  in
                      (uu____79391, args)  in
                    (match uu____79378 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____79406::(l,uu____79408)::(r,uu____79410)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____79457 =
                           let uu____79461 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____79461 l r  in
                         bind uu____79457
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____79472 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79472 l
                                    in
                                 let r1 =
                                   let uu____79474 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79474 r
                                    in
                                 let uu____79475 =
                                   let uu____79479 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____79479 l1 r1  in
                                 bind uu____79475
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____79489 =
                                           let uu____79491 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79491 l1  in
                                         let uu____79492 =
                                           let uu____79494 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79494 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____79489 uu____79492))))
                     | (hd2,uu____79497) ->
                         let uu____79514 =
                           let uu____79516 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____79516 t  in
                         fail1 "trefl: not an equality (%s)" uu____79514))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____79305
  
let (dup : unit -> unit tac) =
  fun uu____79533  ->
    let uu____79536 = cur_goal ()  in
    bind uu____79536
      (fun g  ->
         let uu____79542 =
           let uu____79549 = FStar_Tactics_Types.goal_env g  in
           let uu____79550 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____79549 uu____79550  in
         bind uu____79542
           (fun uu____79560  ->
              match uu____79560 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_79570 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_79570.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_79570.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_79570.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_79570.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____79573  ->
                       let uu____79574 =
                         let uu____79577 = FStar_Tactics_Types.goal_env g  in
                         let uu____79578 =
                           let uu____79579 =
                             let uu____79580 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____79581 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____79580
                               uu____79581
                              in
                           let uu____79582 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____79583 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____79579 uu____79582 u
                             uu____79583
                            in
                         add_irrelevant_goal "dup equation" uu____79577
                           uu____79578 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____79574
                         (fun uu____79587  ->
                            let uu____79588 = add_goals [g']  in
                            bind uu____79588 (fun uu____79592  -> ret ())))))
  
let rec longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs,y::ys) ->
              let uu____79718 = f x y  in
              if uu____79718 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____79741 -> (acc, l11, l21)  in
        let uu____79756 = aux [] l1 l2  in
        match uu____79756 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal tac)
  =
  fun g1  ->
    fun g2  ->
      let close_forall_no_univs1 bs f =
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f
         in
      let uu____79862 = get_phi g1  in
      match uu____79862 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____79869 = get_phi g2  in
          (match uu____79869 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____79882 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____79882 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____79913 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____79913 phi1  in
                    let t2 =
                      let uu____79923 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____79923 phi2  in
                    let uu____79932 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____79932
                      (fun uu____79937  ->
                         let uu____79938 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____79938
                           (fun uu____79945  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_79950 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____79951 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_79950.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_79950.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_79950.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_79950.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____79951;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_79950.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_79950.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_79950.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_79950.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_79950.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_79950.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_79950.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_79950.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_79950.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_79950.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_79950.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_79950.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_79950.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_79950.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_79950.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_79950.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_79950.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_79950.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_79950.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_79950.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_79950.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_79950.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_79950.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_79950.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_79950.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_79950.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_79950.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_79950.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_79950.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_79950.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_79950.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_79950.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_79950.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_79950.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_79950.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_79950.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_79950.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____79955 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____79955
                                (fun goal  ->
                                   mlog
                                     (fun uu____79965  ->
                                        let uu____79966 =
                                          goal_to_string_verbose g1  in
                                        let uu____79968 =
                                          goal_to_string_verbose g2  in
                                        let uu____79970 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____79966 uu____79968 uu____79970)
                                     (fun uu____79974  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____79982  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____79998 =
               set
                 (let uu___2195_80003 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_80003.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_80003.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_80003.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_80003.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_80003.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_80003.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_80003.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_80003.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_80003.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_80003.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_80003.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_80003.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____79998
               (fun uu____80006  ->
                  let uu____80007 = join_goals g1 g2  in
                  bind uu____80007 (fun g12  -> add_goals [g12]))
         | uu____80012 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____80034 =
      let uu____80041 = cur_goal ()  in
      bind uu____80041
        (fun g  ->
           let uu____80051 =
             let uu____80060 = FStar_Tactics_Types.goal_env g  in
             __tc uu____80060 t  in
           bind uu____80051
             (fun uu____80088  ->
                match uu____80088 with
                | (t1,typ,guard) ->
                    let uu____80104 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____80104 with
                     | (hd1,args) ->
                         let uu____80153 =
                           let uu____80168 =
                             let uu____80169 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____80169.FStar_Syntax_Syntax.n  in
                           (uu____80168, args)  in
                         (match uu____80153 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____80190)::(q,uu____80192)::[]) when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid
                              ->
                              let v_p =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None p
                                 in
                              let v_q =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None q
                                 in
                              let g1 =
                                let uu____80246 =
                                  let uu____80247 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80247
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80246
                                 in
                              let g2 =
                                let uu____80249 =
                                  let uu____80250 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80250
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80249
                                 in
                              bind __dismiss
                                (fun uu____80257  ->
                                   let uu____80258 = add_goals [g1; g2]  in
                                   bind uu____80258
                                     (fun uu____80267  ->
                                        let uu____80268 =
                                          let uu____80273 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____80274 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____80273, uu____80274)  in
                                        ret uu____80268))
                          | uu____80279 ->
                              let uu____80294 =
                                let uu____80296 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____80296 typ  in
                              fail1 "Not a disjunction: %s" uu____80294))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____80034
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____80331 =
      let uu____80334 = cur_goal ()  in
      bind uu____80334
        (fun g  ->
           FStar_Options.push ();
           (let uu____80347 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____80347);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_80354 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_80354.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_80354.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_80354.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_80354.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____80331
  
let (top_env : unit -> env tac) =
  fun uu____80371  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____80386  ->
    let uu____80390 = cur_goal ()  in
    bind uu____80390
      (fun g  ->
         let uu____80397 =
           (FStar_Options.lax ()) ||
             (let uu____80400 = FStar_Tactics_Types.goal_env g  in
              uu____80400.FStar_TypeChecker_Env.lax)
            in
         ret uu____80397)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____80417 =
        mlog
          (fun uu____80422  ->
             let uu____80423 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____80423)
          (fun uu____80428  ->
             let uu____80429 = cur_goal ()  in
             bind uu____80429
               (fun goal  ->
                  let env =
                    let uu____80437 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____80437 ty  in
                  let uu____80438 = __tc_ghost env tm  in
                  bind uu____80438
                    (fun uu____80457  ->
                       match uu____80457 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____80471  ->
                                let uu____80472 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____80472)
                             (fun uu____80476  ->
                                mlog
                                  (fun uu____80479  ->
                                     let uu____80480 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____80480)
                                  (fun uu____80485  ->
                                     let uu____80486 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____80486
                                       (fun uu____80491  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____80417
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____80516 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____80522 =
              let uu____80529 =
                let uu____80530 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____80530
                 in
              new_uvar "uvar_env.2" env uu____80529  in
            bind uu____80522
              (fun uu____80547  ->
                 match uu____80547 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____80516
        (fun typ  ->
           let uu____80559 = new_uvar "uvar_env" env typ  in
           bind uu____80559
             (fun uu____80574  ->
                match uu____80574 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____80593 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____80612 -> g.FStar_Tactics_Types.opts
             | uu____80615 -> FStar_Options.peek ()  in
           let uu____80618 = FStar_Syntax_Util.head_and_args t  in
           match uu____80618 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____80638);
                FStar_Syntax_Syntax.pos = uu____80639;
                FStar_Syntax_Syntax.vars = uu____80640;_},uu____80641)
               ->
               let env1 =
                 let uu___2286_80683 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_80683.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_80683.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_80683.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_80683.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_80683.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_80683.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_80683.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_80683.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_80683.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_80683.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_80683.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_80683.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_80683.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_80683.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_80683.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_80683.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_80683.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_80683.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_80683.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_80683.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_80683.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_80683.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_80683.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_80683.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_80683.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_80683.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_80683.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_80683.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_80683.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_80683.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_80683.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_80683.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_80683.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_80683.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_80683.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_80683.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_80683.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_80683.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_80683.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_80683.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_80683.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_80683.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____80687 =
                 let uu____80690 = bnorm_goal g  in [uu____80690]  in
               add_goals uu____80687
           | uu____80691 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____80593
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____80753 = if b then t2 else ret false  in
             bind uu____80753 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____80779 = trytac comp  in
      bind uu____80779
        (fun uu___613_80791  ->
           match uu___613_80791 with
           | FStar_Pervasives_Native.Some (true ) -> ret true
           | FStar_Pervasives_Native.Some (false ) -> failwith "impossible"
           | FStar_Pervasives_Native.None  -> ret false)
  
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun e  ->
    fun t1  ->
      fun t2  ->
        let uu____80833 =
          bind get
            (fun ps  ->
               let uu____80841 = __tc e t1  in
               bind uu____80841
                 (fun uu____80862  ->
                    match uu____80862 with
                    | (t11,ty1,g1) ->
                        let uu____80875 = __tc e t2  in
                        bind uu____80875
                          (fun uu____80896  ->
                             match uu____80896 with
                             | (t21,ty2,g2) ->
                                 let uu____80909 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____80909
                                   (fun uu____80916  ->
                                      let uu____80917 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____80917
                                        (fun uu____80925  ->
                                           let uu____80926 =
                                             do_unify e ty1 ty2  in
                                           let uu____80930 =
                                             do_unify e t11 t21  in
                                           tac_and uu____80926 uu____80930)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____80833
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____80978  ->
             let uu____80979 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____80979
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (fresh_bv_named :
  Prims.string -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.bv tac) =
  fun nm  ->
    fun t  ->
      bind idtac
        (fun uu____81013  ->
           let uu____81014 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____81014)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____81025 =
      mlog
        (fun uu____81030  ->
           let uu____81031 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____81031)
        (fun uu____81036  ->
           let uu____81037 = cur_goal ()  in
           bind uu____81037
             (fun g  ->
                let uu____81043 =
                  let uu____81052 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____81052 ty  in
                bind uu____81043
                  (fun uu____81064  ->
                     match uu____81064 with
                     | (ty1,uu____81074,guard) ->
                         let uu____81076 =
                           let uu____81079 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____81079 guard  in
                         bind uu____81076
                           (fun uu____81083  ->
                              let uu____81084 =
                                let uu____81088 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____81089 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____81088 uu____81089 ty1  in
                              bind uu____81084
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____81098 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____81098
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____81105 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____81106 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____81105
                                          uu____81106
                                         in
                                      let nty =
                                        let uu____81108 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____81108 ty1  in
                                      let uu____81109 =
                                        let uu____81113 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____81113 ng nty  in
                                      bind uu____81109
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____81122 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____81122
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____81025
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____81196 =
      let uu____81205 = cur_goal ()  in
      bind uu____81205
        (fun g  ->
           let uu____81217 =
             let uu____81226 = FStar_Tactics_Types.goal_env g  in
             __tc uu____81226 s_tm  in
           bind uu____81217
             (fun uu____81244  ->
                match uu____81244 with
                | (s_tm1,s_ty,guard) ->
                    let uu____81262 =
                      let uu____81265 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____81265 guard  in
                    bind uu____81262
                      (fun uu____81278  ->
                         let uu____81279 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____81279 with
                         | (h,args) ->
                             let uu____81324 =
                               let uu____81331 =
                                 let uu____81332 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____81332.FStar_Syntax_Syntax.n  in
                               match uu____81331 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____81347;
                                      FStar_Syntax_Syntax.vars = uu____81348;_},us)
                                   -> ret (fv, us)
                               | uu____81358 -> fail "type is not an fv"  in
                             bind uu____81324
                               (fun uu____81379  ->
                                  match uu____81379 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____81395 =
                                        let uu____81398 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____81398 t_lid
                                         in
                                      (match uu____81395 with
                                       | FStar_Pervasives_Native.None  ->
                                           fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid,t_us,t_ps,t_ty,mut,c_lids)
                                                ->
                                                failwhen
                                                  ((FStar_List.length a_us)
                                                     <>
                                                     (FStar_List.length t_us))
                                                  "t_us don't match?"
                                                  (fun uu____81449  ->
                                                     let uu____81450 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____81450 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____81465 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____81493
                                                                  =
                                                                  let uu____81496
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____81496
                                                                    c_lid
                                                                   in
                                                                match uu____81493
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail
                                                                    "ctor not found?"
                                                                | FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (
                                                                    match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    (_c_lid,c_us,c_ty,_t_lid,nparam,mut1)
                                                                    ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor)
                                                                     in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____81570
                                                                     ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us
                                                                     in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty
                                                                     in
                                                                    let uu____81575
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____81575
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____81598
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____81598
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____81641
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____81641
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____81714
                                                                    =
                                                                    let uu____81716
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____81716
                                                                     in
                                                                    failwhen
                                                                    uu____81714
                                                                    "not total?"
                                                                    (fun
                                                                    uu____81735
                                                                     ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    }  in
                                                                    let is_imp
                                                                    uu___614_81752
                                                                    =
                                                                    match uu___614_81752
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____81756)
                                                                    -> true
                                                                    | 
                                                                    uu____81759
                                                                    -> false
                                                                     in
                                                                    let uu____81763
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____81763
                                                                    with
                                                                    | 
                                                                    (a_ps,a_is)
                                                                    ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____81897
                                                                     ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____81959
                                                                     ->
                                                                    match uu____81959
                                                                    with
                                                                    | 
                                                                    ((bv,uu____81979),
                                                                    (t,uu____81981))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let bs2 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs1  in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____82051
                                                                     ->
                                                                    match uu____82051
                                                                    with
                                                                    | 
                                                                    ((bv,uu____82078),
                                                                    (t,uu____82080))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____82139
                                                                     ->
                                                                    match uu____82139
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs2
                                                                     in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2
                                                                     in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats))
                                                                     in
                                                                    let env =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g  in
                                                                    let equ =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env s_ty
                                                                     in
                                                                    let uu____82194
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_82211
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_82211.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____82194
                                                                    with
                                                                    | 
                                                                    (uu____82225,uu____82226,uu____82227,pat_t,uu____82229,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____82236
                                                                    =
                                                                    let uu____82237
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____82237
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____82236
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____82242
                                                                    =
                                                                    let uu____82251
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____82251]
                                                                     in
                                                                    let uu____82270
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____82242
                                                                    uu____82270
                                                                     in
                                                                    let nty =
                                                                    let uu____82276
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____82276
                                                                     in
                                                                    let uu____82279
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____82279
                                                                    (fun
                                                                    uu____82309
                                                                     ->
                                                                    match uu____82309
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label
                                                                     in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs2
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____82336
                                                                    =
                                                                    let uu____82347
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____82347]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____82336
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____82383
                                                                    =
                                                                    let uu____82394
                                                                    =
                                                                    let uu____82399
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____82399)
                                                                     in
                                                                    (g', br,
                                                                    uu____82394)
                                                                     in
                                                                    ret
                                                                    uu____82383))))))
                                                                    | 
                                                                    uu____82420
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____81465
                                                           (fun goal_brs  ->
                                                              let uu____82470
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____82470
                                                              with
                                                              | (goals,brs,infos)
                                                                  ->
                                                                  let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                  let uu____82543
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____82543
                                                                    (
                                                                    fun
                                                                    uu____82554
                                                                     ->
                                                                    let uu____82555
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____82555
                                                                    (fun
                                                                    uu____82565
                                                                     ->
                                                                    ret infos))))
                                            | uu____82572 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____81196
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____82621::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____82651 = init xs  in x :: uu____82651
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____82664 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____82673) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____82739 = last args  in
          (match uu____82739 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____82769 =
                 let uu____82770 =
                   let uu____82775 =
                     let uu____82776 =
                       let uu____82781 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____82781  in
                     uu____82776 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____82775, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____82770  in
               FStar_All.pipe_left ret uu____82769)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____82794,uu____82795) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____82848 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____82848 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____82890 =
                      let uu____82891 =
                        let uu____82896 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____82896)  in
                      FStar_Reflection_Data.Tv_Abs uu____82891  in
                    FStar_All.pipe_left ret uu____82890))
      | FStar_Syntax_Syntax.Tm_type uu____82899 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____82924 ->
          let uu____82939 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____82939 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____82970 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____82970 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____83023 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____83036 =
            let uu____83037 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____83037  in
          FStar_All.pipe_left ret uu____83036
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____83058 =
            let uu____83059 =
              let uu____83064 =
                let uu____83065 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____83065  in
              (uu____83064, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____83059  in
          FStar_All.pipe_left ret uu____83058
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____83105 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____83110 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____83110 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____83163 ->
                            failwith
                              "impossible: open_term returned different amount of binders"
                         in
                      FStar_All.pipe_left ret
                        (FStar_Reflection_Data.Tv_Let
                           (false, (FStar_Pervasives_Native.fst b1),
                             (lb.FStar_Syntax_Syntax.lbdef), t22))))
      | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____83205 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____83209 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____83209 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____83229 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____83235 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____83290 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____83290
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____83311 =
                  let uu____83318 =
                    FStar_List.map
                      (fun uu____83331  ->
                         match uu____83331 with
                         | (p1,uu____83340) -> inspect_pat p1) ps
                     in
                  (fv, uu____83318)  in
                FStar_Reflection_Data.Pat_Cons uu____83311
            | FStar_Syntax_Syntax.Pat_var bv ->
                FStar_Reflection_Data.Pat_Var bv
            | FStar_Syntax_Syntax.Pat_wild bv ->
                FStar_Reflection_Data.Pat_Wild bv
            | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
             in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
          let brs2 =
            FStar_List.map
              (fun uu___615_83436  ->
                 match uu___615_83436 with
                 | (pat,uu____83458,t5) ->
                     let uu____83476 = inspect_pat pat  in (uu____83476, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____83485 ->
          ((let uu____83487 =
              let uu____83493 =
                let uu____83495 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____83497 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____83495 uu____83497
                 in
              (FStar_Errors.Warning_CantInspect, uu____83493)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____83487);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____82664
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____83515 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____83515
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____83519 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____83519
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____83523 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____83523
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____83530 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____83530
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____83555 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____83555
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____83572 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____83572
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____83591 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____83591
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____83595 =
          let uu____83596 =
            let uu____83603 =
              let uu____83604 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____83604  in
            FStar_Syntax_Syntax.mk uu____83603  in
          uu____83596 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83595
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____83612 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83612
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83623 =
          let uu____83624 =
            let uu____83631 =
              let uu____83632 =
                let uu____83646 =
                  let uu____83649 =
                    let uu____83650 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____83650]  in
                  FStar_Syntax_Subst.close uu____83649 t2  in
                ((false, [lb]), uu____83646)  in
              FStar_Syntax_Syntax.Tm_let uu____83632  in
            FStar_Syntax_Syntax.mk uu____83631  in
          uu____83624 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83623
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83695 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____83695 with
         | (lbs,body) ->
             let uu____83710 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____83710)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____83747 =
                let uu____83748 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____83748  in
              FStar_All.pipe_left wrap uu____83747
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____83755 =
                let uu____83756 =
                  let uu____83770 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____83788 = pack_pat p1  in
                         (uu____83788, false)) ps
                     in
                  (fv, uu____83770)  in
                FStar_Syntax_Syntax.Pat_cons uu____83756  in
              FStar_All.pipe_left wrap uu____83755
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv,t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1))
           in
        let brs1 =
          FStar_List.map
            (fun uu___616_83837  ->
               match uu___616_83837 with
               | (pat,t1) ->
                   let uu____83854 = pack_pat pat  in
                   (uu____83854, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____83902 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83902
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____83930 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83930
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____83976 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83976
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____84015 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____84015
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____84035 =
        bind get
          (fun ps  ->
             let uu____84041 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____84041 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____84035
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____84075 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_84082 = ps  in
                 let uu____84083 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_84082.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_84082.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_84082.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_84082.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_84082.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_84082.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_84082.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_84082.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_84082.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_84082.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_84082.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_84082.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____84083
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____84075
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____84110 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____84110 with
      | (u,ctx_uvars,g_u) ->
          let uu____84143 = FStar_List.hd ctx_uvars  in
          (match uu____84143 with
           | (ctx_uvar,uu____84157) ->
               let g =
                 let uu____84159 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____84159 false
                   ""
                  in
               (g, g_u))
  
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng  ->
    fun env  ->
      fun typ  ->
        let uu____84182 = goal_of_goal_ty env typ  in
        match uu____84182 with
        | (g,g_u) ->
            let ps =
              let uu____84194 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____84197 = FStar_Util.psmap_empty ()  in
              {
                FStar_Tactics_Types.main_context = env;
                FStar_Tactics_Types.main_goal = g;
                FStar_Tactics_Types.all_implicits =
                  (g_u.FStar_TypeChecker_Env.implicits);
                FStar_Tactics_Types.goals = [g];
                FStar_Tactics_Types.smt_goals = [];
                FStar_Tactics_Types.depth = (Prims.parse_int "0");
                FStar_Tactics_Types.__dump =
                  (fun ps  -> fun msg  -> dump_proofstate ps msg);
                FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = (Prims.parse_int "0");
                FStar_Tactics_Types.tac_verb_dbg = uu____84194;
                FStar_Tactics_Types.local_state = uu____84197
              }  in
            let uu____84207 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____84207)
  
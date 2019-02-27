open Prims
let (env_hook :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (inspect_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Reflection_Data.aqualv) =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu____61699)
        -> FStar_Reflection_Data.Q_Implicit
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
        FStar_Reflection_Data.Q_Meta t
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        FStar_Reflection_Data.Q_Explicit
    | FStar_Pervasives_Native.None  -> FStar_Reflection_Data.Q_Explicit
  
let (pack_aqual : FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.aqual)
  =
  fun aqv  ->
    match aqv with
    | FStar_Reflection_Data.Q_Explicit  -> FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Q_Implicit  ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit false)
    | FStar_Reflection_Data.Q_Meta t ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t)
  
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    let uu____61724 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____61724
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let lid = FStar_Parser_Const.p2l ns  in
    let fallback uu____61743 =
      let quals =
        let uu____61747 =
          FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid  in
        if uu____61747
        then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
        else
          (let uu____61754 =
             FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid  in
           if uu____61754
           then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
           else
             (let uu____61761 =
                FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid  in
              if uu____61761
              then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
              else
                (let uu____61768 =
                   FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid  in
                 if uu____61768
                 then
                   FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
                 else FStar_Pervasives_Native.None)))
         in
      let uu____61775 = FStar_Parser_Const.p2l ns  in
      FStar_Syntax_Syntax.lid_as_fv uu____61775
        (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "999"))
        quals
       in
    let uu____61777 = FStar_ST.op_Bang env_hook  in
    match uu____61777 with
    | FStar_Pervasives_Native.None  -> fallback ()
    | FStar_Pervasives_Native.Some env ->
        let qninfo = FStar_TypeChecker_Env.lookup_qname env lid  in
        (match qninfo with
         | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,_us),_rng) ->
             let quals = FStar_Syntax_DsEnv.fv_qual_of_se se  in
             let uu____61857 = FStar_Parser_Const.p2l ns  in
             FStar_Syntax_Syntax.lid_as_fv uu____61857
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "999")) quals
         | uu____61859 -> fallback ())
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____61878::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____61908 = init xs  in x :: uu____61908
  
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____61918) ->
        let uu____61933 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____61933
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____61937) ->
        FStar_Reflection_Data.C_String s
    | FStar_Const.Const_range r -> FStar_Reflection_Data.C_Range r
    | FStar_Const.Const_reify  -> FStar_Reflection_Data.C_Reify
    | FStar_Const.Const_reflect l ->
        let uu____61942 = FStar_Ident.path_of_lid l  in
        FStar_Reflection_Data.C_Reflect uu____61942
    | uu____61943 ->
        let uu____61944 =
          let uu____61946 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____61946  in
        failwith uu____61944
  
let rec (inspect_ln :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    let t3 = FStar_Syntax_Util.unlazy_emb t2  in
    match t3.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t4,uu____61959) -> inspect_ln t4
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Reflection_Data.Tv_Var bv
    | FStar_Syntax_Syntax.Tm_bvar bv -> FStar_Reflection_Data.Tv_BVar bv
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect_ln: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____62017 = last args  in
        (match uu____62017 with
         | (a,q) ->
             let q' = inspect_aqual q  in
             let uu____62045 =
               let uu____62050 =
                 let uu____62051 =
                   let uu____62056 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____62056  in
                 uu____62051 FStar_Pervasives_Native.None
                   t3.FStar_Syntax_Syntax.pos
                  in
               (uu____62050, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____62045)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____62067,uu____62068) ->
        failwith "inspect_ln: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t4,k) ->
        let body =
          match bs with
          | [] -> t4
          | bs1 ->
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_abs (bs1, t4, k))
                FStar_Pervasives_Native.None t4.FStar_Syntax_Syntax.pos
           in
        FStar_Reflection_Data.Tv_Abs (b, body)
    | FStar_Syntax_Syntax.Tm_type uu____62160 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect_ln: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____62181 ->
        let uu____62196 = FStar_Syntax_Util.arrow_one t3  in
        (match uu____62196 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
        FStar_Reflection_Data.Tv_Refine (bv, t4)
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____62221 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____62221
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
        let uu____62240 =
          let uu____62245 =
            let uu____62246 =
              FStar_Syntax_Unionfind.uvar_id
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            FStar_BigInt.of_int_fs uu____62246  in
          (uu____62245, (ctx_u, s))  in
        FStar_Reflection_Data.Tv_Uvar uu____62240
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____62278 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (false, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____62304 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (true, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____62357 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____62357
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____62378 =
                let uu____62385 =
                  FStar_List.map
                    (fun uu____62398  ->
                       match uu____62398 with
                       | (p1,uu____62407) -> inspect_pat p1) ps
                   in
                (fv, uu____62385)  in
              FStar_Reflection_Data.Pat_Cons uu____62378
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
           in
        let brs1 =
          FStar_List.map
            (fun uu___522_62458  ->
               match uu___522_62458 with
               | (pat,uu____62480,t5) ->
                   let uu____62498 = inspect_pat pat  in (uu____62498, t5))
            brs
           in
        FStar_Reflection_Data.Tv_Match (t4, brs1)
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Reflection_Data.Tv_Unknown
    | uu____62503 ->
        ((let uu____62505 =
            let uu____62511 =
              let uu____62513 = FStar_Syntax_Print.tag_of_term t3  in
              let uu____62515 = FStar_Syntax_Print.term_to_string t3  in
              FStar_Util.format2
                "inspect_ln: outside of expected syntax (%s, %s)\n"
                uu____62513 uu____62515
               in
            (FStar_Errors.Warning_CantInspect, uu____62511)  in
          FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____62505);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____62526) ->
        FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____62538 =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
           in
        if uu____62538
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____62542)::(post,uu____62544)::uu____62545 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____62588 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          (let uu____62602 =
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Tot_lid
              in
           if uu____62602
           then
             let maybe_dec =
               FStar_List.tryFind
                 (fun uu___523_62610  ->
                    match uu___523_62610 with
                    | FStar_Syntax_Syntax.DECREASES uu____62612 -> true
                    | uu____62616 -> false) ct.FStar_Syntax_Syntax.flags
                in
             let md =
               match maybe_dec with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   t) -> FStar_Pervasives_Native.Some t
               | uu____62626 -> failwith "impossible"  in
             FStar_Reflection_Data.C_Total
               ((ct.FStar_Syntax_Syntax.result_typ), md)
           else FStar_Reflection_Data.C_Unknown)
    | FStar_Syntax_Syntax.GTotal uu____62636 ->
        FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total (t,uu____62652) ->
        FStar_Syntax_Syntax.mk_Total t
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let ct =
          let uu____62660 =
            let uu____62671 = FStar_Syntax_Syntax.as_arg pre  in
            let uu____62680 =
              let uu____62691 = FStar_Syntax_Syntax.as_arg post  in
              [uu____62691]  in
            uu____62671 :: uu____62680  in
          {
            FStar_Syntax_Syntax.comp_univs = [];
            FStar_Syntax_Syntax.effect_name =
              FStar_Parser_Const.effect_Lemma_lid;
            FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
            FStar_Syntax_Syntax.effect_args = uu____62660;
            FStar_Syntax_Syntax.flags = []
          }  in
        FStar_Syntax_Syntax.mk_Comp ct
    | uu____62724 -> failwith "cannot pack a C_Unknown"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____62733 =
          let uu____62745 = FStar_BigInt.string_of_big_int i  in
          (uu____62745, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____62733
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
    | FStar_Reflection_Data.C_Range r -> FStar_Const.Const_range r
    | FStar_Reflection_Data.C_Reify  -> FStar_Const.Const_reify
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____62765 = FStar_Ident.lid_of_path ns FStar_Range.dummyRange
           in
        FStar_Const.Const_reflect uu____62765
  
let (pack_ln : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv -> FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_BVar bv -> FStar_Syntax_Syntax.bv_to_tm bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = pack_aqual q  in FStar_Syntax_Util.mk_app l [(r, q')]
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) -> FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____62830 =
          let uu____62837 =
            let uu____62838 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____62838  in
          FStar_Syntax_Syntax.mk uu____62837  in
        uu____62830 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,ctx_u_s) ->
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((false, [lb]), t2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((true, [lb]), t2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____62907 =
                let uu____62908 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____62908  in
              FStar_All.pipe_left wrap uu____62907
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____62915 =
                let uu____62916 =
                  let uu____62930 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____62948 = pack_pat p1  in
                         (uu____62948, false)) ps
                     in
                  (fv, uu____62930)  in
                FStar_Syntax_Syntax.Pat_cons uu____62916  in
              FStar_All.pipe_left wrap uu____62915
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
            (fun uu___524_62997  ->
               match uu___524_62997 with
               | (pat,t1) ->
                   let uu____63014 = pack_pat pat  in
                   (uu____63014, FStar_Pervasives_Native.None, t1)) brs
           in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs1))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inl t), tacopt), FStar_Pervasives_Native.None))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inr c), tacopt), FStar_Pervasives_Native.None))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
          FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (compare_bv :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv -> FStar_Order.order) =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv x y  in
      if n1 < (Prims.parse_int "0")
      then FStar_Order.Lt
      else
        if n1 = (Prims.parse_int "0") then FStar_Order.Eq else FStar_Order.Gt
  
let (is_free :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun x  -> fun t  -> FStar_Syntax_Util.is_free_in x t 
let (lookup_attr :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv Prims.list)
  =
  fun attr  ->
    fun env  ->
      let uu____63175 =
        let uu____63176 = FStar_Syntax_Subst.compress attr  in
        uu____63176.FStar_Syntax_Syntax.n  in
      match uu____63175 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let ses =
            let uu____63185 =
              let uu____63187 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_Ident.text_of_lid uu____63187  in
            FStar_TypeChecker_Env.lookup_attr env uu____63185  in
          FStar_List.concatMap
            (fun se  ->
               let uu____63191 = FStar_Syntax_Util.lid_of_sigelt se  in
               match uu____63191 with
               | FStar_Pervasives_Native.None  -> []
               | FStar_Pervasives_Native.Some l ->
                   let uu____63197 =
                     FStar_Syntax_Syntax.lid_as_fv l
                       (FStar_Syntax_Syntax.Delta_constant_at_level
                          (Prims.parse_int "999"))
                       FStar_Pervasives_Native.None
                      in
                   [uu____63197]) ses
      | uu____63199 -> []
  
let (lookup_typ :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns  in
      FStar_TypeChecker_Env.lookup_sigelt env lid
  
let (sigelt_attrs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.attribute Prims.list) =
  fun se  -> se.FStar_Syntax_Syntax.sigattrs 
let (set_sigelt_attrs :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun attrs  ->
    fun se  ->
      let uu___885_63247 = se  in
      {
        FStar_Syntax_Syntax.sigel =
          (uu___885_63247.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng =
          (uu___885_63247.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals =
          (uu___885_63247.FStar_Syntax_Syntax.sigquals);
        FStar_Syntax_Syntax.sigmeta =
          (uu___885_63247.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = attrs
      }
  
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.sigelt_view) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let ((r,lb::[]),uu____63256) ->
        let fv =
          match lb.FStar_Syntax_Syntax.lbname with
          | FStar_Util.Inr fv -> fv
          | FStar_Util.Inl uu____63267 ->
              failwith "impossible: global Sig_let has bv"
           in
        let uu____63269 =
          FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs
           in
        (match uu____63269 with
         | (s,us) ->
             let typ =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbtyp  in
             let def =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbdef  in
             FStar_Reflection_Data.Sg_Let
               (r, fv, (lb.FStar_Syntax_Syntax.lbunivs),
                 (lb.FStar_Syntax_Syntax.lbtyp),
                 (lb.FStar_Syntax_Syntax.lbdef)))
    | FStar_Syntax_Syntax.Sig_inductive_typ (lid,us,bs,ty,uu____63297,c_lids)
        ->
        let nm = FStar_Ident.path_of_lid lid  in
        let uu____63308 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____63308 with
         | (s,us1) ->
             let bs1 = FStar_Syntax_Subst.subst_binders s bs  in
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____63329 =
               let uu____63346 =
                 FStar_List.map FStar_Ident.path_of_lid c_lids  in
               (nm, us1, bs1, ty1, uu____63346)  in
             FStar_Reflection_Data.Sg_Inductive uu____63329)
    | FStar_Syntax_Syntax.Sig_datacon (lid,us,ty,uu____63358,n1,uu____63360)
        ->
        let uu____63367 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____63367 with
         | (s,us1) ->
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____63387 =
               let uu____63392 = FStar_Ident.path_of_lid lid  in
               (uu____63392, ty1)  in
             FStar_Reflection_Data.Sg_Constructor uu____63387)
    | uu____63393 -> FStar_Reflection_Data.Unk
  
let (pack_sigelt :
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.sigelt) =
  fun sv  ->
    match sv with
    | FStar_Reflection_Data.Sg_Let (r,fv,univs1,typ,def) ->
        let s = FStar_Syntax_Subst.univ_var_closing univs1  in
        let typ1 = FStar_Syntax_Subst.subst s typ  in
        let def1 = FStar_Syntax_Subst.subst s def  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inr fv) univs1 typ1
            FStar_Parser_Const.effect_Tot_lid def1 []
            def1.FStar_Syntax_Syntax.pos
           in
        let uu____63419 =
          let uu____63420 =
            let uu____63427 =
              let uu____63430 = FStar_Syntax_Syntax.lid_of_fv fv  in
              [uu____63430]  in
            ((r, [lb]), uu____63427)  in
          FStar_Syntax_Syntax.Sig_let uu____63420  in
        FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____63419
    | FStar_Reflection_Data.Sg_Constructor uu____63436 ->
        failwith "packing Sg_Constructor, sorry"
    | FStar_Reflection_Data.Sg_Inductive uu____63442 ->
        failwith "packing Sg_Inductive, sorry"
    | FStar_Reflection_Data.Unk  -> failwith "packing Unk, sorry"
  
let (inspect_bv : FStar_Syntax_Syntax.bv -> FStar_Reflection_Data.bv_view) =
  fun bv  ->
    let uu____63467 =
      FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname  in
    let uu____63469 = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index  in
    {
      FStar_Reflection_Data.bv_ppname = uu____63467;
      FStar_Reflection_Data.bv_index = uu____63469;
      FStar_Reflection_Data.bv_sort = (bv.FStar_Syntax_Syntax.sort)
    }
  
let (pack_bv : FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.bv) =
  fun bvv  ->
    let uu____63476 =
      FStar_Ident.mk_ident
        ((bvv.FStar_Reflection_Data.bv_ppname), FStar_Range.dummyRange)
       in
    let uu____63478 =
      FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index  in
    {
      FStar_Syntax_Syntax.ppname = uu____63476;
      FStar_Syntax_Syntax.index = uu____63478;
      FStar_Syntax_Syntax.sort = (bvv.FStar_Reflection_Data.bv_sort)
    }
  
let (inspect_binder :
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.bv * FStar_Reflection_Data.aqualv))
  =
  fun b  ->
    let uu____63494 = b  in
    match uu____63494 with
    | (bv,aq) -> let uu____63505 = inspect_aqual aq  in (bv, uu____63505)
  
let (pack_binder :
  FStar_Syntax_Syntax.bv ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.binder)
  =
  fun bv  ->
    fun aqv  -> let uu____63517 = pack_aqual aqv  in (bv, uu____63517)
  
let (moduleof : FStar_TypeChecker_Env.env -> Prims.string Prims.list) =
  fun e  -> FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule 
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____63552 = FStar_Syntax_Util.un_uinst t1  in
      let uu____63553 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____63552 uu____63553
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 
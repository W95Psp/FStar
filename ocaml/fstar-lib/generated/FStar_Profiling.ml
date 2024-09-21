open Prims
type counter =
  {
  cid: Prims.string ;
  total_time: Prims.int FStar_Compiler_Effect.ref ;
  running: Prims.bool FStar_Compiler_Effect.ref ;
  undercount: Prims.bool FStar_Compiler_Effect.ref }
let (__proj__Mkcounter__item__cid : counter -> Prims.string) =
  fun projectee ->
    match projectee with | { cid; total_time; running; undercount;_} -> cid
let (__proj__Mkcounter__item__total_time :
  counter -> Prims.int FStar_Compiler_Effect.ref) =
  fun projectee ->
    match projectee with
    | { cid; total_time; running; undercount;_} -> total_time
let (__proj__Mkcounter__item__running :
  counter -> Prims.bool FStar_Compiler_Effect.ref) =
  fun projectee ->
    match projectee with
    | { cid; total_time; running; undercount;_} -> running
let (__proj__Mkcounter__item__undercount :
  counter -> Prims.bool FStar_Compiler_Effect.ref) =
  fun projectee ->
    match projectee with
    | { cid; total_time; running; undercount;_} -> undercount
let (json_of_counter : counter -> FStar_Json.json) =
  fun c ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Compiler_Effect.op_Bang c.total_time in
            FStar_Json.JsonInt uu___4 in
          ("total_time", uu___3) in
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = FStar_Compiler_Effect.op_Bang c.running in
              FStar_Json.JsonBool uu___6 in
            ("running", uu___5) in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStar_Compiler_Effect.op_Bang c.undercount in
                FStar_Json.JsonBool uu___8 in
              ("undercount", uu___7) in
            [uu___6] in
          uu___4 :: uu___5 in
        uu___2 :: uu___3 in
      ("id", (FStar_Json.JsonStr (c.cid))) :: uu___1 in
    FStar_Json.JsonAssoc uu___
let (new_counter : Prims.string -> counter) =
  fun cid ->
    let uu___ = FStar_Compiler_Util.mk_ref Prims.int_zero in
    let uu___1 = FStar_Compiler_Util.mk_ref false in
    let uu___2 = FStar_Compiler_Util.mk_ref false in
    { cid; total_time = uu___; running = uu___1; undercount = uu___2 }
let (all_counters : counter FStar_Compiler_Util.smap) =
  FStar_Compiler_Util.smap_create (Prims.of_int (20))
let (create_or_lookup_counter : Prims.string -> counter) =
  fun cid ->
    let uu___ = FStar_Compiler_Util.smap_try_find all_counters cid in
    match uu___ with
    | FStar_Pervasives_Native.Some c -> c
    | FStar_Pervasives_Native.None ->
        let c = new_counter cid in
        (FStar_Compiler_Util.smap_add all_counters cid c; c)
let profile :
  'a .
    (unit -> 'a) ->
      Prims.string FStar_Pervasives_Native.option -> Prims.string -> 'a
  =
  fun f ->
    fun module_name ->
      fun cid ->
        let uu___ = FStar_Options.profile_enabled module_name cid in
        if uu___
        then
          let c = create_or_lookup_counter cid in
          let uu___1 = FStar_Compiler_Effect.op_Bang c.running in
          (if uu___1
           then f ()
           else
             (try
                (fun uu___3 ->
                   match () with
                   | () ->
                       (FStar_Compiler_Effect.op_Colon_Equals c.running true;
                        (let uu___5 = FStar_Compiler_Util.record_time f in
                         match uu___5 with
                         | (res, elapsed) ->
                             ((let uu___7 =
                                 let uu___8 =
                                   FStar_Compiler_Effect.op_Bang c.total_time in
                                 uu___8 + elapsed in
                               FStar_Compiler_Effect.op_Colon_Equals
                                 c.total_time uu___7);
                              FStar_Compiler_Effect.op_Colon_Equals c.running
                                false;
                              res)))) ()
              with
              | uu___3 ->
                  (FStar_Compiler_Effect.op_Colon_Equals c.running false;
                   FStar_Compiler_Effect.op_Colon_Equals c.undercount true;
                   FStar_Compiler_Effect.raise uu___3)))
        else f ()
let (report_json : Prims.string -> counter -> unit) =
  fun tag ->
    fun c ->
      let counter1 = json_of_counter c in
      let uu___ =
        FStar_Json.string_of_json
          (FStar_Json.JsonAssoc
             [("tag", (FStar_Json.JsonStr tag)); ("counter", counter1)]) in
      FStar_Compiler_Util.print1_error "%s\n" uu___
let (report_human : Prims.string -> counter -> unit) =
  fun tag ->
    fun c ->
      let warn =
        let uu___ = FStar_Compiler_Effect.op_Bang c.running in
        if uu___
        then " (Warning, this counter is still running)"
        else
          (let uu___2 = FStar_Compiler_Effect.op_Bang c.undercount in
           if uu___2
           then
             " (Warning, some operations raised exceptions and we not accounted for)"
           else "") in
      let uu___ =
        let uu___1 = FStar_Compiler_Effect.op_Bang c.total_time in
        FStar_Compiler_Util.string_of_int uu___1 in
      FStar_Compiler_Util.print4 "%s, profiled %s:\t %s ms%s\n" tag c.cid
        uu___ warn
let (report : Prims.string -> counter -> unit) =
  fun tag ->
    fun c ->
      let uu___ = FStar_Options.message_format () in
      match uu___ with
      | FStar_Options.Human -> report_human tag c
      | FStar_Options.Json -> report_json tag c
let (report_and_clear : Prims.string -> unit) =
  fun tag ->
    let ctrs =
      FStar_Compiler_Util.smap_fold all_counters
        (fun uu___ -> fun v -> fun l -> v :: l) [] in
    FStar_Compiler_Util.smap_clear all_counters;
    (let ctrs1 =
       FStar_Compiler_Util.sort_with
         (fun c1 ->
            fun c2 ->
              let uu___1 = FStar_Compiler_Effect.op_Bang c2.total_time in
              let uu___2 = FStar_Compiler_Effect.op_Bang c1.total_time in
              uu___1 - uu___2) ctrs in
     FStar_Compiler_List.iter (report tag) ctrs1)
(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.Syntax.Print
open FStar.Compiler.Effect
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Const
open FStar.Compiler.Util

module DsEnv = FStar.Syntax.DsEnv

type printing_options = {
  hide_uvar_nums: bool;
  print_bound_var_types: bool;
  print_effect_args: bool;
  print_implicits: bool;
  print_real_names: bool;
  print_universes: bool;
  ugly: bool;
}

val db_to_string          :                    bv -> string
val bv_to_string          : printing_options -> bv -> string
val bvs_to_string         : printing_options -> string -> list bv -> string
val fv_to_string          : printing_options -> fv -> string
val nm_to_string          : printing_options -> bv -> string
val lid_to_string         : printing_options -> lid -> string
val term_to_string        : printing_options -> term -> string
val term_to_string'       : printing_options -> DsEnv.env -> term -> string
val uvar_to_string        : printing_options -> uvar -> string
val comp_to_string        : printing_options -> comp -> string
val comp_to_string'       : printing_options -> DsEnv.env -> comp -> string
val lbs_to_string         : printing_options -> list qualifier -> letbindings -> string
val tag_of_term           : printing_options -> term -> string
val lbname_to_string      : printing_options -> lbname -> string
val pat_to_string         : printing_options -> pat -> string
val branch_to_string      : printing_options -> Syntax.branch -> string
val modul_to_string       : printing_options -> modul -> string
val univ_names_to_string  :                    univ_names -> string
val univ_to_string        : printing_options -> universe -> string
val univs_to_string       : printing_options -> universes -> string
val attrs_to_string       : printing_options -> list attribute -> string
val sigelt_to_string      : printing_options -> sigelt -> string
val sigelt_to_string_short: printing_options -> sigelt -> string
val tag_of_sigelt         : printing_options -> sigelt -> string
val binder_to_string      : printing_options -> binder -> string
val binders_to_string     : printing_options -> string -> binders -> string
val binder_to_json        : printing_options -> DsEnv.env -> binder -> json
val binders_to_json       : printing_options -> DsEnv.env -> binders -> json
val aqual_to_string       :                    aqual -> string
val bqual_to_string       : printing_options -> bqual -> string
val args_to_string        : printing_options -> args -> string
val eff_decl_to_string    : printing_options -> bool -> eff_decl -> string
val sub_eff_to_string     : printing_options -> sub_eff -> string
val subst_to_string       : printing_options -> subst_t -> string
val const_to_string       :                    sconst -> string
val qual_to_string        : printing_options -> qualifier -> string
val quals_to_string       : printing_options -> list qualifier -> string
val tscheme_to_string     : printing_options -> tscheme -> string
val cflag_to_string       : printing_options -> cflag -> string
val cflags_to_string      : printing_options -> list cflag -> string
val set_to_string         : printing_options -> ('a -> string) -> set 'a -> string
val list_to_string        : printing_options -> ('a -> string) -> list 'a -> string
val delta_depth_to_string : delta_depth -> string
val action_to_string      : printing_options -> action -> string
val metadata_to_string    : printing_options -> metadata -> string
val ctx_uvar_to_string    : printing_options -> ctx_uvar -> string
val ctx_uvar_to_string_no_reason    : printing_options -> ctx_uvar -> string

val emb_typ_to_string: printing_options -> emb_typ -> string


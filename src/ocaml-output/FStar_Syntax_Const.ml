
open Prims
let mk = (fun t -> (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange))

let p2l = (fun l -> (FStar_Ident.lid_of_path l FStar_Range.dummyRange))

let pconst = (fun s -> (p2l (("Prims")::(s)::[])))

let prims_lid = (p2l (("Prims")::[]))

let fstar_ns_lid = (p2l (("FStar")::[]))

let bool_lid = (pconst "bool")

let unit_lid = (pconst "unit")

let string_lid = (pconst "string")

let bytes_lid = (pconst "bytes")

let char_lid = (pconst "char")

let int_lid = (pconst "int")

let uint8_lid = (pconst "uint8")

let int64_lid = (pconst "int64")

let float_lid = (pconst "float")

let exn_lid = (pconst "exn")

let list_lid = (pconst "list")

let pattern_lid = (pconst "pattern")

let precedes_lid = (pconst "precedes")

let lex_t_lid = (pconst "lex_t")

let lexcons_lid = (pconst "LexCons")

let lextop_lid = (pconst "LexTop")

let smtpat_lid = (pconst "SMTPat")

let smtpatT_lid = (pconst "SMTPatT")

let smtpatOr_lid = (pconst "SMTPatOr")

let int32_lid = (p2l (("FStar")::("Int32")::("int32")::[]))

let int31_lid = (p2l (("FStar")::("Int31")::("int31")::[]))

let heap_lid = (p2l (("FStar")::("Heap")::("heap")::[]))

let kunary = (fun k k' -> (let _111_15 = (let _111_14 = (let _111_13 = (let _111_11 = (FStar_Syntax_Syntax.null_binder k)
in (_111_11)::[])
in (let _111_12 = (FStar_Syntax_Syntax.mk_Total k')
in (_111_13, _111_12)))
in FStar_Syntax_Syntax.Tm_arrow (_111_14))
in (mk _111_15)))

let kbin = (fun k1 k2 k' -> (let _111_28 = (let _111_27 = (let _111_26 = (let _111_24 = (FStar_Syntax_Syntax.null_binder k1)
in (let _111_23 = (let _111_22 = (FStar_Syntax_Syntax.null_binder k2)
in (_111_22)::[])
in (_111_24)::_111_23))
in (let _111_25 = (FStar_Syntax_Syntax.mk_Total k')
in (_111_26, _111_25)))
in FStar_Syntax_Syntax.Tm_arrow (_111_27))
in (mk _111_28)))

let ktern = (fun k1 k2 k3 k' -> (let _111_45 = (let _111_44 = (let _111_43 = (let _111_41 = (FStar_Syntax_Syntax.null_binder k1)
in (let _111_40 = (let _111_39 = (FStar_Syntax_Syntax.null_binder k2)
in (let _111_38 = (let _111_37 = (FStar_Syntax_Syntax.null_binder k3)
in (_111_37)::[])
in (_111_39)::_111_38))
in (_111_41)::_111_40))
in (let _111_42 = (FStar_Syntax_Syntax.mk_Total k')
in (_111_43, _111_42)))
in FStar_Syntax_Syntax.Tm_arrow (_111_44))
in (mk _111_45)))

let true_lid = (pconst "True")

let false_lid = (pconst "False")

let and_lid = (pconst "l_and")

let or_lid = (pconst "l_or")

let not_lid = (pconst "l_not")

let imp_lid = (pconst "l_imp")

let iff_lid = (pconst "l_iff")

let ite_lid = (pconst "ITE")

let exists_lid = (pconst "Exists")

let forall_lid = (pconst "Forall")

let b2t_lid = (pconst "b2t")

let using_IH = (pconst "InductionHyp")

let admit_lid = (pconst "admit")

let magic_lid = (pconst "magic")

let eq2_lid = (pconst "Eq2")

let neq_lid = (pconst "neq")

let neq2_lid = (pconst "neq2")

let exp_true_bool = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))))

let exp_false_bool = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))))

let exp_unit = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))

let cons_lid = (pconst "Cons")

let nil_lid = (pconst "Nil")

let assume_lid = (pconst "_assume")

let assert_lid = (pconst "_assert")

let list_append_lid = (p2l (("FStar")::("List")::("append")::[]))

let strcat_lid = (p2l (("Prims")::("strcat")::[]))

let let_in_typ = (p2l (("Prims")::("Let")::[]))

let op_Eq = (pconst "op_Equality")

let op_notEq = (pconst "op_disEquality")

let op_LT = (pconst "op_LessThan")

let op_LTE = (pconst "op_LessThanOrEqual")

let op_GT = (pconst "op_GreaterThan")

let op_GTE = (pconst "op_GreaterThanOrEqual")

let op_Subtraction = (pconst "op_Subtraction")

let op_Minus = (pconst "op_Minus")

let op_Addition = (pconst "op_Addition")

let op_Multiply = (pconst "op_Multiply")

let op_Division = (pconst "op_Division")

let op_Modulus = (pconst "op_Modulus")

let op_And = (pconst "op_AmpAmp")

let op_Or = (pconst "op_BarBar")

let op_Negation = (pconst "op_Negation")

let array_lid = (p2l (("FStar")::("Array")::("array")::[]))

let array_mk_array_lid = (p2l (("FStar")::("Array")::("mk_array")::[]))

let st_lid = (p2l (("FStar")::("ST")::[]))

let write_lid = (p2l (("FStar")::("ST")::("write")::[]))

let read_lid = (p2l (("FStar")::("ST")::("read")::[]))

let alloc_lid = (p2l (("FStar")::("ST")::("alloc")::[]))

let op_ColonEq = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

let ref_lid = (p2l (("FStar")::("Heap")::("ref")::[]))

let heap_ref = (p2l (("FStar")::("Heap")::("Ref")::[]))

let set_empty = (p2l (("FStar")::("Set")::("empty")::[]))

let set_singleton = (p2l (("FStar")::("Set")::("singleton")::[]))

let set_union = (p2l (("FStar")::("Set")::("union")::[]))

let effect_PURE_lid = (pconst "PURE")

let effect_Pure_lid = (pconst "Pure")

let effect_Tot_lid = (pconst "Tot")

let effect_Lemma_lid = (pconst "Lemma")

let effect_GTot_lid = (pconst "GTot")

let effect_GHOST_lid = (pconst "GHOST")

let effect_Ghost_lid = (pconst "Ghost")

let all_lid = (p2l (("FStar")::("All")::[]))

let effect_ALL_lid = (p2l (("FStar")::("All")::("ALL")::[]))

let effect_ML_lid = (p2l (("FStar")::("All")::("ML")::[]))

let failwith_lid = (p2l (("FStar")::("All")::("failwith")::[]))

let pipe_right_lid = (p2l (("FStar")::("All")::("pipe_right")::[]))

let pipe_left_lid = (p2l (("FStar")::("All")::("pipe_left")::[]))

let try_with_lid = (p2l (("FStar")::("All")::("try_with")::[]))

let as_requires = (pconst "as_requires")

let as_ensures = (pconst "as_ensures")

let decreases_lid = (pconst "decreases")





(* \#line cholera-model.nw 26 *)
open HolKernel boolLib Parse mnUtils Psyntax
open simpLib bossLib boolSimps arithmeticTheory pred_setTheory
infix >-

val hol_ss = bossLib.list_ss

(* \#line cholera-model.nw 4498 *)
local
  (* parent theories *)
  open cholstateTheory overrideTheory chol_opsemTheory
in
end

val _ = new_theory "cholmeaning";

(* \#line cholera-model.nw 4898 *)
val valid_econtext = new_definition(
  "valid_econtext",
  --`valid_econtext f =
      (?f' e1. f = CApBinary f' e1) \/
      (?f' e2. f = \e1. CApBinary f' e1 e2) \/
      (?f' e2 b. f = \e1. Assign f' e1 e2 b) \/
      (?e2 f'. (f = (\e1. f' e1 e2)) /\
               f' IN {COr; CAnd; CommaSep}) \/
      (?e2 e3. (f = \e1. CCond e1 e2 e3)) \/
      (?f'. f = CApUnary f') \/
      (f IN  {Addr; Deref; CAndOr_sqpt; PostInc; RValreq}) \/
      (?fld. f = \e. SVar e fld) \/
      (?args. f = \e. FnApp e args) \/
      (?fn before after.
          (f = \e. FnApp fn (APPEND before (e :: after)))) \/
      (?t. f = Cast t)`--);
(* \#line cholera-model.nw 4921 *)
val rec_expr_P = cholexprTheory.rec_expr_P
val rec_exprl_EVERY = cholexprTheory.rec_exprl_EVERY
val NOT_IN_EMPTY = pred_setTheory.NOT_IN_EMPTY
val IN_INSERT = pred_setTheory.IN_INSERT
val valid_econtext_rec_expr = store_thm(
  "valid_econtext_rec_expr",
  (--`!P f e.
         valid_econtext f /\ rec_expr_P (f e) P ==> rec_expr_P e P`--),
  REWRITE_TAC [valid_econtext, IN_INSERT, NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ELIM_TAC THEN
  FULL_SIMP_TAC hol_ss [rec_expr_P, rec_exprl_EVERY,
                        listTheory.EVERY_APPEND]);
val valid_econtexts_11 = store_thm(
  "valid_econtexts_11",
  ``!f. valid_econtext f ==> !e1 e2. (f e1 = f e2) = (e1 = e2)``,
  GEN_TAC THEN SIMP_TAC hol_ss [valid_econtext, NOT_IN_EMPTY,
    IN_INSERT] THEN REPEAT STRIP_TAC THEN ELIM_TAC THEN
  SIMP_TAC hol_ss [listTheory.APPEND_11, cholexprTheory.CExpr_11]);
(* \#line cholera-model.nw 4969 *)
val lval2rval = new_definition(
  "lval2rval",
  ``lval2rval (s0,e0,se0) (s,e,se) =
       (s0 = s) /\
       ?n t. (e0 = LVal n t) /\
             (~(array_type t) /\
              (?sz. sizeof s0.strmap (INL t) sz /\
                    (mark_ref n sz se0 se /\
                     (range_set n sz) SUBSET s0.initmap /\
                     (e = ECompVal (mem2val s0 n sz) t) \/
                     (~(range_set n sz SUBSET s0.initmap) \/
                      (!se'. ~(mark_ref n sz se0 se'))) /\
                     (se = se0) /\ (e = UndefinedExpr))) \/
              (?sz t'.
                  (t = Array t' sz) /\ (se0 = se) /\
                  (e = ECompVal (num2mval ptr_size n) (Ptr t'))))``);
(* \#line cholera-model.nw 4993 *)
val lval2rval_states_equal = store_thm(
  "lval2rval_states_equal",
  --`!s0 ese0 s ese. lval2rval (s0,ese0) (s,ese) ==> (s0 = s)`--,
  REPEAT GEN_TAC THEN CONV_TAC (ant_CONV (
    (arg_CONV 1 (snd_CONV pair_CONV)) THENC
    (arg_CONV 2 (snd_CONV pair_CONV)))) THEN
  REWRITE_TAC [lval2rval] THEN STRIP_TAC);
val update_map_over_lval2rval = store_thm(
  "update_map_over_lval2rval",
  --`!s0 e0 se0 s e se. lval2rval (s0,e0,se0) (s,e,se) ==>
                        (update_map se0 = update_map se)`--,
  SIMP_TAC (hol_ss ++ impnorm_set) [lval2rval] THEN
  PROVE_TAC [se_infoTheory.update_map_over_mark_ref]);
(* \#line cholera-model.nw 5011 *)
open cholexprTheory
val lval_one_one = prove(
  ``!n1 t1 n2 t2. (LVal n1 t1 = LVal n2 t2) ==>
                  (n1 = n2) /\ (t1 = t2)``,
  SIMP_TAC hol_ss [cholexprTheory.CExpr_11])
val lval2rval_det = store_thm(
  "lval2rval_det",
  ``!se0 s0 e0 se s e.
       lval2rval (s0, e0, se0) (s, e, se) ==>
       !se' s' e'.
          lval2rval (s0, e0, se0) (s', e', se') ==>
          (s' = s) /\ (e' = e) /\ (se' = se)``,
  SIMP_TAC hol_ss [lval2rval] THEN REPEAT STRIP_TAC THEN
  ELIM_TAC THEN SIMP_TAC hol_ss [CExpr_11,
    CExpr_distinct, choltypeTheory.CType_11] THEN
  IMP_RES_TAC lval_one_one THEN ELIM_TAC THEN
  IMP_RES_TAC (cholmemTheory.sizeof_det) THEN ELIM_TAC THEN
  dMESON_TAC 6 [choltypeTheory.type_classes,
                se_infoTheory.mark_ref_det,
                choltypeTheory.CType_11]);
val lval2rval_is_lval = store_thm(
  "lval2rval_is_lval",
  ``!s0 e0 se0 X.
      lval2rval (s0, e0, se0) X ==> ?n t. e0 = LVal n t``,
  SIMP_TAC hol_ss [lval2rval, pairTheory.FORALL_PROD] THEN
  REPEAT STRIP_TAC THEN ELIM_TAC THEN MESON_TAC []);
val lval2rval_ecompval = store_thm(
  "lval2rval_ecompval",
  ``!s0 v t se0 X. ~(lval2rval (s0, ECompVal v t, se0) X)``,
  SIMP_TAC hol_ss [pairTheory.FORALL_PROD, CExpr_distinct,
                  lval2rval]);
val lval2rval_results = store_thm(
  "lval2rval_results",
  ``!X s e se. lval2rval X (s,e,se) ==>
               (?v t. e = ECompVal v t) \/ (e = UndefinedExpr)``,
  SIMP_TAC hol_ss [pairTheory.FORALL_PROD, lval2rval] THEN
  REPEAT STRIP_TAC THEN ELIM_TAC THEN SIMP_TAC hol_ss [CExpr_11]);
(* \#line cholera-model.nw 5065 *)
val valid_lvcontext = new_definition (
  "valid_lvcontext",
  --`valid_lvcontext f =
        (?f' e1. f = CApBinary f' e1) \/
        (?f' e2. f = \e1. CApBinary f' e1 e2) \/
        (?e2 f'. (f = (\e1. f' e1 e2)) /\
                 f' IN {COr; CAnd; CommaSep}) \/
        (?e2 e3. (f = \e1. CCond e1 e2 e3)) \/
        (?f'. f = CApUnary f') \/
        (f IN  {Deref; CAndOr_sqpt; RValreq}) \/
        (?args. f = \e. FnApp e args) \/
        (?fn before after.
              (f = \e. FnApp fn (APPEND before (e :: after)))) \/
        (?t. f = Cast t)`--);
(* \#line cholera-model.nw 5085 *)
val mysimp =
  SIMP_TAC hol_ss [CExpr_11, CExpr_distinct]
val lvcontexts_are_econtexts = store_thm(
  "lvcontexts_are_econtexts",
  --`!f. valid_lvcontext f ==> valid_econtext f`--,
  SIMP_TAC hol_ss [
    valid_lvcontext, valid_econtext, NOT_IN_EMPTY, IN_INSERT] THEN
  REPEAT STRIP_TAC THEN ELIM_TAC THEN
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN mysimp THEN
  MESON_TAC []);
(* \#line cholera-model.nw 5763 *)
val malloc = new_definition(
  "malloc",
  ``malloc s0 a n =
       DISJOINT s0.allocmap (range_set a n) /\
       ~(a = 0) /\
       a + n < 2 EXP (CHAR_BIT * ptr_size)``);
(* \#line cholera-model.nw 5731 *)
val rec_i_vars = new_recursive_definition {
  name = "rec_i_vars",
  rec_axiom = listTheory.list_Axiom,
  def =
   ``(rec_i_vars st1 [] st2 resv = (st1 = st2) /\ (resv = T)) /\
     (rec_i_vars st1 (CONS (hd:string#CType) tail) st2 resv =
        ?n.
           sizeof st1.strmap (INL (SND hd)) n /\
           (((?a. malloc st1 a n) /\
            let a = (@a. malloc st1 a n) in
                 rec_i_vars
                   (st1 with
                    <| varmap updated_by (\v. override v (FST hd) a) ;
                       typemap updated_by (\t. override t (FST hd) (SND hd));
                       allocmap updated_by ((UNION) (range_set a n)) |>)
                   tail
                   st2 resv) \/
           (!a. ~malloc st1 a n) /\ (resv = F) /\ (st2 = st1)))``
};
val install_vars = new_definition(
  "install_vars",
  ``install_vars st1 fn st2 resv =
        rec_i_vars (st1 with <| varmap := st1.gvarmap ;
                                typemap := st1.gtypemap ;
                                strmap := st1.gstrmap |>)
                   ((st1.fnmap fn).parameters)
                   st2 resv``);
(* \#line cholera-model.nw 5778 *)
val rec_i_vals = new_recursive_definition {
  name = "rec_i_vals",
  rec_axiom = listTheory.list_Axiom,
  def = (--`
    (rec_i_vals st1 [] vallist st2 res =
       (vallist = []) /\ (st1 = st2) /\ res) /\
    (rec_i_vals s0 (CONS (phd:string#CType) ptl) vallist s res =
       ?vval vtype vtl pname ptype.
          (vallist = CONS (ECompVal vval vtype) vtl) /\
          (phd = (pname, ptype)) /\
          ((?s1 newval rs.
             convert_val s0.strmap (vval, vtype) (newval, ptype) /\
             (rs = range_set (s0.varmap pname) (LENGTH newval)) /\
             (s1 = val2mem s0 (s0.varmap pname) newval
                   with <| initmap updated_by ((UNION) rs) ;
                           allocmap updated_by ((UNION) rs) |>) /\
             rec_i_vals s1 ptl vtl s res) \/
           (!nv. ~convert_val s0.strmap (vval,vtype) (nv, ptype)) /\
           (res = F)))`--)};

val install_values = new_definition (
  "install_values",
  ``install_values s0 fn pvl s1 res =
          rec_i_vals s0 (s0.fnmap fn).parameters pvl s1 res``);
(* \#line cholera-model.nw 5695 *)
val pass_parameters = new_definition (
  "pass_parameters",
  ``pass_parameters s0 fnid pv s res =
      ?s1 res'.
        install_vars s0 fnid s1 res' /\
        (res'
         => install_values s1 fnid pv s res
         |  (res = F) /\ (s = s0))``);
(* \#line cholera-model.nw 3199 *)
val se = (==`:num # (MemObj list)`==) (* these two are here for *)
val qse = ty_antiq se;                (* the benefit of cholmeaning *)
val se_info = (==`:se_info`==)
val qse_info = ty_antiq se_info
val paired_se = (==`:se_info # se_info`==)
val qpaired_se = ty_antiq paired_se
val sse = (==`:se_info#CState`==)
val qsse = ty_antiq sse
(* \#line cholera-model.nw 4570 *)
open Datatype
val _ = Hol_datatype `
  meaningfuls =  mExpr of CExpr => se_info |
                 mTCExpr of CExpr => se_info |
                 mStmt of CStmt | mStmtl of CStmt list |
                 mVarD of var_decl | mVarDl of var_decl list`;
val meaningfuls = TypeBase.axiom_of ``:meaningfuls``
(* \#line cholera-model.nw 4589 *)
val is_mExprish = Define`
    (is_mExprish (mExpr e se) = T) /\
    (is_mExprish (mTCExpr e se) = T) /\
    (is_mExprish (mStmt s) = F) /\ (is_mExprish (mStmtl sl) = F) /\
    (is_mExprish (mVarD v) = F) /\ (is_mExprish (mVarDl vl) = F)`;
val _ = Define`
    (is_mStmtish (mExpr e ses) = F) /\
    (is_mStmtish (mTCExpr e se) = F) /\
    (is_mStmtish (mStmt s) = T) /\ (is_mStmtish (mStmtl sl) = T) /\
    (is_mStmtish (mVarD v) = F) /\ (is_mStmtish (mVarDl vl) = F)`;
val _ = Define`
        (is_mVarDish (mExpr e ses) = F) /\
        (is_mVarDish (mTCExpr e se) = F) /\
        (is_mVarDish (mStmt s) = F) /\ (is_mVarDish (mStmtl sl) = F) /\
        (is_mVarDish (mVarD v) = T) /\ (is_mVarDish (mVarDl vl) = T)`;
val is_mlistish = Define`
    (is_mlistish (mExpr e ses) = F) /\
    (is_mlistish (mTCExpr e se) = F) /\
    (is_mlistish (mStmt s) = F) /\ (is_mlistish (mStmtl sl) = T) /\
    (is_mlistish (mVarD v) = F) /\ (is_mlistish (mVarDl vl) = T)`;
val is_mExpr = new_definition(
  "is_mExpr",
  --`is_mExpr m = is_mExprish m /\ ~is_mlistish m`--);
val is_mStmt = new_definition(
  "is_mStmt",
  --`is_mStmt m = is_mStmtish m /\ ~is_mlistish m`--);
(* \#line cholera-model.nw 4621 *)
val out_mExpr = new_recursive_definition {
  name = "out_mExpr", rec_axiom = meaningfuls,
  def = (--`(out_mExpr (mExpr e se) = (e, se)) /\
            (out_mExpr (mTCExpr e se) = (e, se))`--)
};
val out_mStmt = new_recursive_definition {
  name = "out_mStmt", rec_axiom = meaningfuls,
  def = (--`out_mStmt (mStmt s) = s`--)
};
val out_mStmtl = new_recursive_definition {
  name = "out_mStmtl", rec_axiom = meaningfuls,
  def = (--`out_mStmtl (mStmtl s) = s`--)
};
(* \#line cholera-model.nw 4659 *)
val _ = Hol_datatype
              `meaning_val = ExprVal of CExpr => se_info |
                             FunArgsVal of CExpr list => se_info |
                             StmtVal | RetVal of MemObj list |
                             BreakVal | ContVal | VarDeclVal |
                             Undefined`;
val meaning_val = TypeBase.axiom_of ``:meaning_val``
val is_retval = new_definition(
  "is_retval",
  (--`is_retval v = (?v'. v = RetVal v')`--));
val is_interruptval = new_definition (
  "is_interruptval",
  (--`is_interruptval v = (v = ContVal) \/ (v = BreakVal) \/
                          (?mv. v = RetVal mv)`--));
(* \#line cholera-model.nw 4680 *)
val traplink = new_definition(
  "traplink",
  --`traplink tt v = (tt = ContTrap) /\ (v = ContVal) \/
                     (tt = BreakTrap) /\ (v = BreakVal)`--);
(* \#line cholera-model.nw 4521 *)
val memval = ty_antiq (==`:MemObj list`==);
val _ = print "About to define meaning relation\n";
local
  val mng  =
    (--`meaning:meaningfuls -> CState ->
                (CState # meaning_val) -> bool`--)
  val ev = (--`ExprVal`--)
  val evl = (--`FunArgsVal`--)
in
  val (meaning_rules, meaning_ind, meaning_cases) = IndDefLib.Hol_reln`
      
(* \#line cholera-model.nw 4772 *)
(!n se s.
   ^mng (mExpr (Cnum n) se) s
        (s, ^ev (ECompVal (num2mval int_size n) (Signed Int)) se)) /\
(* \#line cholera-model.nw 4791 *)
(!n se s.
    ^mng (mExpr (Cchar n) se) s
         (s, ^ev (ECompVal (num2mval int_size n) (Signed Int)) se)) /\
(!t se s.
    ^mng (mExpr (Cnullptr t) se) s
         (s, ^ev (ECompVal (num2mval ptr_size 0) (Ptr t)) se)) /\
(!n se s.
    ^mng (mExpr (CFunRef n) se) s
         (s, ^ev (ECompVal (create_memval_fnref n) (s.typemap n)) se)) /\
(* \#line cholera-model.nw 4826 *)
(!vname se s.
    ^mng (mExpr (Var vname) se) s
         (s, ^ev (LVal (s.varmap vname) (s.typemap vname)) se))
(* \#line cholera-model.nw 4800 *)
                                            /\
(* \#line cholera-model.nw 4849 *)
(!s v t v' t' se.
    convert_val s.strmap (v, t) (v', t') ==>
    ^mng (mExpr (Cast t' (ECompVal v t)) se) s
         (s, ^ev (ECompVal v' t') se)) /\
(* \#line cholera-model.nw 4859 *)
(!v t t' se s.
    (!v'. ~convert_val s.strmap (v, t) (v', t')) ==>
    ^mng (mExpr (Cast t' (ECompVal v t)) se) s (s, ^ev UndefinedExpr se))
(* \#line cholera-model.nw 4801 *)
                           /\
(* \#line cholera-model.nw 4884 *)
(!f e se0 s0 e' se s.
    ^mng (mExpr e se0) s0 (s, ^ev e' se) /\
    valid_econtext f ==>
    ^mng (mExpr ((f:CExpr->CExpr) e) se0) s0 (s, ^ev (f e') se)) /\
(* \#line cholera-model.nw 4947 *)
(!f se s.
    valid_econtext f \/ (?asfn lhs b. f = \e. Assign asfn lhs e b) ==>
    ^mng (mExpr (f UndefinedExpr) se) s (s, ^ev UndefinedExpr se)) /\
(* \#line cholera-model.nw 5054 *)
(!f e0 se0 s0 s e se.
   valid_lvcontext f /\ lval2rval (s0,e0,se0) (s,e,se) ==>
   ^mng (mExpr ((f:CExpr->CExpr) e0) se0) s0 (s, ^ev (f e) se)) /\
(* \#line cholera-model.nw 5112 *)
(!e se0 s0 s se.
    apply_se (se0, s0) (se, s) ==>
    ^mng (mExpr e se0) s0 (s, ^ev e se)) /\
(* \#line cholera-model.nw 5124 *)
(!e se0 s0.
    (!se s. ~(apply_se (se0, s0) (se, s))) /\
    ~is_null_se se0 /\ ~(e = UndefinedExpr) ==>
    ^mng (mExpr e se0) s0 (s0, ^ev UndefinedExpr se0)) /\
(* \#line cholera-model.nw 5141 *)
(!v t e2 se s0.
    is_null_se se ==>
    ^mng (mExpr (CommaSep (ECompVal v t) e2) se) s0
         (s0, ^ev (RValreq e2) base_se)) /\
(* \#line cholera-model.nw 5151 *)
(!v t se s. ^mng (mExpr (RValreq (ECompVal v t)) se) s
                 (s, ^ev (ECompVal v t) se)) /\
(* \#line cholera-model.nw 5211 *)
(!f v1 type1 v2 type2 se0 s.
   (!res restype. ~binop_meaning s f v1 type1 v2 type2 res restype) ==>
   ^mng (mExpr (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se0) s
        (s, ^ev UndefinedExpr se0)) /\
(!s f v1 type1 v2 type2 res restype se.
    binop_meaning s f v1 type1 v2 type2 res restype ==>
    ^mng (mExpr (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se) s
         (s, ^ev (ECompVal res restype) se)) /\
(* \#line cholera-model.nw 5181 *)
(!s f ival t result rt se.
   unop_meaning s f ival t result rt ==>
   ^mng (mExpr (CApUnary f (ECompVal ival t)) se) s
        (s, ^ev (ECompVal result rt) se)) /\
(!s0 se0 f ival t.
     (!res rt. ~(unop_meaning s0 f ival t res rt)) ==>
     ^mng (mExpr (CApUnary f (ECompVal ival t)) se0) s0
          (s0, ^ev UndefinedExpr se0)) /\
(* \#line cholera-model.nw 5263 *)
(!v t se s sub2.
    (coerce_to_num v = 0) /\ scalar_type t ==>
    ^mng (mExpr (CAnd (ECompVal v t) sub2) se) s
         (s, ^ev (ECompVal (num2mval int_size 0) (Signed Int)) se)) /\
(!v t se s sub2.
    ~(coerce_to_num v = 0) /\ is_null_se se /\ scalar_type t ==>
    ^mng (mExpr (CAnd (ECompVal v t) sub2) se) s
         (s, ^ev (CAndOr_sqpt sub2) base_se)) /\
(!v t se s.
   scalar_type t ==>
   ^mng (mExpr (CAndOr_sqpt (ECompVal v t)) se) s
        (s, ^ev (ECompVal (if coerce_to_num v = 0 then num2mval int_size 0
                           else num2mval int_size 1) (Signed Int))
                se)) /\
(* \#line cholera-model.nw 5296 *)
(!v t sub2 se s.
   ~(coerce_to_num v = 0) /\ scalar_type t ==>
   ^mng (mExpr (COr (ECompVal v t) sub2) se) s
        (s, ^ev (ECompVal (num2mval int_size 1) (Signed Int)) se)) /\
(!v t sub2 se s.
    (coerce_to_num v = 0) /\ is_null_se se /\ scalar_type t ==>
    ^mng (mExpr (COr (ECompVal v t) sub2) se) s
         (s, ^ev (CAndOr_sqpt sub2) base_se)) /\
(* \#line cholera-model.nw 5334 *)
(!v t e2 t2 e3 t3 resexpr result_type se s sn.
    
(* \#line cholera-model.nw 5325 *)
is_null_se se /\ scalar_type t /\
expr_type (expr_type_comps s) RValue (INL e2) (INL t2) /\
expr_type (expr_type_comps s) RValue (INL e3) (INL t3) /\
expr_type (expr_type_comps s) RValue
          (INL (CCond (ECompVal v t) e2 e3))
          (INL result_type)
(* \#line cholera-model.nw 5335 *)
                                         /\
    (coerce_to_num v = 0) /\
    ((t2 = Struct sn) /\ (resexpr = RValreq e3) \/
     (!sn. ~(t2 = Struct sn)) /\ (resexpr = Cast result_type e3)) ==>
    ^mng (mExpr (CCond (ECompVal v t) e2 e3) se) s (s, ^ev resexpr base_se))

           /\

(!v t e2 t2 e3 t3 resexpr result_type se s sn.
   
(* \#line cholera-model.nw 5325 *)
is_null_se se /\ scalar_type t /\
expr_type (expr_type_comps s) RValue (INL e2) (INL t2) /\
expr_type (expr_type_comps s) RValue (INL e3) (INL t3) /\
expr_type (expr_type_comps s) RValue
          (INL (CCond (ECompVal v t) e2 e3))
          (INL result_type)
(* \#line cholera-model.nw 5344 *)
                                        /\
   ~(coerce_to_num v = 0) /\
   ((t2 = Struct sn) /\ (resexpr = RValreq e2) \/
     (!sn. ~(t2 = Struct sn)) /\ (resexpr = Cast result_type e2)) ==>
   ^mng (mExpr (CCond (ECompVal v t) e2 e3) se) s (s, ^ev resexpr base_se))

          /\
(* \#line cholera-model.nw 5378 *)
(!mval t se s.
    ~(t = Void) ==>
    ^mng (mExpr (Deref (ECompVal mval (Ptr t))) se) s
         (s, ^ev (LVal (memval2addr mval) t) se)) /\
(* \#line cholera-model.nw 5397 *)
(!a t se s. ^mng (mExpr (Addr (LVal a t)) se) s
                 (s, ^ev (ECompVal (num2mval ptr_size a) (Ptr t)) se)) /\
(* \#line cholera-model.nw 5424 *)
(!se0 s0 s e se mb mb' f a RHS.
    ^mng (mExpr RHS se0) s0 (s, ^ev e se) /\
    (mb' = BAG_delta (ref_map se0, ref_map se) mb) ==>
    ^mng (mExpr (Assign f a RHS mb) se0) s0
         (s, ^ev (Assign f a e mb') se)) /\
(* \#line cholera-model.nw 5452 *)
(!f n t e mb se0 s0.
     ^mng (mExpr (Assign (SOME f) (LVal n t) e mb) se0) s0
          (s0, ExprVal (Assign NONE (LVal n t)
                         (CApBinary f (LVal n t) e)
                         mb)
                       se0)) /\
(* \#line cholera-model.nw 5513 *)
(!s v0 t0 v lhs_t ok_refs se0 se' se a resv mb.
     convert_val s.strmap (v0,t0) (v,lhs_t) /\
     (ok_refs = \x. x IN (se_affects (a, v)) => mb x | 0) /\
     (se' = ref_map_fupd (\rm. BAG_DIFF rm ok_refs) se0) /\
     (se = add_se (a, v) se') /\ (resv = ECompVal v lhs_t)
                          \/
     (!v. ~convert_val s.strmap (v0, t0) (v, lhs_t)) /\
     (resv = UndefinedExpr) /\ (se = se0) ==>
     ^mng (mExpr (Assign NONE (LVal a lhs_t) (ECompVal v0 t0) mb) se0)
          s (s, ^ev resv se)) /\
(* \#line cholera-model.nw 5543 *)
(!se0 se s t t' sz v nv nv1 a resv.
   sizeof s.strmap (INL t) sz /\ (v = mem2val s a sz) /\
   range_set a sz SUBSET s.initmap /\
   binop_meaning s CPlus v t (num2mval int_size 1) (Signed Int) nv1 t' /\
   convert_val s.strmap (nv1,t') (nv,t) /\
   (se = add_se (a, nv) se0) /\ (resv = ECompVal v t)
              \/
   (!nv. ~convert_val s.strmap (nv1, t') (nv, t)) /\
   (se = se0) /\ (resv = UndefinedExpr) ==>
   ^mng (mExpr (PostInc (LVal a t)) se0) s (s, ^ev resv se)) /\
(* \#line cholera-model.nw 5561 *)
(!a t se0 sz s v.
   sizeof s.strmap (INL t) sz /\
   (v = mem2val s a sz) /\
   ((!nv1 t'.
       ~binop_meaning s CPlus v t (num2mval int_size 1) (Signed Int) nv1 t') \/
   ~(range_set a sz SUBSET s.initmap)) ==>
   ^mng (mExpr (PostInc (LVal a t)) se0) s (s, ^ev UndefinedExpr se0)) /\
(* \#line cholera-model.nw 5590 *)
(!s st fld ftype se offn a.
     offset s.strmap st fld offn /\
     lookup_field_info (s.strmap st) fld ftype ==>
     ^mng (mExpr (SVar (LVal a (Struct st)) fld) se) s
          (s, ^ev (LVal (a + offn) ftype) se)) /\

(!s st fld ftype fsz v fv se offn.
   offset s.strmap st fld offn /\
   lookup_field_info (s.strmap st) fld ftype /\
   sizeof s.strmap (INL ftype) fsz /\
   (fv:^memval = GENLIST (\n. EL (n + offn) v) fsz) ==>
   ^mng (mExpr (SVar (ECompVal v (Struct st)) fld) se) s
        (s, ^ev (ECompVal fv ftype) se)) /\
(* \#line cholera-model.nw 5633 *)
(!f params se s.
    EVERY (\e. ?v t. e = ECompVal v t) (CONS f params) /\
    is_null_se se ==>
    ^mng (mExpr (FnApp f params) se) s
         (s, ^ev (FnApp_sqpt f params) base_se)) /\
(* \#line cholera-model.nw 5647 *)
(!fnval ftype params se s0 s1 s2 s fnid rt vs rv ev.
    ^mng (mStmt (s1.fnmap fnid).body) s1 (s2, rv) /\
    pass_parameters s0 fnid params s1 T /\
    memval_fnref fnval fnid /\
    (ftype = Function rt vs) /\
    ((?v. (rv = RetVal v) /\ (ev = ECompVal v rt) /\
          (s = s0 with <| locmap := s2.locmap ;
                          initmap := s2.initmap INTER s0.allocmap |>))
                    \/
     (rv = Undefined) /\ (ev = UndefinedExpr) /\ (s = s0)) ==>
    ^mng (mExpr (FnApp_sqpt (ECompVal fnval ftype) params) se) s0
         (s, ^ev ev se)) /\
(* \#line cholera-model.nw 5667 *)
(!fnval ftype params se s0 s fnid.
   pass_parameters s0 fnid params s F /\
   memval_fnref fnval fnid ==>
   ^mng (mExpr (FnApp_sqpt (ECompVal fnval ftype) params) se) s0
        (s0, ^ev UndefinedExpr se)) /\
(* \#line cholera-model.nw 5814 *)
(!e se s. ^mng (mTCExpr e se) s (s, ^ev e se))
     /\
(!e0 se0 s0 s' e' se' s e se.
   ^mng (mExpr e0 se0) s0 (s', ^ev e' se') /\
   ^mng (mTCExpr e' se') s' (s, ^ev e se) ==>
   ^mng (mTCExpr e0 se0) s0 (s, ^ev e se))
(* \#line cholera-model.nw 4531 *)
                                /\
      
(* \#line cholera-model.nw 5891 *)
(!s. ^mng (mStmt EmptyStmt) s (s, StmtVal)) /\

(* \#line cholera-model.nw 5916 *)
(!s0. ^mng (mStmtl []) s0 (s0, StmtVal)) /\

(!st1 sttail s1 s' s2 v.
   ^mng (mStmt st1) s1 (s', StmtVal) /\
   ^mng (mStmtl sttail) s' (s2, v) ==>
   ^mng (mStmtl (st1 :: sttail)) s1 (s2,v)) /\

(!st1 s1 s' v sttail.
   ^mng (mStmt st1) s1 (s', v) /\ ~(v = StmtVal) ==>
   ^mng (mStmtl (st1 :: sttail)) s1 (s', v)) /\

(!e s1 s2 e' se v t retval.
   ^mng (mTCExpr (RValreq e) base_se) s1 (s2, ^ev e' se) /\
   is_null_se se /\
   ((e' = ECompVal v t) /\ (retval = RetVal v) \/
    (e' = UndefinedExpr) /\ (retval = Undefined)) ==>
   ^mng (mStmt (Ret e)) s1 (s2, retval)) /\

(!s1. ^mng (mStmt EmptyRet) s1 (s1, RetVal [])) /\
(!s1. ^mng (mStmt Break) s1 (s1, BreakVal)) /\
(!s1. ^mng (mStmt Cont) s1 (s1, ContVal)) /\
(* \#line cholera-model.nw 5957 *)
(!st s s0 v tt.
     ^mng (mStmt st) s0 (s, v) /\ traplink tt v ==>
     ^mng (mStmt (Trap tt st)) s0 (s, StmtVal)) /\

(!st s s0 v tt.
     ^mng (mStmt st) s0 (s, v) /\ ~(traplink tt v) ==>
     ^mng (mStmt (Trap tt st)) s0 (s, v))
(* \#line cholera-model.nw 5893 *)
                                        /\

(!exp s1 s2 se val retval v t.
     ^mng (mTCExpr (RValreq exp) base_se) s1 (s2, ^ev val se) /\
     ((val = ECompVal v t) /\ (retval = StmtVal) /\ is_null_se se \/
      (val = UndefinedExpr) /\ (retval = Undefined)) ==>
     ^mng (mStmt (Standalone exp)) s1 (s2, retval))
(* \#line cholera-model.nw 5880 *)
                                    /\
(* \#line cholera-model.nw 5996 *)
(!guard t e s0 s se.
    ^mng (mTCExpr (RValreq guard) base_se) s0 (s, ^ev UndefinedExpr se) ==>
    ^mng (mStmt (CIf guard t e)) s0 (s, Undefined)) /\

(!guard s1 s' gval t se thenstmt elsestmt s2 val.
    ^mng (mTCExpr (RValreq guard) base_se) s1 (s', ^ev (ECompVal gval t) se) /\
    ^mng (mStmt thenstmt) s' (s2, val) /\
    ~(coerce_to_num gval = 0) /\  (* guard is true *)
    scalar_type t /\ is_null_se se ==>
    ^mng (mStmt (CIf guard thenstmt elsestmt)) s1 (s2, val)) /\

(!guard s1 s' gval t se thenstmt elsestmt s2 val.
    ^mng (mTCExpr (RValreq guard) base_se) s1
         (s', ^ev (ECompVal gval t) se) /\
    ^mng (mStmt elsestmt) s' (s2, val) /\
    (coerce_to_num gval = 0) (* guard is false *) /\
    scalar_type t /\ is_null_se se ==>
    ^mng (mStmt (CIf guard thenstmt elsestmt)) s1 (s2, val))
(* \#line cholera-model.nw 5881 *)
                               /\
(* \#line cholera-model.nw 6043 *)
(!guard s0 s se bdy.
    ^mng (mTCExpr (RValreq guard) base_se) s0
         (s, ^ev UndefinedExpr se) ==>
    ^mng (mStmt (CLoop guard bdy)) s0 (s, Undefined)) /\

(!guard bdy s0 s gval t se.
     ^mng (mTCExpr (RValreq guard) base_se) s0
          (s, ^ev (ECompVal gval t) se) /\
     scalar_type t /\ (coerce_to_num gval = 0) /\ is_null_se se ==>
     ^mng (mStmt (CLoop guard bdy)) s0 (s, StmtVal)) /\
(* \#line cholera-model.nw 6063 *)
(!guard bdy s0 s' s gval t se v.
   ^mng (mTCExpr (RValreq guard) base_se) s0
        (s', ^ev (ECompVal gval t) se) /\
   ^mng (mStmt bdy) s' (s, v) /\
   ~(v = StmtVal) /\ scalar_type t /\
   ~(coerce_to_num gval = 0) /\ is_null_se se ==>
   ^mng (mStmt (CLoop guard bdy)) s0 (s, v)) /\
(* \#line cholera-model.nw 6077 *)
(!guard bdy gval t s0 s' s'' s v se.
   ^mng (mTCExpr (RValreq guard) base_se) s0 (s', ^ev (ECompVal gval t) se) /\
   ^mng (mStmt bdy) s' (s'', StmtVal) /\
   ^mng (mStmt (CLoop guard bdy)) s'' (s, v) /\
   scalar_type t /\ ~(coerce_to_num gval = 0) /\
   is_null_se se ==>
   ^mng (mStmt (CLoop guard bdy)) s0 (s, v))
(* \#line cholera-model.nw 5882 *)
                                  /\
(* \#line cholera-model.nw 6103 *)
(!s0 s1 vds sts s2 v.
     ^mng (mVarDl vds) s0 (s1, VarDeclVal) /\
     ^mng (mStmtl sts) s1 (s2, v) ==>
     ^mng (mStmt (Block vds sts))
          s0
          (s0 with <| locmap := s2.locmap ;
                      initmap := s2.initmap INTER s0.allocmap |>,
           v)) /\
(* \#line cholera-model.nw 6121 *)
(!vds sts s0 s. ^mng (mVarDl vds) s0 (s, Undefined) ==>
                ^mng (mStmt (Block vds sts)) s0 (s0, Undefined))
(* \#line cholera-model.nw 5883 *)
                        /\
(* \#line cholera-model.nw 6150 *)
(!s type n name a.
   sizeof s.strmap (INL type) n /\
   (?a. malloc s a n) /\
   (a = (@a. malloc s a n)) ==>
   ^mng (mVarD (VDec type name)) s
        (s with <| allocmap updated_by (UNION) (range_set a n);
                   varmap   updated_by (\v. override v name a);
                   typemap  updated_by (\t. override t name type) |>,
         VarDeclVal)) /\

(!s type name.
    (!a. ~malloc s a (sizeof_fn s.strmap type)) ==>
    ^mng (mVarD (VDec type name)) s (s, Undefined))
(* \#line cholera-model.nw 6138 *)
                                            /\
(* \#line cholera-model.nw 6181 *)
(!t name e s0 s se s1 v.
   ^mng (mVarD (VDec t name)) s0 (s1, VarDeclVal) /\
   ^mng (mTCExpr
          (Assign NONE (Var name) (RValreq e) EMPTY_BAG) base_se)
        s1 (s, ^ev (ECompVal v t) se) /\
   is_null_se se ==>
   ^mng (mVarD (VDecInit t name e)) s0 (s, VarDeclVal)) /\
(* \#line cholera-model.nw 6194 *)
(!t n e s0 s s1 se.
    ^mng (mVarD (VDec t n)) s0 (s1, VarDeclVal) /\
    ^mng (mTCExpr
            (Assign NONE (Var n) (RValreq e) EMPTY_BAG) base_se)
         s1 (s, ^ev UndefinedExpr se) ==>
    ^mng (mVarD (VDecInit t n e)) s0 (s, Undefined)) /\
(* \#line cholera-model.nw 6206 *)
(!t n e s0 s.
    ^mng (mVarD (VDec t n)) s0 (s, Undefined) ==>
    ^mng (mVarD (VDecInit t n e)) s0 (s, Undefined))
(* \#line cholera-model.nw 6139 *)
                                                  /\
(* \#line cholera-model.nw 6223 *)
(!name flds s newstrmap.
    (newstrmap = override s.strmap name (str_info flds)) ==>
    ^mng (mVarD (VStrDec name flds)) s
         (s with strmap := newstrmap, VarDeclVal))
(* \#line cholera-model.nw 6140 *)
                                       /\
(* \#line cholera-model.nw 6245 *)
(!s. ^mng (mVarDl []) s (s, VarDeclVal)) /\

(!vhd vtl s0 s.
   ^mng (mVarD vhd) s0 (s, Undefined) ==>
   ^mng (mVarDl (vhd :: vtl)) s0 (s, Undefined)) /\

(!vhd vtl s0 s1 s2 v.
    ^mng (mVarD vhd) s0 (s1, VarDeclVal) /\
    ^mng (mVarDl vtl) s1 (s2, v) ==>
    ^mng (mVarDl (vhd :: vtl)) s0 (s2, v))
(* \#line cholera-model.nw 4533 *)
  `
  val meaning = CONJ meaning_rules meaning_ind
end;
(* \#line cholera-model.nw 4544 *)
val umeaning = new_definition(
  "umeaning",
  (--`umeaning p s0 s v =
         meaning (mStmt p) s0 (s, v) /\
         !s' v'. meaning (mStmt p) s0 (s', v') ==>
                 ~(v' = Undefined)`--));

(* \#line cholera-model.nw 6309 *)
local
  open BasicProvers
  val mng_induction = CONJUNCT2 meaning
  val ss = srw_ss()
  val chol_RULE = SIMP_RULE ss []
  val transform =
      SPEC (--`\x (s:CState) (sv:CState # meaning_val).
                 is_mExprish x ==> P (out_mExpr x) s sv`--) >-
      (fn th => let val ants = strip_conj (hd (hyp (UNDISCH_ALL th)))
                    val rwts = map (SIMP_CONV ss []) ants
                in
                    REWRITE_RULE rwts th
                end) >- UNDISCH_ALL
  val base_thm = transform mng_induction
  fun t2 spec_t = SPEC spec_t >- chol_RULE >- GEN_ALL >- DISCH_ALL
in
  val meaning_expr_induction = save_thm(
    "meaning_expr_induction",
    t2 (--`mExpr e se0`--) base_thm)
end;
val strong_mng_induction = save_thm(
  "strong_mng_induction",
  IndDefRules.derive_strong_induction
  ((CONJUNCTS ## I) (CONJ_PAIR meaning)));
(* \#line cholera-model.nw 6280 *)
val meaning_thms = save_thm("meaning_thms", meaning_rules)
val meaning_induction = save_thm("meaning_induction", meaning_ind);
val meaning_cases = save_thm("meaning_cases", meaning_cases);
(* \#line cholera-model.nw 6273 *)
val _ = export_theory();

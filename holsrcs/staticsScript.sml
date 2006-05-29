(* Typing of C(++) expressions *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open typesTheory memoryTheory expressionsTheory

val _ = new_theory "statics";

(* conditions on whether or not a conditional expressions has a given type *)
(* In C++ Standard, this is 5.16 *)
val cond_typing_conds_def = Define`
  cond_typing_conds (gty, t1, t2, restype) =
      scalar_type gty /\
      (arithmetic_type t1 /\ arithmetic_type t2 /\
       (restype = ua_conversions t1 t2) \/
      (?s. (t1 = Class s) /\ (t1 = t2) /\ (t1 = restype)) \/
      pointer_type t1 /\ pointer_type t2 /\
      ((t1 = t2) /\ (restype = t1) \/
       Ptr Void IN {t1; t2} /\ (restype = Ptr Void)) \/
      (t1 = Void) /\ (t2 = t1) /\ (restype = t1))
`;

(* SANITY *)
val cond_typing_conds_det = store_thm(
  "cond_typing_conds_det",
  ``!gty t1 t2 rt1 rt2.
       cond_typing_conds (gty, t1, t2, rt1) ==>
       cond_typing_conds (gty, t1, t2, rt2) ==>
       (rt1 = rt2)``,
  SRW_TAC [][cond_typing_conds_def] THEN
  TRY (FULL_SIMP_TAC (srw_ss()) [arithmetic_type_def] THEN NO_TAC) THEN
  METIS_TAC [type_classes])

(* SANITY *)
val cond_typing_wellformed = store_thm(
  "cond_typing_wellformed",
  ``!gty acs t1 t2 rt.
       cond_typing_conds (gty, t1, t2, rt) /\
       wf_type acs t1 /\ wf_type acs t2 ==>
       wf_type acs rt``,
  SRW_TAC [][cond_typing_conds_def] THEN
  SRW_TAC [][typesTheory.ua_converted_types_well_formed])

val arithmetic_pair_type_def = Define`
  arithmetic_pair_type t1 t2 t =
      arithmetic_type t1 /\ arithmetic_type t2 /\
      (t = ua_conversions t1 t2)
`;

val binary_op_type_def = Define`
    (binary_op_type CPlus t1 t2 t =
      arithmetic_pair_type t1 t2 t \/
      (pointer_type t1 /\ integral_type t2 /\ (t = t1)) \/
      (integral_type t1 /\ pointer_type t2 /\ (t = t2))) /\
    (binary_op_type CMinus t1 t2 t =
      arithmetic_pair_type t1 t2 t \/
      (pointer_type t1 /\ integral_type t2 /\ (t = t1)) \/
      (pointer_type t1 /\ (t1 = t2) /\ (t = ptrdiff_t))) /\
    (binary_op_type CLess t1 t2 t =
      arithmetic_type t1 /\ arithmetic_type t2 /\ (t = Signed Int) \/
      pointer_type t1 /\ (t1 = t2) /\ (t = Signed Int)) /\
    (binary_op_type CGreat t1 t2 t =
      arithmetic_type t1 /\ arithmetic_type t2 /\ (t = Signed Int) \/
      pointer_type t1 /\ (t1 = t2) /\ (t = Signed Int)) /\
    (binary_op_type CLessE t1 t2 t =
      arithmetic_type t1 /\ arithmetic_type t2 /\ (t = Signed Int) \/
      pointer_type t1 /\ (t1 = t2) /\ (t = Signed Int)) /\
    (binary_op_type CGreatE t1 t2 t =
      arithmetic_type t1 /\ arithmetic_type t2 /\ (t = Signed Int) \/
      pointer_type t1 /\ (t1 = t2) /\ (t = Signed Int)) /\
    (binary_op_type CEq t1 t2 t =
      arithmetic_type t1 /\ arithmetic_type t2 /\ (t = Signed Int) \/
      pointer_type t1 /\ (t1 = t2) /\ (t = Signed Int) \/
      pointer_type t1 /\ pointer_type t2 /\
      {Ptr Void} SUBSET {t1; t2} /\ (t = Signed Int)) /\
    (binary_op_type CNotEq t1 t2 t =
      arithmetic_type t1 /\ arithmetic_type t2 /\ (t = Signed Int) \/
      pointer_type t1 /\ (t1 = t2) /\ (t = Signed Int) \/
      pointer_type t1 /\ pointer_type t2 /\
      {Ptr Void} SUBSET {t1; t2} /\ (t = Signed Int)) /\
    (binary_op_type CTimes t1 t2 t = arithmetic_pair_type t1 t2 t) /\
    (binary_op_type CDiv t1 t2 t = arithmetic_pair_type t1 t2 t) /\
    (binary_op_type CMod t1 t2 t =
      integral_type t1 /\ integral_type t2 /\
      (t = ua_conversions t1 t2))
`

val unary_op_type_def = Define`
    (unary_op_type CUnPlus t0 t =
      arithmetic_type t0 /\ (t = integral_promotions t0)) /\
    (unary_op_type CUnMinus t0 t =
      arithmetic_type t0 /\ (t = integral_promotions t0)) /\
    (unary_op_type CComp t0 t =
      integral_type t0 /\ (t = integral_promotions t0)) /\
    (unary_op_type CNot t0 t = scalar_type t0 /\ (t = Signed Int)) /\
    (unary_op_type CNullFunRef t0 t =
       (?rt args_t. t0 = Function rt args_t) /\ (t = Signed Int))
`

val ass_type_conds_def0 = Defn.Hol_defn "ass_type_conds"
  `(ass_type_conds (NONE, t1, t2) =
      ~array_type t1 /\ ((t1 = t2) \/
                         arithmetic_type t1 /\ arithmetic_type t2 \/
                         pointer_type t1 /\ pointer_type t2 /\
                         ((t1 = Ptr Void) \/ (t2 = Ptr Void)))) /\
   (ass_type_conds (SOME f, t1, t2) =
      f IN {CPlus; CMinus; CTimes; CDiv; CMod} /\
      ?t. binary_op_type f t1 t2 t /\
          ass_type_conds (NONE, t1, t))`;

val (ass_type_conds,_) = Defn.tprove(
  ass_type_conds_def0,
  WF_REL_TAC `measure (option_case 0 (\x.1) o FST)`)
val _ = save_thm("ass_type_conds", ass_type_conds);

(* SANITY *)
val ops_dont_produce_arrays = store_thm(
  "ops_dont_produce_arrays",
  ``(!f t1 t2 rt. binary_op_type f t1 t2 rt ==> ~array_type rt) /\
    (!f t0 rt.    unary_op_type f t0 rt ==> ~array_type rt)``,
  CONJ_TAC THEN GEN_TAC THENL [
    STRUCT_CASES_TAC (Q.SPEC `f` expressionsTheory.c_binops_nchotomy),
    STRUCT_CASES_TAC (Q.SPEC `f` expressionsTheory.c_unops_nchotomy)
  ] THEN SRW_TAC [][binary_op_type_def, unary_op_type_def,
    arithmetic_pair_type_def] THEN
  METIS_TAC [type_classes, integral_type_def, integral_promotions_safe,
             ua_conversions_safe]);

val _ = Hol_datatype `expr_value_type = LValue | RValue`;

val (expr_type_rules, expr_type_ind, expr_type_cases) = Hol_reln`

  (!s e t. ~array_type t /\ expr_type s LValue e t
               ==>
           expr_type s RValue e t) /\

  (!s e bt n. expr_type s LValue (^e e) (^t (Array bt n))
                 ==>
              expr_type s RValue (^e e) (^t (Ptr bt))) /\

  (!s n. expr_type s RValue (^e (Cnum n)) (^t (Signed Int))) /\

  (!s c. expr_type s RValue (^e (Cchar c)) (^t (Signed Int))) /\

  (!smap tmap t.
      well_formed_type smap t ==>
      expr_type (smap,tmap) RValue (^e (Cnullptr t)) (^t (Ptr t))) /\

  (!smap tmap n.
      well_formed_type smap (tmap n) /\ ~(tmap n = Void)
         ==>
      expr_type (smap,tmap) LValue (^e (Var n)) (^t (tmap n))) /\

  (!smap tmap n t.
      well_formed_type smap t /\ ~(t = Void)
         ==>
      expr_type (smap,tmap) LValue (^e (LVal n t)) (^t t)) /\

  (!smap tmap v t.
      well_formed_type smap t /\ ~array_type t
         ==>
      expr_type (smap,tmap) RValue (^e (ECompVal v t)) (^t t)) /\

  (!s e t.  expr_type s RValue (^e e) (^t t)
              ==>
            expr_type s RValue (^e (RValreq e)) (^t t)) /\

  (!smap tmap e t t0.
      well_formed_type smap t /\ (scalar_type t \/ (t = Void)) /\
      expr_type (smap, tmap) RValue (^e e) (^t t0)
          ==>
      expr_type (smap,tmap) RValue (^e (Cast t e)) (^t t)) /\

  (!env v t. expr_type env v (^e UndefinedExpr) (^t t)) /\

  (!s e1 e2 rt args.
       expr_type s RValue (^e e1)  (^t (Function rt args)) /\
       expr_type s RValue (^el e2) (^tl args)
          ==>
       expr_type s RValue (^e (FnApp e1 e2)) (^t rt)) /\

(!s e1 e2 rt args.
     expr_type s RValue (^e e1)  (^t (Function rt args)) /\
     expr_type s RValue (^el e2) (^tl args) ==>
     expr_type s RValue (^e (FnApp_sqpt e1 e2)) (^t rt))
(* \#line cholera-model.nw 2337 *)
                          /\

(* \#line cholera-model.nw 2516 *)
(!s e t. expr_type s LValue (^e e) (^t t) /\ scalar_type t ==>
         expr_type s RValue (^e (PostInc e)) (^t t)) /\

(!s e t0 f t. expr_type s RValue (^e e) (^t t0) /\
              unary_op_type f t0 t ==>
              expr_type s RValue (^e (CApUnary f e)) (^t t)) /\

(!s e1 t1 e2 t2 t f.
     expr_type s RValue (^e e1) (^t t1) /\
     expr_type s RValue (^e e2) (^t t2) /\
     binary_op_type f t1 t2 t ==>
     expr_type s RValue (^e (CApBinary f e1 e2)) (^t t))
(* \#line cholera-model.nw 2338 *)
                            /\

(* \#line cholera-model.nw 2535 *)
(!s e1 t1 e2 t2.
     expr_type s RValue (^e e1) (^t t1) /\
     expr_type s RValue (^e e2) (^t t2) /\
     scalar_type t1 /\ scalar_type t2 ==>
     expr_type s RValue (^e (CAnd e1 e2)) (^t (Signed Int))) /\

(!s e1 t1 e2 t2.
     expr_type s RValue (^e e1) (^t t1) /\
     expr_type s RValue (^e e2) (^t t2) /\
     scalar_type t1 /\ scalar_type t2 ==>
     expr_type s RValue (^e (COr e1 e2)) (^t (Signed Int))) /\
(* \#line cholera-model.nw 2551 *)
(!s e t. expr_type s RValue (^e e) (^t t) /\ scalar_type t ==>
         expr_type s RValue (^e (CAndOr_sqpt e)) (^t (Signed Int))) /\
(* \#line cholera-model.nw 2601 *)
(!s e1 gty e2 t2 e3 t3 restype.
     expr_type s RValue (^e e1) (^t gty) /\
     expr_type s RValue (^e e2) (^t t2)  /\
     expr_type s RValue (^e e3) (^t t3)  /\
     cond_typing_conds (gty, t2, t3, restype) ==>
     expr_type s RValue  (^e (CCond e1 e2 e3)) (^t restype))
(* \#line cholera-model.nw 2339 *)
                                    /\

(* \#line cholera-model.nw 2632 *)
(!s e1 lhs_t e2 rhs_t f b.
     expr_type s LValue (^e e1) (^t lhs_t) /\
     expr_type s RValue (^e e2) (^t rhs_t) /\
     ass_type_conds (f, lhs_t, rhs_t) ==>
     expr_type s RValue (^e (Assign f e1 e2 b)) (^t lhs_t))
(* \#line cholera-model.nw 2340 *)
                                /\

(* \#line cholera-model.nw 2617 *)
(!s e t. expr_type s RValue (^e e) (^t (Ptr t)) /\ ~(t = Void) ==>
         expr_type s LValue (^e (Deref e)) (^t t)) /\

(!s e t. expr_type s LValue (^e e) (^t t) ==>
         expr_type s RValue (^e (Addr e)) (^t (Ptr t)))
(* \#line cholera-model.nw 2341 *)
                                        /\

(* \#line cholera-model.nw 2650 *)
(!s tm e sn n t.
     expr_type (s,tm) LValue (^e e) (^t (Struct sn)) /\
     lookup_field_info (s sn) n t ==>
     expr_type (s,tm) LValue (^e (SVar e n)) (^t t)) /\

(!s tm e sn n t.
     expr_type (s, tm) RValue (^e e) (^t (Struct sn)) /\
     lookup_field_info (s sn) n t /\ ~array_type t ==>
     expr_type (s, tm) RValue (^e (SVar e n)) (^t t))
(* \#line cholera-model.nw 2342 *)
                                    /\

(* \#line cholera-model.nw 2665 *)
(!s. expr_type s RValue (^el []) (^tl [])) /\

(!s hde hdt tle tlt.
     expr_type s RValue (^e hde)  (^t hdt) /\
     expr_type s RValue (^el tle) (^tl tlt) ==>
     expr_type s RValue (^el (hde :: tle)) (^tl (hdt :: tlt)))
  /\
(* \#line cholera-model.nw 2681 *)
(!s e1 e2 t0 t. expr_type s RValue (^e e2) (^t t) /\
                expr_type s RValue (^e e1) (^t t0) ==>
                expr_type s RValue (^e (CommaSep e1 e2)) (^t t))
(* \#line cholera-model.nw 2343 *)
                                     `
end;
(* \#line cholera-model.nw 2353 *)
val e_cases =
  (concl >- strip_forall >- snd >- strip_disj >-
   map (strip_exists >- snd >- rhs))
  (cholexprTheory.CExpr_nchotomy)
val lvalue_typing = save_thm(
  "lvalue_typing",
  LIST_CONJ
    (map (GEN_ALL o
          (fn t =>
           (ONCE_REWRITE_CONV [expr_type_cases] THENC SIMP_CONV (srw_ss()) [])
          ``expr_type env LValue (INL ^t) t``)) e_cases));
(* \#line cholera-model.nw 2370 *)
val rvalue_typing = save_thm(
  "rvalue_typing",
  LIST_CONJ (map (GEN_ALL o (fn t =>
    (ONCE_REWRITE_CONV [expr_type_cases] THENC SIMP_CONV (srw_ss()) [])
    ``expr_type env RValue (INL ^t) t``)) e_cases));
val list_etype_rewrites =
  CONJ (GEN_ALL
          ((ONCE_REWRITE_CONV [expr_type_cases] THENC
            SIMP_CONV hol_ss []) ``expr_type s v (INR []) t``))
       (GEN_ALL
          ((ONCE_REWRITE_CONV [expr_type_cases] THENC
            SIMP_CONV hol_ss [])
           ``expr_type s v (INR (CONS e es)) t``))
val expr_type_rewrites = save_thm(
  "expr_type_rewrites",
  LIST_CONJ [lvalue_typing, rvalue_typing, list_etype_rewrites]);
val expr_typing = save_thm(
  "expr_typing",
  LIST_CONJ (
     map
      (fn t => GEN_ALL (
        (ONCE_REWRITE_CONV [expr_type_cases] THENC SIMP_CONV (srw_ss()) [])
      ``expr_type senv v (INL ^t) t``)) e_cases));
(* \#line cholera-model.nw 2694 *)
val unary_op_type_well_formed = store_thm(
  "unary_op_type_well_formed",
  ``!f t0 t1. unary_op_type f t0 t1 ==>
              !smap. well_formed_type smap t1``,
  GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `f` cholexprTheory.c_unops_nchotomy) THEN
  SIMP_TAC hol_ss [unary_op_type,
    choltypeTheory.integral_promotions,
    choltypeTheory.arithmetic_type,
    choltypeTheory.integral_type,
    pred_setTheory.IN_INSERT,
    pred_setTheory.NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC hol_ss [choltypeTheory.wf_type_rewrites,
                       choltypeTheory.well_formed_type]);
(* \#line cholera-model.nw 2714 *)
val binary_op_type_well_formed = store_thm(
  "binary_op_type_well_formed",
  ``!f t1 t2 t smap.
        well_formed_type smap t1 /\ well_formed_type smap t2 ==>
        binary_op_type f t1 t2 t ==> well_formed_type smap t``,
  GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `f` cholexprTheory.c_binops_nchotomy) THEN
  SIMP_TAC hol_ss [binary_op_type, arithmetic_pair_type] THEN
  REPEAT STRIP_TAC THEN ELIM_TAC THEN
  ASM_SIMP_TAC hol_ss [
    choltypeTheory.ua_converted_types_well_formed,
    choltypeTheory.ptrdiff_t_well_formed,
    choltypeTheory.well_formed_type_THM]);
(* \#line cholera-model.nw 2732 *)
val ctype_distinct = let val bt = choltypeTheory.CType_distinct
                     in CONJ bt (GSYM bt) end;
open cholexprTheory
val expr_type_well_formed_lemma = prove(
  ``!s v x r.
       expr_type s v x r ==>
       (!e t smap tmap.
           (x = INL e) ==> (r = INL t) ==> (s = (smap,tmap)) ==>
           has_no_undefineds e ==>
           well_formed_type smap t /\
           ((v = LValue) ==> ~(t = Void))) /\
       (!el tl smap tmap.
           (x = INR el) ==> (r = INR tl) ==> (s = (smap, tmap)) ==>
           ALL_EL has_no_undefineds el ==>
           ALL_EL (well_formed_type smap) tl /\
           (v = RValue))``,
  HO_MATCH_MP_TAC expr_type_ind THEN REPEAT CONJ_TAC THEN
  SIMP_TAC (srw_ss()) [
    choltypeTheory.well_formed_type_THM,
    choltypeTheory.ua_converted_types_well_formed,
    choltypeTheory.lookup_field_info,
    GSYM RIGHT_FORALL_IMP_THM, has_no_undefineds] THEN
  dMESON_TAC 10 [unary_op_type_well_formed,
    binary_op_type_well_formed, cond_typing_wellformed] THEN
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC hol_ss [
    choltypeTheory.well_formed_type_THM,
    choltypeTheory.ua_converted_types_well_formed,
    choltypeTheory.str_info_11] THEN ELIM_TAC THEN
  FULL_SIMP_TAC hol_ss [choltypeTheory.str_info_struct_info,
                        MEM_MAP] THEN
  ASM_MESON_TAC [pairTheory.SND]);
val expr_type_well_formed = save_thm(
  "expr_type_well_formed",
  SIMP_RULE (hol_ss ++ impnorm_set) [
    GSYM RIGHT_FORALL_IMP_THM, FORALL_AND_THM, GSYM CONJ_ASSOC
  ] expr_type_well_formed_lemma);
(* \#line cholera-model.nw 2778 *)
val type11 = choltypeTheory.CType_11
local
  val base = choltypeTheory.CType_distinct
in
  val type_distinct = CONJ base (GSYM base)
end
val TYPE_ss = simpLib.rewrites [type11, type_distinct,
  choltypeTheory.arithmetic_type,
  choltypeTheory.integral_type,
  choltypeTheory.pointer_type,
  choltypeTheory.array_type
]
val type_ss = hol_ss ++ TYPE_ss
val type_rwt = FULL_SIMP_TAC type_ss []
(* \#line cholera-model.nw 2797 *)
val c_unops_cases = cholexprTheory.c_unops_nchotomy
val c_binops_cases = cholexprTheory.c_binops_nchotomy
val unary_op_type_det = store_thm(
  "unary_op_type_det",
  ``!f t0 t1.
       unary_op_type f t0 t1 ==>
       (!t2. unary_op_type f t0 t2 ==> (t1 = t2))``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `f` c_unops_cases) THEN
  SIMP_TAC hol_ss [unary_op_type]);
(* \#line cholera-model.nw 2812 *)
val binary_op_type_det = store_thm(
  "binary_op_type_det",
  ``!f t1 t2 t.
       binary_op_type f t1 t2 t ==>
       (!t'. binary_op_type f t1 t2 t' ==> (t' = t))``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `f` c_binops_cases) THEN
  SIMP_TAC type_ss [binary_op_type, arithmetic_pair_type] THEN
  REPEAT STRIP_TAC THEN ELIM_TAC THEN type_rwt);
(* \#line cholera-model.nw 2828 *)
val strong_type_induction =
  IndDefRules.derive_strong_induction(CONJUNCTS expr_type_rules, expr_type_ind)
val is_ultimately_imp = strip_forall >- snd >- is_imp
fun last_imp_conv c t =
  if (is_imp t) then
    if (is_ultimately_imp (snd (dest_imp t))) then
      RAND_CONV (last_imp_conv c) t
    else
      c t
  else if (is_forall t) then
      STRIP_QUANT_CONV (last_imp_conv c) t
  else
      raise (Fail "Not an implication")
val naive_ss = let
  open simpLib boolSimps listSimps rich_listSimps sumSimps pairSimps pureSimps
in
  mk_simpset [PURE_ss, BOOL_ss, PAIR_ss, LIST_ss, UNWIND_ss, SUM_ss, NOT_ss]
end;
val strong_res_tac =
  REPEAT (FIRST_X_ASSUM
    (tofl (concl >- is_forall) >-
     tofl (concl >- strip_forall >- snd >- is_neg >- not) >-
     res_search true [] [] >- REPEAT))
fun type_rwt_non_forall (asl, g) =
  (if all (not o is_forall) asl then
     ABBREV_TAC ``tmapn = (tmap:string->CType) n`` THEN
     POP_ASSUM (K ALL_TAC) THEN ELIM_TAC THEN type_rwt
   else
     NO_TAC) (asl, g)
fun lfi_free_tac (asl, g) =
  (if (all (not o free_in ``lookup_field_info``) asl) then
       strong_res_tac THEN type_rwt THEN
       MAP_EVERY (IMP_RES_TAC >- TRY) [unary_op_type_det,
         binary_op_type_det, cond_typing_conds_det] THEN
       type_rwt THEN ELIM_TAC THEN type_rwt
  else
       NO_TAC) (asl, g)

val lfi_tac =
  IMP_RES_TAC expr_type_well_formed THEN
  type_rwt THEN strong_res_tac THEN ELIM_TAC THEN type_rwt THEN
  IMP_RES_TAC (choltypeTheory.lfi_det) THEN type_rwt THEN
  ELIM_TAC THEN type_rwt THEN NO_TAC


val struct_lval_is_rval = prove(
  ``!s e sn. expr_type s LValue (INL e) (INL (Struct sn)) ==>
             expr_type s RValue (INL e) (INL (Struct sn))``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [expr_type_cases] THEN type_rwt)

val better_lfi_det = prove(
  ``!smap sn n. well_formed_type smap (Struct sn) ==>
                !t. lookup_field_info (smap sn) n t ==>
                    !t'. lookup_field_info (smap sn) n t' = (t' = t)``,
  PROVE_TAC [choltypeTheory.lfi_det]);

val expr_type_det_lemma = prove(
  ``!s v e t.
       expr_type s v e t ==>
       (!ex. (e = INL ex) ==> has_no_undefineds ex) ==>
       (!exl. (e = INR exl) ==> ALL_EL has_no_undefineds exl) ==>
       (!t'. expr_type s v e t' = (t' = t)) /\
       ((v = LValue) ==>
        !t0. (t = INL t0) ==>
             (!bt n. (t0 = Array bt n) ==>
                     !t'. expr_type s RValue e t' = (t' = INL (Ptr bt))) /\
             (~array_type t0 ==>
              !t'. expr_type s RValue e t' = (t' = t)))``,
  HO_MATCH_MP_TAC strong_type_induction THEN
  SRW_TAC [ETA_ss][has_no_undefineds,  choltypeTheory.array_type,
                   lvalue_typing] THEN
  ASM_SIMP_TAC (srw_ss()) [expr_type_rewrites, choltypeTheory.array_type] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  dMESON_TAC 10 [unary_op_type_det, binary_op_type_det,
                 sumTheory.INR_INL_11, cond_typing_conds_det] THEN
  (* four goals at this point; all about typing of field selections *)
  `well_formed_type s (Struct sn)` by PROVE_TAC [expr_type_well_formed] THEN
  nres_search_then 2 false [][] ASSUME_TAC better_lfi_det THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  EQ_TAC THEN SRW_TAC [][] THEN
  IMP_RES_THEN MP_TAC struct_lval_is_rval THEN
  SRW_TAC [][] THEN PROVE_TAC []);
val expr_type_det0 = save_thm(
  "expr_type_det0",
  SIMP_RULE (hol_ss ++ impnorm_set) [
    GSYM RIGHT_FORALL_IMP_THM, FORALL_AND_THM
  ] expr_type_det_lemma);
val expr_type_det = store_thm(
  "expr_type_det",
  ``!e v s t1 t2.
      expr_type s v (INL e) (INL t1) /\
      expr_type s v (INL e) (INL t2) /\
      has_no_undefineds e ==>
      (t1 = t2)``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC expr_type_det0 THEN
  RULE_ASSUM_TAC (SIMP_RULE hol_ss []) THEN RES_TAC THEN
  FULL_SIMP_TAC hol_ss []);
(* \#line cholera-model.nw 2932 *)
val expr_type_lists0 = prove(
  ``(!s v tlr. expr_type s v (INR []) tlr =
               (tlr = INR []) /\ (v = RValue)) /\
    (!s v elr. expr_type s v elr (INR []) =
               (elr = INR []) /\ (v = RValue)) /\
    (!s v e el trl.
               expr_type s v (INR (e::el)) tlr =
               (v = RValue) /\
               ?t tl. (tlr = INR (t::tl)) /\
                      expr_type s v (INL e) (INL t) /\
                      expr_type s v (INR el) (INR tl)) /\
    (!s v elr t tl.
               expr_type s v elr (INR (t::tl)) =
               (v = RValue) /\
               ?e el. (elr = INR (e::el)) /\
                      expr_type s v (INL e) (INL t) /\
                      expr_type s v (INR el) (INR tl))``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [expr_type_cases])) THEN
  SIMP_TAC hol_ss [] THEN MESON_TAC []);
open SingleStep;
val expr_type_lists_append = prove(
  ``(!s v el1 el2 tlr.
               expr_type s v (INR (APPEND el1 el2)) tlr =
               (v = RValue) /\
               ?tl1 tl2. (tlr = INR (APPEND tl1 tl2)) /\
                         expr_type s v (INR el1) (INR tl1) /\
                         expr_type s v (INR el2) (INR tl2)) /\
    (!s v tl1 tl2 elr.
               expr_type s v elr (INR (APPEND tl1 tl2)) =
               (v = RValue) /\
               ?el1 el2. (elr = INR (APPEND el1 el2)) /\
                         expr_type s v (INR el1) (INR tl1) /\
                         expr_type s v (INR el2) (INR tl2))``,
  CONJ_TAC THEN NTAC 2 GEN_TAC THEN
  INDUCT_THEN listTheory.list_INDUCT STRIP_ASSUME_TAC THEN
  SIMP_TAC hol_ss [expr_type_lists0] THENL [
    REPEAT GEN_TAC THEN
    CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [expr_type_cases])) THEN
    SIMP_TAC hol_ss [] THEN EQ_TAC THEN STRIP_TAC THEN
    ELIM_TAC THEN ASM_SIMP_TAC hol_ss [expr_type_lists0] THEN
    Cases_on `el2` THEN FULL_SIMP_TAC hol_ss [expr_type_lists0],
    REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ELIM_TAC THEN
    FIRST_X_ASSUM (tofl (concl >- is_forall) >- ASSUME_TAC) THEN
    FULL_SIMP_TAC (hol_ss ++ exdisj_set) [] THEN ASM_MESON_TAC [],
    REPEAT GEN_TAC THEN
    CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [expr_type_cases])) THEN
    SIMP_TAC hol_ss [] THEN EQ_TAC THEN STRIP_TAC THEN
    ELIM_TAC THEN ASM_SIMP_TAC hol_ss [expr_type_lists0] THEN
    Cases_on `el2` THEN FULL_SIMP_TAC hol_ss [expr_type_lists0],
    REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ELIM_TAC THEN
    FIRST_X_ASSUM (tofl (concl >- is_forall) >- ASSUME_TAC) THEN
    FULL_SIMP_TAC (hol_ss ++ exdisj_set) [] THEN ASM_MESON_TAC []
  ]);

val expr_type_lists = save_thm(
  "expr_type_lists",
  CONJ expr_type_lists0 expr_type_lists_append);
val expr_type_blank_lists = store_thm(
  "expr_type_blank_lists",
  ``(!s v el tlr. expr_type s v (INR el) tlr =
                  (v = RValue) /\
                  ?tl. (tlr = INR tl) /\ (LENGTH el = LENGTH tl) /\
                       expr_type s v (INR el) (INR tl)) /\
    (!s v tl elr. expr_type s v elr (INR tl) =
                  (v = RValue) /\
                  ?el. (elr = INR el) /\ (LENGTH el = LENGTH tl) /\
                       expr_type s v (INR el) (INR tl))``,
  CONJ_TAC THEN NTAC 2 GEN_TAC THEN
  INDUCT_THEN listTheory.list_INDUCT STRIP_ASSUME_TAC THEN
  SIMP_TAC hol_ss [expr_type_lists] THEN dMESON_TAC 10 [] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ELIM_TAC THEN
  SIMP_TAC (hol_ss ++ exdisj_set) [] THEN REPEAT CONJ_TAC THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_MESON_TAC [sumTheory.INR_INL_11]);

(* \#line cholera-model.nw 2311 *)
val _ = export_theory();


val _ = export_theory();

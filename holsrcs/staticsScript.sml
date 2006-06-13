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

(* t1 is the type of the lvalue, t2 is the type of the RHS.
   ass_type_conds checks whether the two are compatible. *)
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

val lookup_field_info_def = Define`
  lookup_field_info s n t = MEM (n,t) s
`;
val nodup_flds_def = Define`
  nodup_flds s = ALL_DISTINCT (MAP FST s)
`

val nodups_lfi_det = store_thm(
  "nodups_lfi_det",
  ``!s n t.
       nodup_flds s /\ lookup_field_info s n t ==>
       !t'. lookup_field_info s n t' ==> (t' = t)``,
  SRW_TAC [][nodup_flds_def, lookup_field_info_def] THEN Induct_on `s` THEN
  SRW_TAC [][listTheory.MEM_MAP] THEN
  FULL_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN PROVE_TAC []);

val _ = Hol_datatype `expr_value_type = LValue | RValue`;

val (expr_type_rules, expr_type_ind, expr_type_cases) = Hol_reln`

  (!s e t. ~array_type t /\ expr_type s LValue e t
               ==>
           expr_type s RValue e t) /\

  (!s e bt n. expr_type s LValue e (Array bt n)
                 ==>
              expr_type s RValue e (Ptr bt)) /\

  (!s n. expr_type s RValue (Cnum n) (Signed Int)) /\

  (!s c. expr_type s RValue (Cchar c) (Signed Int)) /\

  (!smap tmap t.
      wf_type smap t ==>
      expr_type (smap,tmap) RValue (Cnullptr t) (Ptr t)) /\

  (!smap tmap n.
      wf_type smap (tmap n) /\ ~(tmap n = Void)
         ==>
      expr_type (smap,tmap) LValue (Var n) (tmap n)) /\

  (!smap tmap n t.
      wf_type smap t /\ ~(t = Void)
         ==>
      expr_type (smap,tmap) LValue (LVal n t) t) /\

  (!smap tmap v t.
      wf_type smap t /\ ~array_type t
         ==>
      expr_type (smap,tmap) RValue (ECompVal v t) t) /\

  (!s e t.  expr_type s RValue e t
              ==>
            expr_type s RValue (RValreq e) t) /\

  (!smap tmap e t t0.
      wf_type smap t /\ (scalar_type t \/ (t = Void)) /\
      expr_type (smap, tmap) RValue e t0
          ==>
      expr_type (smap,tmap) RValue (Cast t e) t) /\

  (!env v t. expr_type env v UndefinedExpr t) /\

  (!s e1 e2 rt args.
       expr_type s RValue e1  (Function rt args) /\
       expr_typel s e2 args
          ==>
       expr_type s RValue (FnApp e1 e2) rt) /\

  (!s e1 e2 rt args.
       expr_type s RValue e1  (Function rt args) /\
       expr_typel s e2 args
          ==>
       expr_type s RValue (FnApp_sqpt e1 e2) rt) /\

  (!s e t.
       expr_type s LValue e t /\ scalar_type t ==>
       expr_type s RValue (PostInc e) t) /\

  (!s e t0 f t. expr_type s RValue e t0 /\
                unary_op_type f t0 t ==>
                expr_type s RValue (CApUnary f e) t) /\

  (!s e1 t1 e2 t2 t f.
       expr_type s RValue e1 t1 /\
       expr_type s RValue e2 t2 /\
       binary_op_type f t1 t2 t ==>
       expr_type s RValue (CApBinary f e1 e2) t) /\

  (!s e1 t1 e2 t2.
       expr_type s RValue e1 t1 /\
       expr_type s RValue e2 t2 /\
       scalar_type t1 /\ scalar_type t2 ==>
       expr_type s RValue (CAnd e1 e2) (Signed Int)) /\

  (!s e1 t1 e2 t2.
       expr_type s RValue e1 t1 /\
       expr_type s RValue e2 t2 /\
       scalar_type t1 /\ scalar_type t2
         ==>
       expr_type s RValue (COr e1 e2) (Signed Int)) /\

  (!s e t. expr_type s RValue e t /\ scalar_type t ==>
           expr_type s RValue (CAndOr_sqpt e) (Signed Int)) /\

  (!s e1 gty e2 t2 e3 t3 restype.
       expr_type s RValue e1 gty /\
       expr_type s RValue e2 t2  /\
       expr_type s RValue e3 t3  /\
       cond_typing_conds (gty, t2, t3, restype)
         ==>
       expr_type s RValue  (CCond e1 e2 e3) restype) /\

  (!s e1 lhs_t e2 rhs_t f b.
       expr_type s LValue e1 lhs_t /\
       expr_type s RValue e2 rhs_t /\
       ass_type_conds (f, lhs_t, rhs_t) ==>
       expr_type s RValue (Assign f e1 e2 b) lhs_t) /\

  (!s e t. expr_type s RValue e (Ptr t) /\ ~(t = Void) ==>
           expr_type s LValue (Deref e) t) /\

  (!s e t. expr_type s LValue e t ==>
           expr_type s RValue (Addr e) (Ptr t)) /\

  (!s tm e sn n t.
       expr_type (s,tm) LValue e (Class sn) /\
       lookup_field_info (s sn) n t ==>
       expr_type (s,tm) LValue (SVar e n) t) /\

  (!s tm e sn n t.
       expr_type (s, tm) RValue e (Class sn) /\
       lookup_field_info (s sn) n t /\ ~array_type t ==>
       expr_type (s, tm) RValue (SVar e n) t) /\

  (!s e1 e2 t0 t.
       expr_type s RValue e2 t /\
       expr_type s RValue e1 t0 ==>
       expr_type s RValue (CommaSep e1 e2) t) /\

  (!s. expr_typel s [] []) /\

  (!s hde hdt tle tlt.
       expr_type s RValue hde  hdt /\
       expr_typel s tle tlt
         ==>
       expr_typel s (hde :: tle) (hdt :: tlt))
`

infix >-
fun (f >- g) = g o f
val e_cases =
  (concl >- strip_forall >- snd >- strip_disj >-
   map (strip_exists >- snd >- rhs))
  (expressionsTheory.CExpr_nchotomy)
val lvalue_typing = save_thm(
  "lvalue_typing",
  LIST_CONJ
    (map (GEN_ALL o
          (fn t =>
           (ONCE_REWRITE_CONV [expr_type_cases] THENC SIMP_CONV (srw_ss()) [])
          ``expr_type env LValue ^t t``)) e_cases));
val rvalue_typing = save_thm(
  "rvalue_typing",
  LIST_CONJ (map (GEN_ALL o (fn t =>
    (ONCE_REWRITE_CONV [expr_type_cases] THENC SIMP_CONV (srw_ss()) [])
    ``expr_type env RValue ^t t``)) e_cases));
val list_etype_rewrites =
  CONJ (GEN_ALL
          ((ONCE_REWRITE_CONV [expr_type_cases] THENC
            SIMP_CONV (srw_ss()) []) ``expr_typel s [] t``))
       (GEN_ALL
          ((ONCE_REWRITE_CONV [expr_type_cases] THENC
            SIMP_CONV (srw_ss()) [])
           ``expr_typel s (e:: es) t``))
val expr_type_rewrites = save_thm(
  "expr_type_rewrites",
  LIST_CONJ [lvalue_typing, rvalue_typing, list_etype_rewrites]);
val expr_typing = save_thm(
  "expr_typing",
  LIST_CONJ (
     map
      (fn t => GEN_ALL (
        (ONCE_REWRITE_CONV [expr_type_cases] THENC SIMP_CONV (srw_ss()) [])
      ``expr_type senv v ^t t``)) e_cases));

(* SANITY *)
val unary_op_type_det = store_thm(
  "unary_op_type_det",
  ``!f t0 t1.
       unary_op_type f t0 t1 ==>
       (!t2. unary_op_type f t0 t2 ==> (t1 = t2))``,
  GEN_TAC THEN Cases_on `f` THEN SIMP_TAC (srw_ss()) [unary_op_type_def]);

(* SANITY *)
val binary_op_type_det = store_thm(
  "binary_op_type_det",
  ``!f t1 t2 t.
       binary_op_type f t1 t2 t ==>
       (!t'. binary_op_type f t1 t2 t' ==> (t' = t))``,
  Cases THEN
  SIMP_TAC (srw_ss()) [binary_op_type_def, arithmetic_pair_type_def] THEN
  SRW_TAC [][] THEN METIS_TAC [type_classes]);

val lvalue_rvalue_nonarray = store_thm(
  "lvalue_rvalue_nonarray",
  ``expr_type s LValue e t /\ ~array_type t ==> expr_type s RValue e t``,
  SRW_TAC [][expr_type_rules])
val lvalue_rvalue_array = store_thm(
  "lvalue_rvalue_array",
  ``expr_type s LValue e (Array bt n) ==> expr_type s RValue e (Ptr bt)``,
  PROVE_TAC [expr_type_rules]);


val wf_strmap_def = Define`
  wf_strmap smap = !s. nodup_flds (smap s)
`;

val expr_type_det_lemma = prove(
  ``(!s v e t.
       expr_type s v e t ==>
          has_no_undefineds e ==>
          wf_strmap (FST s) ==>
          (!t'. expr_type s v e t' = (t' = t)) /\
          ((v = LValue) ==>
           (!bt n. (t = Array bt n) ==>
                   !t'. expr_type s RValue e t' = (t' = Ptr bt)) /\
           (~array_type t ==> !t'. expr_type s RValue e t' = (t' = t)))) /\
    (!s e t. expr_typel s e t ==>
               wf_strmap (FST s) ==>
               ALL_EL has_no_undefineds e ==>
               (!t'. expr_typel s e t' = (t' = t)))``,
  HO_MATCH_MP_TAC expr_type_ind THEN
  SRW_TAC [ETA_ss][lvalue_typing] THEN
  ASM_SIMP_TAC (srw_ss()) [expr_type_rewrites] THEN
  FULL_SIMP_TAC (srw_ss()) [wf_type_def] THEN
  METIS_TAC [array_type_def, wf_type_def, unary_op_type_det,
             binary_op_type_det, cond_typing_conds_det, wf_strmap_def,
             nodups_lfi_det, TypeBase.one_one_of ``:CPP_Type``,
             lvalue_rvalue_nonarray])
val expr_type_det0 = save_thm(
  "expr_type_det0",
  SIMP_RULE (srw_ss() ++ DNF_ss) [] expr_type_det_lemma);
val expr_type_det = store_thm(
  "expr_type_det",
  ``!e v s t1 t2.
      expr_type s v e t1 /\ expr_type s v e t2 /\ wf_strmap (FST s) /\
      has_no_undefineds e ==>
      (t1 = t2)``,
  METIS_TAC [expr_type_det0])

val expr_type_lists0 = prove(
  ``(!s tlr. expr_typel s [] tlr = (tlr = [])) /\
    (!s elr. expr_typel s elr [] = (elr = [])) /\
    (!s e el tlr.
               expr_typel s (e::el) tlr =
               ?t tl. (tlr = t::tl) /\
                      expr_type s RValue e t /\
                      expr_typel s el tl) /\
    (!s elr t tl.
               expr_typel s elr (t::tl) =
               ?e el. (elr = e::el) /\
                      expr_type s RValue e t /\
                      expr_typel s el tl)``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [expr_type_cases])) THEN
  SIMP_TAC (srw_ss()) [])

val expr_type_lists_append = prove(
  ``(!s el1 el2 tlr.
               expr_typel s (APPEND el1 el2) tlr =
               ?tl1 tl2. (tlr = APPEND tl1 tl2) /\
                         expr_typel s el1 tl1 /\
                         expr_typel s el2 tl2) /\
    (!s tl1 tl2 elr.
               expr_typel s elr (APPEND tl1 tl2) =
               ?el1 el2. (elr = APPEND el1 el2) /\
                         expr_typel s el1 tl1 /\
                         expr_typel s el2 tl2)``,
  CONJ_TAC THENL [
    Induct_on `el1` THEN SRW_TAC [][expr_type_lists0] THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN METIS_TAC [],
    Induct_on `tl1` THEN SRW_TAC [][expr_type_lists0] THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN METIS_TAC []
  ]);

val expr_type_lists = save_thm(
  "expr_type_lists",
  CONJ expr_type_lists0 expr_type_lists_append);
val expr_typel_list_lengths = store_thm(
  "expr_typel_list_lengths",
  ``!s el tl. expr_typel s el tl ==> (LENGTH el = LENGTH tl)``,
  Induct_on `el` THEN SRW_TAC [][expr_type_lists] THEN
  SRW_TAC [][] THEN METIS_TAC [])

val _ = export_theory();



(* Dynamics for C expression operators *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open utilsTheory typesTheory memoryTheory expressionsTheory
     statesTheory aggregatesTheory class_infoTheory

val _ = new_theory "operators";

(* ----------------------------------------------------------------------
    Statics of operators
   ---------------------------------------------------------------------- *)

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
    (unary_op_type CNot t0 t = scalar_type t0 /\ (t = Signed Int))
`

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


(* ----------------------------------------------------------------------
    Dynamics of operators
   ---------------------------------------------------------------------- *)

(* ASSUMPTION: the REP_INT/INT_VAL functions convert pointer values
               appropriately
*)
val add_pointer_def = Define`
  add_pointer (v1, t1, s1:num) (v2, t2) (res, rt) =
       (rt = t1) /\ integral_type t2 /\ pointer_type t1 /\
       (case (INT_VAL t1 v1, INT_VAL t2 v2) of
           (SOME r1, SOME r2) ->
               (case REP_INT t1 (r1 + &s1 * r2) of
                   SOME r -> (res = r)
                || NONE -> F)
        || _ -> F)
`;

val sub_pointers_def = Define`
  sub_pointers sz (v1, t1) (v2, t2) (res, rt) =
    (rt = ptrdiff_t) /\
    pointer_type t1 /\
    pointer_type t2 /\
    (strip_ptr_const t1 = strip_ptr_const t2) /\
    (case (INT_VAL t1 v1, INT_VAL t2 v2) of
        (SOME r1, SOME r2) ->
            (case REP_INT ptrdiff_t ((r1 - r2) / &sz) of
                SOME r -> (res = r)
             || NONE -> F)
     || _ -> F)
`;

val add_arith_def = Define`
  add_arith (v1, t1) (v2, t2) (res, rt) =
       (rt = ua_conversions t1 t2) /\
       ?i1 i2.
          (INT_VAL t1 v1 = SOME i1) /\
          (INT_VAL t2 v2 = SOME i2) /\
          (SOME res = REP_INT rt (i1 + i2))
`

(* BAD_ASSUMPTION: doesn't distinguish pointer and arithmetic behaviours,
     meaning that there is no check to see that pointers are only compared
     within the same object *)
val relop_def = Define`
  relop f (v1, t1) (v2, t2) (res, rt) =
     (rt = Bool) /\
     ?i1 i2. (INT_VAL t1 v1 = SOME i1) /\
             (INT_VAL t2 v2 = SOME i2) /\
             (if f i1 i2 then SOME res = REP_INT rt 1
              else SOME res = REP_INT rt 0)
`;

val arithop_def = Define`
  arithop f (v1, t1) (v2, t2) (res, rt) =
    (rt = ua_conversions t1 t2) /\
    ?i1 i2. (INT_VAL t1 v1 = SOME i1) /\
            (INT_VAL t2 v2 = SOME i2) /\
            (SOME res = REP_INT rt (f i1 i2))
`;

(* \#line cholera-model.nw 6484 *)
val unop_meaning_def = TotalDefn.Define
   `(unop_meaning CUnPlus m1 t1 res rt =
      unary_op_type CUnPlus t1 rt /\
      ?i1. (SOME i1 = INT_VAL t1 m1) /\
           (SOME res = REP_INT rt i1)) /\

    (unop_meaning CUnMinus m1 t1 res rt =
      unary_op_type CUnMinus t1 rt /\
      ?i1. (SOME i1 = INT_VAL t1 m1) /\
           (SOME res = REP_INT rt (~i1))) /\

    (* BAD_ASSUMPTION: too hard basket *)
    (unop_meaning CComp m1 t1 res rt = F) /\

    (unop_meaning CNot m1 t1 res rt =
       scalar_type t1 /\ (rt = Signed Int) /\
       ?i. (INT_VAL t1 m1 = SOME i) /\
           (SOME res = if i = 0 then REP_INT rt 1 else REP_INT rt 0))
`;



val binop_meaning_defn = Defn.Hol_defn "binop_meaning" `
   (* relational operators *)
   (binop_meaning s CLess m1 t1 m2 t2 res rt =
      binary_op_type CLess t1 t2 rt /\
      relop (<) (m1,t1) (m2,t2) (res,rt)) /\

   (binop_meaning s CGreat m1 t1 m2 t2 res rt =
      binary_op_type CGreat t1 t2 rt /\
      relop (>) (m1,t1) (m2,t2) (res,rt)) /\

   (binop_meaning s CLessE m1 t1 m2 t2 res rt =
      binary_op_type CLessE t1 t2 rt /\
      relop (<=) (m1,t1) (m2,t2) (res,rt)) /\

   (binop_meaning s CGreatE m1 t1 m2 t2 res rt =
      binary_op_type CGreatE t1 t2 rt /\
      relop (>=) (m1,t1) (m2,t2) (res,rt)) /\

   (binop_meaning s CEq m1 t1 m2 t2 res rt =
      binary_op_type CEq t1 t2 rt /\
      relop (=) (m1,t1) (m2,t2) (res,rt)) /\

   (binop_meaning s CNotEq m1 t1 m2 t2 res rt =
      binary_op_type CNotEq t1 t2 rt /\
      relop (\i1 i2. ~(i1 = i2)) (m1,t1) (m2,t2) (res,rt)) /\

   (binop_meaning s CPlus m1 t1 m2 t2 res rt =
      pointer_type t1 /\ ~pointer_type t2 /\
      (?n. sizeof T (sizeofmap s) (dest_ptr t1) n /\
           add_pointer (m1,t1,n) (m2,t2) (res,rt))
         \/
      pointer_type t2 /\ ~pointer_type t1 /\
      (?n. sizeof T (sizeofmap s) (dest_ptr t2) n /\
           add_pointer (m2,t2,n) (m1,t1) (res,rt)) \/
      ~pointer_type t1 /\ ~pointer_type t2 /\
      add_arith (m1,t1) (m2,t2) (res,rt)) /\

   (binop_meaning s CMinus m1 t1 m2 t2 res rt =
      binary_op_type CMinus t1 t2 rt /\
      (pointer_type t1 /\ ~pointer_type t2 /\
       (?res0 rt0. unop_meaning CUnMinus m2 t2 res0 rt0 /\
                   binop_meaning s CPlus m1 t1 res0 rt0 res rt)
           \/
       pointer_type t1 /\ pointer_type t2 /\
       (?sz. sizeof T (sizeofmap s) (dest_ptr t1) sz /\
             sub_pointers sz (m1,t1) (m2,t2) (res,rt))
           \/
       ~pointer_type t1 /\ ~pointer_type t2 /\
       arithop (-) (m1,t1) (m2,t2) (res,rt)))  /\

   (binop_meaning s CTimes m1 t1 m2 t2 res rt =
       binary_op_type CTimes t1 t2 rt /\
       arithop ( * ) (m1,t1) (m2,t2) (res,rt)) /\

   (* BAD_ASSUMPTION: should define a more under-specified integer division *)
   (binop_meaning s CDiv   m1 t1 m2 t2 res rt =
      binary_op_type CDiv t1 t2 rt /\
      arithop (/) (m1,t1) (m2,t2) (res,rt)) /\

   (binop_meaning s CMod   m1 t1 m2 t2 res rt =
      binary_op_type CMod t1 t2 rt /\
      arithop (%) (m1,t1) (m2,t2) (res,rt))
`;

val (binop_meaning_def, _) = Defn.tprove(
  binop_meaning_defn,
  WF_REL_TAC `measure (\p. case FST (SND p) of CMinus -> 1 || _ -> 0)`)

val _ = save_thm("binop_meaning_def", binop_meaning_def)


(* SANITY *)
val relop_det = store_thm(
  "relop_det",
  ``relop f (m1,t1) (m2,t2) (res1,rt1) /\
    relop f (m1,t1) (m2,t2) (res2,rt2) ==>
    (res1 = res2) /\ (rt1 = rt2)``,
  SRW_TAC [][relop_def] THEN METIS_TAC [TypeBase.one_one_of ``:'a option``]);

val unary_ops_det = store_thm(
  "unary_ops_det",
  ``!f s m1 t1 res rt.
        unop_meaning f m1 t1 res rt ==>
        !res' rt'. unop_meaning f m1 t1 res' rt' ==>
                   (res' = res) /\ (rt' = rt)``,
  Cases_on `f` THEN SRW_TAC [][unop_meaning_def] THEN
  METIS_TAC [unary_op_type_det, TypeBase.one_one_of ``:'a option``])

val arithop_det = store_thm(
  "arithop_det",
  ``arithop f (m1,t1) (m2,t2) (res1,rt1) /\
    arithop f (m1,t1) (m2,t2) (res2,rt2) ==>
    (res1 = res2) /\ (rt1 = rt2)``,
  SRW_TAC [][arithop_def] THEN METIS_TAC [TypeBase.one_one_of ``:'a option``]);

val add_pointer_det = store_thm(
  "add_pointer_det",
  ``add_pointer (v1,t1,s1) (v2,t2) (res1,rt1) /\
    add_pointer (v1,t1,s1) (v2,t2) (res2,rt2) ==>
    (res1 = res2) /\ (rt1 = rt2)``,
  SRW_TAC [][add_pointer_def] THEN
  Cases_on `INT_VAL rt1 v1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `INT_VAL t2 v2`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `REP_INT rt1 (x + &s1 * x')` THEN FULL_SIMP_TAC (srw_ss()) [])

val sub_pointers_det = store_thm(
  "sub_pointers_det",
  ``sub_pointers sz (v1,t1) (v2,t2) (res1,rt1) /\
    sub_pointers sz (v1,t1) (v2,t2) (res2,rt2) ==>
    (res1 = res2) /\ (rt1 = rt2)``,
  SRW_TAC [][sub_pointers_def] THEN
  Cases_on `INT_VAL t1 v1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `INT_VAL t2 v2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `REP_INT ptrdiff_t ((x - x') / &sz)` THEN
  FULL_SIMP_TAC (srw_ss()) []);

val binary_ops_det = store_thm(
  "binary_ops_det",
  ``!f s m1 t1 m2 t2 res rt.
       binop_meaning s f m1 t1 m2 t2 res rt ==>
       !res' rt'. binop_meaning s f m1 t1 m2 t2 res' rt' ==>
                  (res' = res) /\ (rt' = rt)``,
  Cases_on `f` THEN
  SRW_TAC [][binop_meaning_def, add_arith_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [relop_det, arithop_det, type_classes, sizeof_det,
             add_pointer_det, sub_pointers_det, unary_ops_det,
             TypeBase.one_one_of ``:'a option``]);

val arithmetic_pair_classes = prove(
  ``!t1 t2 t.
       arithmetic_pair_type t1 t2 t ==>
       arithmetic_type t1 /\ arithmetic_type t2``,
  SIMP_TAC (srw_ss()) [arithmetic_pair_type_def])

val binops_respect_types = store_thm(
  "binops_respect_types",
  ``!f s v1 t1 v2 t2 res rt t.
       binary_op_type f t1 t2 t /\
       binop_meaning s f v1 t1 v2 t2 res rt ==>
       (rt = t)``,
  Cases_on `f` THEN
  SIMP_TAC (srw_ss()) [binop_meaning_def, binary_op_type_def] THEN
  REPEAT STRIP_TAC THEN
  TRY (METIS_TAC [type_classes, arithmetic_pair_classes]) THEN
  FULL_SIMP_TAC (srw_ss()) [arithmetic_pair_type_def, add_arith_def,
                            add_pointer_def]);

val unops_respect_types = store_thm(
  "unops_respect_types",
  ``!f v0 t0 v t rt.
      unary_op_type f t0 t /\ unop_meaning f v0 t0 v rt ==>
      (rt = t)``,
  Cases_on `f` THEN SRW_TAC [][unop_meaning_def, unary_op_type_def])

val _ = export_theory();

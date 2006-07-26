(* Dynamics for C expression operators *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open utilsTheory typesTheory memoryTheory expressionsTheory staticsTheory
     statesTheory class_infoTheory

val _ = new_theory "operators";

(* ASSUMPTION: the REP_INT/INT_VAL functions convert pointer values
               appropriately
*)
val add_pointer_def = Define`
  add_pointer (v1, t1, s1:num) (v2, t2) (res, rt) =
       (rt = t1) /\ integral_type t2 /\ pointer_type t1 /\
       (case (INT_VAL t1 v1, INT_VAL t2 v2) of
           (SOME r1, SOME r2) -> (case REP_INT t1 (r1 + &s1 * r2) of
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
     (rt = Signed Int) /\
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

val binop_meaning_def = Define`
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
      pointer_type t1 /\
      (?n. sizeof (sizeofmap s) (@t. t1 = Ptr t) n /\
           add_pointer (m1,t1,n) (m2,t2) (res,rt)) \/
      pointer_type t2 /\
      (?n. sizeof (sizeofmap s) (@t. t2 = Ptr t) n /\
           add_pointer (m2,t2,n) (m1,t1) (res,rt)) \/
      ~pointer_type t1 /\ ~pointer_type t2 /\
      add_arith (m1,t1) (m2,t2) (res,rt)) /\

   (binop_meaning s CMinus m1 t1 m2 t2 res rt =
      binary_op_type CMinus t1 t2 rt /\
      arithop (-) (m1,t1) (m2,t2) (res,rt)) /\

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

(* SANITY *)
val relop_det = store_thm(
  "relop_det",
  ``relop f (m1,t1) (m2,t2) (res1,rt1) /\
    relop f (m1,t1) (m2,t2) (res2,rt2) ==>
    (res1 = res2) /\ (rt1 = rt2)``,
  SRW_TAC [][relop_def] THEN METIS_TAC [TypeBase.one_one_of ``:'a option``]);

val arithop_det = store_thm(
  "arithop_det",
  ``arithop f (m1,t1) (m2,t2) (res1,rt1) /\
    arithop f (m1,t1) (m2,t2) (res2,rt2) ==>
    (res1 = res2) /\ (rt1 = rt2)``,
  SRW_TAC [][arithop_def] THEN METIS_TAC [TypeBase.one_one_of ``:'a option``]);


val binary_ops_det = store_thm(
  "binary_ops_det",
  ``!f s m1 t1 m2 t2 res rt.
       binop_meaning s f m1 t1 m2 t2 res rt ==>
       !res' rt'. binop_meaning s f m1 t1 m2 t2 res' rt' ==>
                  (res' = res) /\ (rt' = rt)``,
  Cases_on `f` THEN
  SRW_TAC [][binop_meaning_def, add_pointer_def, add_arith_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  TRY (METIS_TAC [relop_det, arithop_det, type_classes,sizeof_det]) THENL [
    Cases_on `INT_VAL rt m1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `INT_VAL t2 m2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    `n = n'` by METIS_TAC [sizeof_det] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `REP_INT rt (x + &n' * x')` THEN
    FULL_SIMP_TAC (srw_ss()) [],
    `n = n'` by METIS_TAC [sizeof_det] THEN
    Cases_on `INT_VAL rt m2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `INT_VAL t1 m1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `REP_INT rt (x + &n' * x')` THEN FULL_SIMP_TAC (srw_ss()) [],
    METIS_TAC [TypeBase.one_one_of ``:'a option``]
  ]);

val unary_ops_det = store_thm(
  "unary_ops_det",
  ``!f s m1 t1 res rt.
        unop_meaning f m1 t1 res rt ==>
        !res' rt'. unop_meaning f m1 t1 res' rt' ==>
                   (res' = res) /\ (rt' = rt)``,
  Cases_on `f` THEN SRW_TAC [][unop_meaning_def] THEN
  METIS_TAC [unary_op_type_det, TypeBase.one_one_of ``:'a option``])

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

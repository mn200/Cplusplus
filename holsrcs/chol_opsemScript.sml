(* \#line cholera-model.nw 26 *)
open HolKernel boolLib Parse mnUtils Psyntax
open simpLib bossLib boolSimps arithmeticTheory pred_setTheory
infix >-

val hol_ss = bossLib.list_ss

(* \#line cholera-model.nw 6344 *)
local open se_infoTheory in end

open cholexprTheory cholstaticsTheory

val _ = new_theory "chol_opsem";
(* \#line cholera-model.nw 6462 *)
val add_pointer = Define`
  add_pointer (v1, t1, s1) (v2, t2) (res, rt) =
       (rt = t1) /\ integral_type t2 /\ pointer_type t1 /\
       (res = num2mval ptr_size (coerce_to_num v2 * s1 +
                                 coerce_to_num v1))`;
(* \#line cholera-model.nw 6472 *)
val add_arith = Define`
  add_arith s (v1, t1) (v2, t2) (res, rt) =
       (rt = ua_conversions t1 t2) /\
       ?v1' v2'. convert_val s (v1, t1) (v1', rt) /\
                 convert_val s (v2, t2) (v2', rt) /\
                 (res = num2mval (gsizeof rt) (coerce_to_num v1' +
                                               coerce_to_num v2'))`;
(* \#line cholera-model.nw 6371 *)
val binop_meaning = Define`
  
(* \#line cholera-model.nw 6384 *)
(binop_meaning s CLess m1 t1 m2 t2 res rt =
   binary_op_type CLess t1 t2 rt /\
   (coerce_to_num m1 < coerce_to_num m2
      => (res = num2mval int_size 1)
      |  (res = num2mval int_size 0))) /\
(binop_meaning s CGreat m1 t1 m2 t2 res rt =
   binary_op_type CGreat t1 t2 rt /\
   (coerce_to_num m1 > coerce_to_num m2
    => (res = num2mval int_size 1)
    |  (res = num2mval int_size 0))) /\
(binop_meaning s CLessE m1 t1 m2 t2 res rt =
   binary_op_type CLessE t1 t2 rt /\
   (coerce_to_num m1 <= coerce_to_num m2
    => (res = num2mval int_size 1)
    |  (res = num2mval int_size 0))) /\
(binop_meaning s CGreatE m1 t1 m2 t2 res rt =
   binary_op_type CGreatE t1 t2 rt /\
   (coerce_to_num m1 >= coerce_to_num m2
    => (res = num2mval int_size 1)
    |  (res = num2mval int_size 0))) /\
(binop_meaning s CEq m1 t1 m2 t2 res rt =
   binary_op_type CEq t1 t2 rt /\
   (coerce_to_num m1 = coerce_to_num m2
    => (res = num2mval int_size 1)
    |  (res = num2mval int_size 0))) /\
(binop_meaning s CNotEq m1 t1 m2 t2 res rt = F)
(* \#line cholera-model.nw 6372 *)
                           /\
  
(* \#line cholera-model.nw 6420 *)
(binop_meaning s CPlus m1 t1 m2 t2 res rt =
   pointer_type t1 /\
   (?n. sizeof s.strmap (INL (@t. t1 = Ptr t)) n /\
        add_pointer (m1,t1,n) (m2,t2) (res,rt)) \/
   pointer_type t2 /\
   (?n. sizeof s.strmap (INL (@t. t2 = Ptr t)) n /\
        add_pointer (m2,t2,n) (m1,t1) (res,rt)) \/
   ~pointer_type t1 /\ ~pointer_type t2 /\
   add_arith s.strmap (m1,t1) (m2,t2) (res,rt)) /\
(binop_meaning s CMinus m1 t1 m2 t2 res rt =
  ?v1 v2.
    arithmetic_pair_type t1 t2 rt /\ (?rbt. rt = Unsigned rbt) /\
    convert_val s.strmap (m1, t1) (v1, rt) /\
    convert_val s.strmap (m2, t2) (v2, rt) /\
    (res = num2mval (gsizeof rt)
      ((coerce_to_num v1 >= coerce_to_num v2)
       => coerce_to_num v1 - coerce_to_num v2
       |  (coerce_to_num v1 + Num (type_max rt) + 1) -
          coerce_to_num v2))) /\
(binop_meaning s CTimes m1 t1 m2 t2 res rt =
  ?v1 v2.
    arithmetic_pair_type t1 t2 rt /\ (?rbt. rt = Unsigned rbt) /\
    convert_val s.strmap (m1, t1) (v1, rt) /\
    convert_val s.strmap (m2, t2) (v2, rt) /\
    (res = num2mval (gsizeof rt)
      ((coerce_to_num v1 * coerce_to_num v2) MOD
        (Num (type_max rt) + 1)))) /\
(binop_meaning s CDiv   m1 t1 m2 t2 res rt = F) /\
(binop_meaning s CMod   m1 t1 m2 t2 res rt = F)
(* \#line cholera-model.nw 6373 *)
                          `;
(* \#line cholera-model.nw 6484 *)
val unop_meaning_def = TotalDefn.Define
   `(unop_meaning (s:CState) CUnPlus m1 t1 res rt = F) /\
    (unop_meaning s CUnMinus m1 t1 res rt = F) /\
    (unop_meaning s CComp m1 t1 res rt = F) /\
    (unop_meaning s CNot m1 t1 res rt =
       scalar_type t1 /\ (rt = Signed Int) /\
       (res = if coerce_to_num m1 = 0 then num2mval int_size 1
              else num2mval int_size 0)) /\
    (unop_meaning s CNullFunRef m1 t1 res rt = F)`;
(* \#line cholera-model.nw 6501 *)
val NOT_IN_EMPTY = pred_setTheory.NOT_IN_EMPTY
val IN_INSERT =    pred_setTheory.IN_INSERT
val c_binops_cases = cholexprTheory.c_binops_nchotomy
val pgen_thm = pairTheory.FORALL_PROD
val int_n_ptr_F = prove(
  --`!t. ~(integral_type t /\ pointer_type t)`--,
  SIMP_TAC pureSimps.pure_ss [choltypeTheory.pointer_type,
                              choltypeTheory.integral_type] THEN
  REPEAT STRIP_TAC THEN ELIM_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC (let val th = choltypeTheory.CType_distinct in
               [th, GSYM th] end));
val binary_ops_det = store_thm(
  "binary_ops_det",
  ``!f s m1 t1 m2 t2 res rt.
       binop_meaning s f m1 t1 m2 t2 res rt ==>
       !res' rt'. binop_meaning s f m1 t1 m2 t2 res' rt' ==>
                  (res' = res) /\ (rt' = rt)``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `f` c_binops_cases) THEN
  SIMP_TAC hol_ss [binop_meaning, add_pointer, add_arith] THEN
  REPEAT GEN_TAC THEN (COND_CASES_TAC ORELSE ALL_TAC) THEN
  SIMP_TAC hol_ss [] THEN REPEAT STRIP_TAC THEN ELIM_TAC THEN
  MAP_EVERY (fn t => TRY (t THEN NO_TAC)) [
    RES_TAC, IMP_RES_TAC int_n_ptr_F,
    IMP_RES_TAC (cholmemTheory.sizeof_det) THEN ELIM_TAC THEN
    RWT,
    IMP_RES_TAC (cholmemTheory.convert_val_det) THEN
    ELIM_TAC THEN RWT,
    IMP_RES_TAC cholstaticsTheory.binary_op_type_det THEN ELIM_TAC THEN RWT,
    FULL_SIMP_TAC hol_ss [cholstaticsTheory.arithmetic_pair_type] THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    IMP_RES_TAC (cholmemTheory.convert_val_det) THEN
    ELIM_TAC THEN RWT
  ]);
val unary_ops_det = store_thm(
  "unary_ops_det",
  --`!f s m1 t1 res rt.
        unop_meaning s f m1 t1 res rt ==>
        !res' rt'. unop_meaning s f m1 t1 res' rt' ==>
                   (res' = res) /\ (rt' = rt)`--,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `f` c_unops_nchotomy) THEN
  SIMP_TAC hol_ss [unop_meaning_def]);
(* \#line cholera-model.nw 6550 *)
val type_classes = choltypeTheory.type_classes
val arithmetic_pair_type = cholstaticsTheory.arithmetic_pair_type
val arithmetic_pair_classes = prove(
  ``!t1 t2 t.
       arithmetic_pair_type t1 t2 t ==>
       arithmetic_type t1 /\ arithmetic_type t2``,
  SIMP_TAC hol_ss [arithmetic_pair_type])
(* \#line cholera-model.nw 6562 *)
val binops_respect_types = store_thm(
  "binops_respect_types",
  ``!f s v1 t1 v2 t2 res rt t.
       binary_op_type f t1 t2 t /\
       binop_meaning s f v1 t1 v2 t2 res rt ==>
       (rt = t)``,
  GEN_TAC THEN SingleStep.Cases_on `f` THEN
  SIMP_TAC hol_ss [binop_meaning, binary_op_type] THEN
  REPEAT STRIP_TAC THEN dMESON_TAC 10 [
    type_classes, arithmetic_pair_classes] THEN
  FULL_SIMP_TAC hol_ss [arithmetic_pair_type, add_arith,
                         add_pointer]);
(* \#line cholera-model.nw 6579 *)
val unops_respect_types = store_thm(
  "unops_respect_types",
  ``!f s v0 t0 v t rt.
      unary_op_type f t0 t /\ unop_meaning s f v0 t0 v rt ==>
      (rt = t)``,
  GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `f` c_unops_nchotomy) THEN
  SIMP_TAC hol_ss [unop_meaning_def, unary_op_type] THEN
  REPEAT STRIP_TAC THEN dMESON_TAC 10 [type_classes]);
(* \#line cholera-model.nw 6353 *)
val _ = export_theory();

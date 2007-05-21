(* Typing of C(++) expressions *)

(* It is a basic premise that every C++ expression has a unique static type. *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open typesTheory memoryTheory expressionsTheory operatorsTheory
     class_infoTheory

val _ = new_theory "statics";


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



val lookup_field_info_def = Define`
  lookup_field_info s n (idx,t) = idx < LENGTH s /\ (EL idx s = (n,t))
`;
val nodup_flds_def = Define`
  nodup_flds s = ALL_DISTINCT (MAP FST s)
`

val lookup_field_info_thm = store_thm(
  "lookup_field_info_thm",
  ``(lookup_field_info [] n (i,t) = F) /\
    (lookup_field_info ((n,ty)::rest) n' (i,ty') =
       (n = n') /\ (i = 0) /\ (ty' = ty) \/
       0 < i /\ lookup_field_info rest n' (i - 1, ty'))``,
  SRW_TAC [][lookup_field_info_def] THEN
  Cases_on `i` THEN SRW_TAC [][] THEN1 METIS_TAC [] THEN
  SRW_TAC [ARITH_ss][EQ_IMP_THM])

val lookup_field_info_MEM = store_thm(
  "lookup_field_info_MEM",
  ``!s n i t. lookup_field_info s n (i,t) ==> MEM (n,t) s``,
  Induct THEN SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][lookup_field_info_thm] THEN METIS_TAC []);

(* SANITY *)
(* if a list of pairs doesn't contain any duplicates amongst the list
   of first components, then the relation that treats it as an association-list
   and looks things up must be deterministic.  (In fact, the lookup here
   returns both the associated second component and the index in the list
   where the key-value pair are stored *)
val nodups_lfi_det = store_thm(
  "nodups_lfi_det",
  ``!s n i t.
       nodup_flds s /\ lookup_field_info s n (i,t) ==>
       !i' t'. lookup_field_info s n (i',t') ==> (i = i') /\ (t' = t)``,
  REWRITE_TAC [nodup_flds_def] THEN Induct_on `s` THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, listTheory.MEM_MAP] THEN
  SRW_TAC [][lookup_field_info_thm, listTheory.MEM_MAP] THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, nodup_flds_def,
                       lookup_field_info_def] THEN
  METIS_TAC [lookup_field_info_MEM,
             DECIDE ``0n < i /\ 0 < i' /\ (i - 1 = i' - 1) ==> (i = i')``]);



val _ = temp_add_record_field ("abs_classes", ``is_abstract``)

val this_type_def = Define`
  this_type s = case s.thisvalue of
                  SOME (ECompVal bytes (Ptr ty)) -> SOME ty
                || _ -> NONE
`;
val _ = temp_add_record_field ("this_type", ``this_type``)

val _ = Hol_datatype `expr_value_type = LValue | RValue`;

val (expr_type_rules, expr_type_ind, expr_type_cases) = Hol_reln`

  (!s e t. ~array_type t /\ expr_type s LValue e t
               ==>
           expr_type s RValue e t) /\

  (!s e bt n. expr_type s LValue e (Array bt n)
                 ==>
              expr_type s RValue e (Ptr bt)) /\

  (!s n. expr_type s RValue (Cnum n) (Signed Int)) /\

  (!s c. expr_type s RValue (Cchar c) BChar) /\

  (!s ty.
       (s.this_type = SOME ty)
  ==>
       expr_type s RValue This (Ptr ty)) /\

  (!si t.
      wf_type si.abs_classes t ==>
      expr_type si RValue (Cnullptr t) (Ptr t)) /\

  (!s n ty.
      (lookup_type s n = SOME ty) /\
      wf_type s.abs_classes ty /\
      ~(ty = Void)
    ==>
      expr_type s LValue (Var n) ty) /\

  (!si n t t' p.
      wf_type si.abs_classes t /\ ~(t = Void) /\
      (t' = if p = [] then t else Class (LAST p))
         ==>
      expr_type si LValue (LVal n t p) t') /\

  (!si v t.
      wf_type si.abs_classes t /\ ~array_type t
         ==>
      expr_type si RValue (ECompVal v t) t) /\

  (!s e t.  expr_type s RValue e t
              ==>
            expr_type s RValue (RValreq e) t) /\

  (!si e t t0.
      wf_type si.abs_classes t /\ (scalar_type t \/ (t = Void)) /\
      expr_type si RValue e t0
          ==>
      expr_type si RValue (Cast t e) t) /\

  (!env v t. expr_type env v UndefinedExpr t) /\

  (* BAD_ASSUMPTION: should check that types of arguments are assignment-
     compatible with argument-types of function *)
  (!s e1 e2 rt args.
       expr_type s RValue e1  (Function rt args) /\
       listRel (expr_type s RValue) e2 args
          ==>
       expr_type s RValue (FnApp e1 e2) rt) /\

  (!s e1 e2 rt.
       expr_type s RValue (FnApp e1 e2) rt
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

  (!s e1 gty e2 t2 e3 t3 restype.
       expr_type s RValue e1 gty /\
       expr_type s RValue e2 t2  /\
       expr_type s RValue e3 t3  /\
       cond_typing_conds (gty, t2, t3, restype)
         ==>
       expr_type s RValue  (CCond e1 e2 e3) restype) /\

  (!s e1 lhs_t e2 rhs_t f.
       expr_type s LValue e1 lhs_t /\
       expr_type s RValue e2 rhs_t /\
       ass_type_conds (f, lhs_t, rhs_t) ==>
       expr_type s RValue (Assign f e1 e2) lhs_t) /\

  (!s e t. expr_type s RValue e (Ptr t) /\ ~(t = Void) ==>
           expr_type s LValue (Deref e) t) /\

  (!s e t. expr_type s LValue e t ==>
           expr_type s RValue (Addr e) (Ptr t)) /\

  (!s e c1 c2 fldid ty.
       expr_type s LValue e (Class c1) /\
       s |- c2 <= c1 /\
       (class_part fldid = c2) /\
       (lookup_field_type s fldid = SOME ty)
     ==>
       expr_type s LValue (SVar e fldid) ty) /\

  (!s e c1 c2 fldid ty.
       expr_type s RValue e (Class c1) /\
       s |- c2 <= c1 /\
       (class_part fldid = c2) /\
       (lookup_field_type s fldid = SOME ty) /\
       ~array_type ty
     ==>
       expr_type s RValue (SVar e fldid) ty)

  /\

  (!s e1 e2 t0 t.
       expr_type s RValue e2 t /\
       expr_type s RValue e1 t0 ==>
       expr_type s RValue (CommaSep e1 e2) t)
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
val expr_type_rewrites = save_thm(
  "expr_type_rewrites",
  LIST_CONJ [lvalue_typing, rvalue_typing]);
val expr_typing = save_thm(
  "expr_typing",
  LIST_CONJ (
     map
      (fn t => GEN_ALL (
        (ONCE_REWRITE_CONV [expr_type_cases] THENC SIMP_CONV (srw_ss()) [])
      ``expr_type senv v ^t t``)) e_cases));

val lvalue_rvalue_nonarray = store_thm(
  "lvalue_rvalue_nonarray",
  ``expr_type s LValue e t /\ ~array_type t ==> expr_type s RValue e t``,
  SRW_TAC [][expr_type_rules])
val lvalue_rvalue_array = store_thm(
  "lvalue_rvalue_array",
  ``expr_type s LValue e (Array bt n) ==> expr_type s RValue e (Ptr bt)``,
  PROVE_TAC [expr_type_rules]);

(* SANITY : only one type possible *)
val expr_type_det_lemma = prove(
  ``(!s v e t.
       expr_type s v e t ==>
          has_no_undefineds e ==>
          (!t'. expr_type s v e t' = (t' = t)) /\
          ((v = LValue) ==>
           (!bt n. (t = Array bt n) ==>
                   !t'. expr_type s RValue e t' = (t' = Ptr bt)) /\
           (~array_type t ==> !t'. expr_type s RValue e t' = (t' = t))))``,
  HO_MATCH_MP_TAC expr_type_ind THEN
  SRW_TAC [ETA_ss][lvalue_typing] THEN
  ASM_SIMP_TAC (srw_ss()) [expr_type_rewrites] THEN
  FULL_SIMP_TAC (srw_ss()) [wf_type_def] THEN
  TRY (METIS_TAC [array_type_def, wf_type_def, unary_op_type_det,
                  binary_op_type_det, cond_typing_conds_det,
                  nodups_lfi_det, TypeBase.one_one_of ``:CPP_Type``,
                  lvalue_rvalue_nonarray]) THEN
  SRW_TAC [][EQ_IMP_THM] THEN
  REPEAT (POP_ASSUM (fn th => if free_in ``e2:CExpr list`` (concl th) then
                                MP_TAC th
                              else ALL_TAC)) THEN
  Q.ID_SPEC_TAC `args` THEN Induct_on `e2` THEN
  SRW_TAC [][listTheory.listRel_CONS]);
val expr_type_det0 = save_thm(
  "expr_type_det0",
  SIMP_RULE (srw_ss() ++ DNF_ss) [] expr_type_det_lemma);
val expr_type_det = store_thm(
  "expr_type_det",
  ``!e v s t1 t2.
      expr_type s v e t1 /\ expr_type s v e t2 /\ has_no_undefineds e ==>
      (t1 = t2)``,
  METIS_TAC [expr_type_det0])

val MEM_splits = prove(
  ``!l. MEM e l ==> ?pfx sfx. (l = pfx ++ (e :: sfx))``,
  Induct THEN SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`[]`, `l`] THEN SRW_TAC [][],
    RES_TAC THEN MAP_EVERY Q.EXISTS_TAC [`h::pfx`, `sfx`] THEN
    SRW_TAC [][]
  ]);

(* SANITY *)
val hasfld_imp_lfi = store_thm(
  "hasfld_imp_lfi",
  ``s |- C has least fld -: (ftype,stat) via p' /\ object_type ftype ==>
    ?i. lookup_field_info
          (MAP (\ (n,ty). (SFName n, ty))
               (THE (nsdmembers s (LAST p'))))
          fld
          (i,ftype)``,
  SRW_TAC [][fieldty_via_def, FieldDecls_def, nsdmembers_def] THEN
  Cases_on `centry` THEN
  FULL_SIMP_TAC (srw_ss()) [fieldtype_def, typesTheory.object_type_def,
                            okfield_def] THEN
  IMP_RES_TAC MEM_splits THEN
  SRW_TAC [][fieldname_def] THEN
  Q.HO_MATCH_ABBREV_TAC
    `?i. lookup_field_info (L1 ++ (X,Y) :: L2) X (i,Y)` THEN
  SRW_TAC [][lookup_field_info_def] THEN
  Q.EXISTS_TAC `LENGTH L1` THEN
  SRW_TAC [ARITH_ss][rich_listTheory.EL_APPEND2])


val _ = export_theory();



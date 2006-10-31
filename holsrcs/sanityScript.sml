(* Sanity theorems for the C++ semantics *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open dynamicsTheory
local open side_effectsTheory statesTheory operatorsTheory in end

val _ = new_theory "sanity";

(* ----------------------------------------------------------------------
    function info remains invariant

    The meaning relation doesn't update the function map, only the
    emeaning relation does.

   ---------------------------------------------------------------------- *)

open side_effectsTheory
val val2mem_fnmap = store_thm(
  "val2mem_fnmap",
  ``(val2mem s a v).fnmap = s.fnmap``,
  SRW_TAC [][statesTheory.val2mem_def]);
val _ = export_rewrites ["val2mem_fnmap"]
val apply_se_preserves_fnmaps = prove(
  ``apply_se (se0,s0) (se,s) ==> (s0.fnmap = s.fnmap)``,
    SRW_TAC [][apply_se_def, apply_lse_def] THEN
    Cases_on `ise` THEN
    FULL_SIMP_TAC (srw_ss()) [se_on_state_def])

val rec_i_params_preserves_fnmaps = prove(
  ``!s0 vars s. rec_i_params s0 prms vars s ==> (s0.fnmap = s.fnmap)``,
  Induct_on `prms` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, rec_i_params_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [])

val pass_parameters_preserves_fnmaps = prove(
  ``pass_parameters s0 fnid params s ==> (s0.fnmap = s.fnmap)``,
  SRW_TAC [][pass_parameters_def] THEN
  IMP_RES_TAC rec_i_params_preserves_fnmaps THEN
  FULL_SIMP_TAC (srw_ss()) [])

val vdeclare_preserves_fnmaps = prove(
  ``vdeclare s0 ty name s ==> (s0.fnmap = s.fnmap)``,
  SRW_TAC [][vdeclare_def] THEN SRW_TAC [][]);

val declmng_preserves_fnmaps = prove(
  ``(!ee0 s0 see. mng ee0 s0 see ==> (s0.fnmap = (FST see).fnmap)) /\
    (!s. (vdf s).fnmap = s.fnmap) ==>
    !d0s0 ds. declmng mng vdf d0s0 ds ==>
              ((SND d0s0).fnmap = (SND ds).fnmap)``,
  STRIP_TAC THEN HO_MATCH_MP_TAC declmng_ind THEN
  SRW_TAC [][] THEN
  TRY (METIS_TAC [lval2rval_states_equal, apply_se_preserves_fnmaps,
                  vdeclare_preserves_fnmaps]) THEN
  RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []);

val declmng_elim_preserves_fnmaps = prove(
  ``declmng mng vdf d0s0 ds ==>
    (!ee0 s0 see. mng ee0 s0 see ==> (s0.fnmap = (FST see).fnmap)) ==>
    (!s. (vdf s).fnmap = s.fnmap) ==>
    ((SND d0s0).fnmap = (SND ds).fnmap)``,
  METIS_TAC [declmng_preserves_fnmaps]);

(* final result *)
val fninfo_invariant = store_thm(
  "fninfo_invariant",
  ``!ee0 s0 see. meaning ee0 s0 see ==> (s0.fnmap = (FST see).fnmap)``,
  HO_MATCH_MP_TAC meaning_ind THEN SRW_TAC [][] THEN
  TRY (METIS_TAC [lval2rval_states_equal, apply_se_preserves_fnmaps]) THEN
  TRY (IMP_RES_TAC pass_parameters_preserves_fnmaps THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN NO_TAC) THEN
  IMP_RES_TAC declmng_elim_preserves_fnmaps THEN
  FULL_SIMP_TAC (srw_ss()) []);

(* ----------------------------------------------------------------------
    class_lvalue_safe
       If a class lvalue occurs, its type (Class cname) will have the same
       cname as the last element of the accompanying path
   ---------------------------------------------------------------------- *)

val clval_safe_def = Define`
  (clval_safe (LVal a (Class c) p) = ~(p = []) /\ (c = LAST p)) /\
  (clval_safe e = T)
`
val _ = export_rewrites ["clval_safe_def"]

val clvalue_safe_def = Define`
  clvalue_safe e = rec_expr_P e clval_safe
`;
val _ = export_rewrites ["clvalue_safe_def"]

(* this proof can't work until I come up with a way of describing memory
   as being "safe" with respect to a program, meaning that any pointers
   read out of memory and pointing to a class satisfy the safety property -
   I suspect this may need to be axiomatised into the ptr_decode function,
   such that if ptr_decode returns SOME (addr,p) then it's OK.  If it's NONE
   then that means the pointer is bad, and the result is undefined behaviour *)

(*
val clvalue_safe_invariant = store_thm(
  "clvalue_safe_invariant",
  ``!e s sse. meaning e s sse ==>
              erec_exte clvalue_safe e ==>
              erec_exte clvalue_safe (SND sse)``,
  HO_MATCH_MP_TAC meaning_ind THEN
  SRW_TAC [][statementsTheory.erec_stmt_def,
             expressionsTheory.rec_expr_P_def]  THEN
  SRW_TAC [][expressionsTheory.rec_expr_P_def] THENL [
    Cases_on `s.typemap ' vname` THEN
    SRW_TAC [][statesTheory.default_path_def],

    FULL_SIMP_TAC (srw_ss()) [valid_econtext_def] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [expressionsTheory.rec_expr_P_def],

    FULL_SIMP_TAC (srw_ss()) [valid_econtext_def] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [expressionsTheory.rec_expr_P_def],

    FULL_SIMP_TAC (srw_ss()) [valid_lvcontext_def] THEN
    SRW_TAC [][] THEN
    IMP_RES_TAC lval2rval_results THEN
    FULL_SIMP_TAC (srw_ss()) [expressionsTheory.rec_expr_P_def],

    SRW_TAC [][expressionsTheory.rec_expr_P_def],
    SRW_TAC [][expressionsTheory.rec_expr_P_def],
    SRW_TAC [][expressionsTheory.rec_expr_P_def],


    FULL_SIMP_TAC (srw_ss()) [expressionsTheory.rec_expr_P_def],

*)



val _ = export_theory();



(* Sanity theorems for the C++ semantics *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open dynamicsTheory declaration_dynamicsTheory
local open side_effectsTheory statesTheory operatorsTheory in end

val _ = new_theory "sanity";

(* ----------------------------------------------------------------------
    statement to statement evaluations preserve continuations
   ---------------------------------------------------------------------- *)

open statementsTheory
val is_exnval_lemma = prove(
  ``is_exnval e /\ (mk_exn e c = ST s c') ==> (c' = c)``,
  Cases_on `e` THEN SIMP_TAC (srw_ss()) [is_exnval_def] THEN
  Cases_on `C'` THEN SIMP_TAC (srw_ss()) [is_exnval_def] THEN
  Cases_on `o'` THEN SIMP_TAC (srw_ss()) [is_exnval_def] THEN
  SRW_TAC [][mk_exn_def]);

val stmt_preserve_continuations = store_thm(
  "stmt_preserve_continuations",
  ``!ee s0 see. meaning ee s0 see ==>
                !c1 c2 st1 st2 s.
                    (ee = ST st1 c1) /\
                    (see = (s, ST st2 c2)) ==>
                    (c2 = c1)``,
  HO_MATCH_MP_TAC mng_ind THEN SRW_TAC [][] THEN
  METIS_TAC [is_exnval_lemma]);


val _ = export_theory();



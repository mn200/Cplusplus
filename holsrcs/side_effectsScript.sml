(* Side effects *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* additional ancestor, that should possibly be a standard part of HOL *)
open function_slicesTheory

(* additionally, we need to pull in the theory of bags *)
open bagTheory

(* C++ ancestor theories  *)
open typesTheory memoryTheory expressionsTheory statementsTheory statesTheory

val _ = new_theory "side_effects";

val _ = type_abbrev("se", ``:num # byte list``)

val _ = Hol_datatype `se_info = <| pending_ses : se->num ;
                                   update_map  : num->bool ;
                                   ref_map     : num->num |>`;

val se_info_component_equality = theorem "se_info_component_equality"
val _ = overload_on ("update_map", ``se_info_update_map``)
val _ = overload_on ("ref_map", ``se_info_ref_map``)
val _ = overload_on ("pending_ses", ``se_info_pending_ses``)

val base_se_def = Define`
  base_se = <| pending_ses := {| |}; update_map := {};
               ref_map := {| |}
            |>
`;

val is_null_se_def = Define`
  is_null_se se = (se.pending_ses = EMPTY_BAG)
`;

val add_se = Define`
  add_se ise se = se with pending_ses updated_by (BAG_INSERT ise)
`;

val se_affects_def = Define`
  se_affects ((n,v):se) = range_set n (LENGTH v)
`;

val null_ise_def = Define`
  null_ise ise = (se_affects ise = EMPTY)
`;

val null_ise_THM = store_thm(
  "null_ise_THM",
  ``!ise. null_ise ise = (SND ise = [])``,
  Cases_on `ise` THEN
  SRW_TAC [][null_ise_def, se_affects_def, range_set, FUN_EQ_THM,
             EMPTY_DEF, EQ_IMP_THM]
  THENL [
    Cases_on `r` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN POP_ASSUM MP_TAC THEN
    intLib.ARITH_TAC,
    DECIDE_TAC
  ]);
val se_on_state_def = Define`
  se_on_state ((n,v):se) s =
      val2mem s n v with initmap updated_by ($UNION (se_affects (n,v)))
`

val select_se_def = Define`
  select_se ise (se0:se_info) se =
        ?nvl. BAG_DELETE se0.pending_ses ise nvl /\
              (se = se0 with pending_ses := nvl)
`

val apply_ise_def = Define`
  apply_ise ise (se0:se_info) se =
      ?u. (u = se_affects ise) /\ DISJOINT (update_map se0) u /\
          DISJOINT (SET_OF_BAG (ref_map se0)) u /\
          (se = update_map_fupd ($UNION u) se0)
`;

val apply_lse_def = Define`
  apply_lse (se0, s0) (se, s) ise =
        ?se'. select_se ise se0 se' /\ apply_ise ise se' se /\
              se_affects ise SUBSET s0.allocmap /\
              (s = se_on_state ise s0)
`

val apply_se_def = Define`
  apply_se sse0 sse = ?ise. apply_lse sse0 sse ise
`

val apply_se = store_thm (
  "apply_se",
  ``apply_se (se0, s0) (se, s) =
        ?ise se'. select_se ise se0 se' /\ apply_ise ise se' se /\
                  se_affects ise SUBSET s0.allocmap /\
                  (s = se_on_state ise s0)``,
  REWRITE_TAC [apply_se_def, apply_lse_def]);

val apply_lse_se = store_thm(
  "apply_lse_se",
  ``!sse0 sse ise. apply_lse sse0 sse ise ==> apply_se sse0 sse``,
  METIS_TAC [apply_se_def])

val _ = export_theory()
(* there used to follow a whole bunch of theorems that were used to establish
   that apply_se was confluent - can recover these from C source files
   if necessary *)

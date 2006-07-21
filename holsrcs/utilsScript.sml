(* Logical utilities - candidates for inclusion in HOL *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

val _ = new_theory "utils"

val deNONE_def = Define`
  deNONE f = THE o_f DRESTRICT f {k | ~(f ' k = NONE)}
`;

open finite_mapTheory
val deNONE = store_thm(
  "deNONE",
  ``k IN FDOM f /\ ~(f ' k = NONE) ==> (deNONE f ' k = THE (f ' k))``,
  SRW_TAC [][DRESTRICT_DEF, deNONE_def,
             o_f_DEF])

val deNONE_FEMPTY = store_thm(
  "deNONE_FEMPTY",
  ``deNONE FEMPTY = FEMPTY``,
  SRW_TAC [][deNONE_def]);
val _ = export_rewrites ["deNONE_FEMPTY"]

val deNONE_FUPDATE = store_thm(
  "deNONE_FUPDATE",
  ``(deNONE (fm |+ (k, SOME v)) = deNONE fm |+ (k,v)) /\
    (deNONE (fm |+ (k, NONE)) = deNONE (fm \\ k))``,
  SRW_TAC [][deNONE_def] THEN
  SRW_TAC [][fmap_EXT, FDOM_DRESTRICT, FAPPLY_FUPDATE_THM] THENL [
    SRW_TAC [boolSimps.CONJ_ss][pred_setTheory.EXTENSION] THEN
    Cases_on `x = k` THEN SRW_TAC [][],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    ASM_SIMP_TAC (srw_ss()) [o_f_FAPPLY, FDOM_DRESTRICT] THEN
    ASM_SIMP_TAC (srw_ss()) [DOMSUB_FAPPLY_THM] THEN
    ASM_SIMP_TAC (srw_ss()) [DRESTRICT_DEF],
    SRW_TAC [][pred_setTheory.EXTENSION] THEN
    Cases_on `x = k` THEN SRW_TAC [][DOMSUB_FAPPLY_THM],
    Cases_on `x = k` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    ASM_SIMP_TAC (srw_ss()) [o_f_FAPPLY, FDOM_DRESTRICT, DOMSUB_FAPPLY_THM] THEN
    ASM_SIMP_TAC (srw_ss()) [DRESTRICT_DEF, DOMSUB_FAPPLY_THM]
  ])
val _ = export_rewrites ["deNONE_FUPDATE"]

val mapPartial_def = Define`
  (mapPartial f [] = []) /\
  (mapPartial f (h::t) = case f h of SOME x -> x :: mapPartial f t
                                  || NONE -> mapPartial f t)
`
val _ = export_rewrites ["mapPartial_def"]




val _ = export_theory()


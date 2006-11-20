(* Logical utilities - candidates for inclusion in HOL *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

val _ = new_theory "utils"

(* ----------------------------------------------------------------------
    deNONE : ('a |-> 'b option) -> ('a |-> 'b)
   ---------------------------------------------------------------------- *)

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

val FDOM_deNONE_SUBSET = store_thm(
  "FDOM_deNONE_SUBSET",
  ``!f. x IN FDOM (deNONE f) ==> x IN FDOM f``,
  HO_MATCH_MP_TAC fmap_INDUCT THEN SRW_TAC [][] THEN
  Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [DOMSUB_NOT_IN_DOM]);

(* ----------------------------------------------------------------------
    mapPartial : ('a -> 'b option) -> 'a list -> 'b list
   ---------------------------------------------------------------------- *)

val mapPartial_def = Define`
  (mapPartial f [] = []) /\
  (mapPartial f (h::t) = case f h of SOME x -> x :: mapPartial f t
                                  || NONE -> mapPartial f t)
`
val _ = export_rewrites ["mapPartial_def"]

val mapPartial_APPEND = store_thm(
  "mapPartial_APPEND",
  ``!l1 l2. mapPartial f (l1 ++ l2) = mapPartial f l1 ++ mapPartial f l2``,
  Induct THEN SRW_TAC [][] THEN Cases_on `f h` THEN SRW_TAC [][]);
val _ = export_rewrites ["mapPartial_APPEND"]


(* ----------------------------------------------------------------------
    EVERYi : (num -> 'a -> bool) -> 'a list -> bool

    checks that every element of a list satisfies a predicate, but where
    the predicate also gets access to the element's position in the list

    For example,

     - EVAL ``EVERYi (\i n. n = i * i) [0;1;4;9;x]``;
     > val it = |- EVERYi (\i n. n = i * i) [0; 1; 4; 9; x] = (x = 16) : thm

   ---------------------------------------------------------------------- *)

val EVERYi_def = Define`
  (EVERYi P [] = T) /\
  (EVERYi P (h::t) = P 0 h /\ EVERYi (P o SUC) t)
`;
val _ = export_rewrites ["EVERYi_def"]

(* ----------------------------------------------------------------------
    FINDL : ('a -> bool) -> 'a list -> 'a option
   ---------------------------------------------------------------------- *)

val FINDL_def = Define`
  (FINDL P [] = NONE) /\
  (FINDL P (h :: t) = if P h then SOME h else FINDL P t)
`;



val _ = export_theory()


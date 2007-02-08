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

val mapPartial_MAP = store_thm(
  "mapPartial_MAP",
  ``mapPartial f (MAP g l) = mapPartial (f o g) l``,
  Induct_on `l` THEN SRW_TAC [][]);

val MAP_mapPartial = store_thm(
  "MAP_mapPartial",
  ``MAP f (mapPartial g l) = mapPartial (OPTION_MAP f o g) l``,
  Induct_on `l` THEN SRW_TAC [][] THEN Cases_on `g h` THEN SRW_TAC [][]);

val mapPartial_mapPartial = store_thm(
  "mapPartial_mapPartial",
  ``mapPartial f (mapPartial g l) = mapPartial (option_case NONE f o g) l``,
  Induct_on `l` THEN SRW_TAC [][] THEN Cases_on `g h` THEN
  SRW_TAC [][])

val mapPartial_K_NONE = store_thm(
 "mapPartial_K_NONE",
  ``mapPartial (\x. NONE) l = []``,
  Induct_on `l` THEN SRW_TAC [][]);
val _ = export_rewrites ["mapPartial_K_NONE"]

val mapPartial_SOME = store_thm(
  "mapPartial_SOME",
  ``mapPartial SOME l = l``,
  Induct_on `l` THEN SRW_TAC [][])
val _ = export_rewrites ["mapPartial_SOME"]

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

(* ----------------------------------------------------------------------
    NUMBER : num -> 'a list -> (num # 'a) list
   ---------------------------------------------------------------------- *)

val NUMBER_def = Define`
  (NUMBER (n:num) [] = []) /\
  (NUMBER n (h::t) = (n,h) :: NUMBER (n + 1) t)
`
val _ = export_rewrites ["NUMBER_def"]

val LENGTH_NUMBER = store_thm(
  "LENGTH_NUMBER",
  ``!n. LENGTH (NUMBER n l) = LENGTH l``,
  Induct_on `l` THEN SRW_TAC [][])
val _ = export_rewrites ["LENGTH_NUMBER"]

val NUMBER_MAP = store_thm(
  "NUMBER_MAP",
  ``!n. NUMBER n (MAP f l) = MAP (I ## f) (NUMBER n l)``,
  Induct_on `l` THEN SRW_TAC [][]);

(* ----------------------------------------------------------------------
    LFINDi : ('a -> bool) -> 'a list -> num option
   ---------------------------------------------------------------------- *)

val LFINDi_def = Define`
  (LFINDi P [] = NONE) /\
  (LFINDi P (h::t) = if P h then SOME 0n
                     else case LFINDi P t of
                             NONE -> NONE
                          || SOME i -> SOME (i + 1))
`
val _ = export_rewrites ["LFINDi_def"]

val LFINDi_THM = store_thm(
  "LFINDi_THM",
  ``(!i. (LFINDi P l = SOME i) ==>
            i < LENGTH l /\ P (EL i l) /\ !j. j < i ==> ~P(EL j l)) /\
    ((LFINDi P l = NONE) ==>
       !i. i < LENGTH l ==> ~P (EL i l))``,
  Induct_on `l` THEN SRW_TAC [][listTheory.EL] THEN
  SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [],
    Cases_on `LFINDi P l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN DECIDE_TAC,
    Cases_on `LFINDi P l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN SRW_TAC [][GSYM ADD1],
    Cases_on `LFINDi P l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `j` THEN SRW_TAC [ARITH_ss][],
    Cases_on `LFINDi P l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `i` THEN SRW_TAC [ARITH_ss][]
  ]);

(* ----------------------------------------------------------------------
    stackenv_extend : 'a -> 'a list list -> 'a list list
   ---------------------------------------------------------------------- *)

val stackenv_extend_def = Define`
  (stackenv_extend a [] = [[a]]) /\
  (stackenv_extend a (h::t) = (a::h) :: t)
`;
val _ = export_rewrites ["stackenv_extend_def"]

val stackenv_extendl_def = Define`
  (stackenv_extendl l [] = [l]) /\
  (stackenv_extendl l (h :: t) = (l ++ h) :: t)
`;
val _ = export_rewrites ["stackenv_extendl_def"]

(* ----------------------------------------------------------------------
    stackenv_newscope : 'a list list -> 'a list list
   ---------------------------------------------------------------------- *)

val stackenv_newscope_def = Define`
  stackenv_newscope env = []::env
`;




val _ = export_theory()


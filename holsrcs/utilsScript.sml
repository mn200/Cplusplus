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
val _ = export_rewrites ["FINDL_def"]

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

val hd_update_def = Define`
  (hd_update f [] = []) /\
  (hd_update f (h::t) = f h :: t)
`;

(* ----------------------------------------------------------------------
    stackenv_newscope : 'a list list -> 'a list list
   ---------------------------------------------------------------------- *)

val stackenv_newscope_def = Define`
  stackenv_newscope env = []::env
`;


(* ----------------------------------------------------------------------
    olmap : ('a -> 'b option) -> 'a list -> 'b list option
   ---------------------------------------------------------------------- *)

val olmap_def = Define`
  (olmap f [] = SOME []) /\
  (olmap f (h::t) =
     case f h of
        NONE -> NONE
     || SOME h -> OPTION_MAP (CONS h) (olmap f t))
`;
val _ = export_rewrites ["olmap_def"]

val olmap_CONG = store_thm(
  "olmap_CONG",
  ``!l1 l2 f1 f2.
      (l1 = l2) /\ (!x. MEM x l2 ==> (f1 x = f2 x)) ==>
      (olmap f1 l1 = olmap f2 l2)``,
  Induct THEN SRW_TAC [][] THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM] THEN
  RES_TAC THEN SRW_TAC [][]);

val _ = DefnBase.export_cong "olmap_CONG"

val option_case_EQ_SOME = store_thm(
  "option_case_EQ_SOME",
  ``(option_case NONE f v = SOME v0) =
        ?v0'. (v = SOME v0') /\ (f v0' = SOME v0)``,
  Cases_on `v` THEN SRW_TAC [][]);
val _ = export_rewrites ["option_case_EQ_SOME"]

val olmap_ALL_MEM = store_thm(
  "olmap_ALL_MEM",
  ``!list x f.
        (olmap f list = SOME x) =
          (LENGTH x = LENGTH list) /\
          !i. i < LENGTH list ==>
              (f (EL i list) = SOME (EL i x))``,
  Induct_on `list` THEN SRW_TAC [][] THENL [
    SRW_TAC [][listTheory.LENGTH_NIL] THEN METIS_TAC [],
    Cases_on `x` THEN SRW_TAC [][] THEN
    SRW_TAC [][EQ_IMP_THM] THENL [
      Cases_on `i` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [],
      FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][],
      FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` MP_TAC) THEN SRW_TAC [][]
    ]
  ]);

val olmap_EQ_NONE = store_thm(
  "olmap_EQ_NONE",
  ``(olmap f list = NONE) = ?e. MEM e list /\ (f e = NONE)``,
  Induct_on `list` THEN SRW_TAC [][] THEN Cases_on `f h` THEN
  SRW_TAC [][] THEN METIS_TAC [TypeBase.distinct_of ``:'a option``]);

val olmap_EQ_SOME = store_thm(
  "olmap_EQ_SOME",
  ``((olmap f list = SOME []) = (list = [])) /\
    ((SOME [] = olmap f list) = (list = [])) /\
    ((olmap f list = SOME (h::t)) =
        ?h0 t0. (f h0 = SOME h) /\ (list = h0::t0) /\ (olmap f t0 = SOME t))``,
  Cases_on `list` THEN SRW_TAC [][]);

val olmap_APPEND = store_thm(
  "olmap_APPEND",
  ``olmap f (l1 ++ l2) =
      case olmap f l1 of
         NONE -> NONE
      || SOME l1' -> case olmap f l2 of
                        NONE -> NONE
                     || SOME l2' -> SOME (l1' ++ l2')``,
  Q.ID_SPEC_TAC `l2` THEN Induct_on`l1` THEN SRW_TAC [][] THENL [
    Cases_on `olmap f l2` THEN SRW_TAC [][],
    Cases_on `f h` THEN SRW_TAC [][] THEN
    Cases_on `olmap f l1` THEN SRW_TAC [][] THEN
    Cases_on `olmap f l2` THEN SRW_TAC [][]
  ]);

(* ----------------------------------------------------------------------
    OP2CMB : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option
   ---------------------------------------------------------------------- *)
val OP2CMB_def = Define`
  (OP2CMB f (SOME x) (SOME y) = SOME (f x y)) /\
  (OP2CMB f _ _ = NONE)
`;
val _ = export_rewrites ["OP2CMB_def"]

val OP2CMB_CONG = store_thm(
  "OP2CMB_CONG",
  ``!x1 x2 y1 y2 f1 f2.
       (x1 = x2) /\ (y1 = y2) /\
       (!x y. (x2 = SOME x) /\ (y2 = SOME y) ==> (f1 x y = f2 x y)) ==>
       (OP2CMB f1 x1 y1 = OP2CMB f2 x2 y2)``,
  SRW_TAC [][] THEN Cases_on `x1` THEN Cases_on `y1` THEN
  SRW_TAC [][]);
val _ = DefnBase.export_cong "OP2CMB_CONG"

val OP2CMB_NONE2 = store_thm(
  "OP2CMB_NONE2",
  ``(OP2CMB f x NONE = NONE)``,
  Cases_on `x` THEN SRW_TAC [][]);
val _ = export_rewrites ["OP2CMB_NONE2"]

val OP2CMB_EQ_SOME_E = store_thm(
  "OP2CMB_EQ_SOME_E",
  ``(OP2CMB f x y = SOME v) ==> ?x0 y0. (v = f x0 y0) /\ (x = SOME x0) /\
                                        (y = SOME y0)``,
  MAP_EVERY Cases_on [`x`,`y`] THEN SRW_TAC [][]);

val INJECTIVE_OP2CMB_EQ_SOME_I = store_thm(
  "INJECTIVE_OP2CMB_EQ_SOME_I",
  ``(!x1 y1 x2 y2. (f x1 y1 = f x2 y2) = (x1 = x2) /\ (y1 = y2)) ==>
    ((OP2CMB f x y = SOME v) =
       ?x0 y0. (v = f x0 y0) /\ (x = SOME x0) /\ (y = SOME y0))``,
  STRIP_TAC THEN MAP_EVERY Cases_on [`x`,`y`] THEN SRW_TAC [][] THEN
  METIS_TAC []);
val _ = export_rewrites ["INJECTIVE_OP2CMB_EQ_SOME_I"]

(* ----------------------------------------------------------------------
    optimage : ('a -> 'b option) -> 'a set -> ('b set, 'a set)
   ---------------------------------------------------------------------- *)

val optimage_def = Define`
  optimage (f : 'a -> 'b option) (s : 'a set) =
     ({ b | ?a. a IN s /\ (SOME b = f a) },
      { a | f a = NONE })
`;

val optimage_image = store_thm(
  "optimage_image",
  ``optimage f s = (IMAGE THE (IMAGE f s DELETE NONE),
                    { a | f a = NONE })``,
  SRW_TAC [DNF_ss][optimage_def, EXTENSION, EQ_IMP_THM] THENL [
    Q.EXISTS_TAC `a` THEN POP_ASSUM (fn th => SRW_TAC [][SYM th]),
    Q.EXISTS_TAC `x''` THEN Cases_on `f x''` THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

(* ----------------------------------------------------------------------
    THEOPT : ('a -> bool) -> 'a option
   ---------------------------------------------------------------------- *)

val THEOPT_def = Define`
  (THEOPT) P = if (?)P then SOME ((@)P) else NONE
`
val _ = add_binder("THEOPT", 0)

val THEOPT_I = store_thm(
  "THEOPT_I",
  ``P x ==> P (THE ((THEOPT) P))``,
  `P = (\x. P x)` by SRW_TAC [][FUN_EQ_THM] THEN
  POP_ASSUM SUBST_ALL_TAC THEN SRW_TAC [][THEOPT_def] THENL [
    SELECT_ELIM_TAC THEN METIS_TAC [],
    METIS_TAC []
  ]);

val THEOPT_EQ_NONE = store_thm(
  "THEOPT_EQ_NONE",
  ``(!x. ~P x) ==> ((THEOPT x. P x) = NONE)``,
  SRW_TAC [][THEOPT_def]);

(* ----------------------------------------------------------------------
    SETFN_APPLY
   ---------------------------------------------------------------------- *)

val SETFN_APPLY_def = Define`
  SETFN_APPLY s x = @y. (x,y) IN s
`;
val _ = overload_on ("'", ``SETFN_APPLY``)

val SETFN_UNIQUE = store_thm(
  "SETFN_UNIQUE",
  ``(x,y) IN s /\ (!y'. (x,y') IN s ==> (y' = y)) ==> (s ' x = y)``,
  SRW_TAC [][SETFN_APPLY_def] THEN SELECT_ELIM_TAC THEN METIS_TAC []);

val _ = export_theory()


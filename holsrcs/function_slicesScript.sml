(* \#line miscellanea.nw 1462 *)
open HolKernel boolLib Parse mnUtils
infix THEN THENL THENC >- ++

val _ = new_theory "function_slices";
open pred_setTheory simpLib
val hol_ss         = bossLib.list_ss ++ rich_listSimps.RICH_LIST_ss
val GENLIST        = rich_listTheory.GENLIST
val LENGTH_SNOC    = rich_listTheory.LENGTH_SNOC
val LENGTH_LASTN   = rich_listTheory.LENGTH_LASTN
val LENGTH_GENLIST = rich_listTheory.LENGTH_GENLIST
(* \#line miscellanea.nw 1482 *)
val slice_upd = new_definition (
  "slice_upd",
  ``slice_upd lmp loc v x =
      (if loc <= x /\ x < loc + LENGTH v then EL (x - loc) v else lmp x)``)
val pull_slice = new_definition (
  "pull_slice",
  ``pull_slice lmp loc sz = GENLIST (\n. lmp (loc + n)) sz``);
val range_set = new_definition(
  "range_set",
  (--`range_set n s = \x. n <= x /\ x < n + s`--));
(* \#line miscellanea.nw 1499 *)
val pull_slice_0 = store_thm(
  "pull_slice_0",
  ``!lmp a. pull_slice lmp a 0 = []``,
  SIMP_TAC hol_ss [pull_slice, GENLIST]);
val slice_upd_NIL = store_thm(
  "slice_upd_NIL",
  ``!lmp a. slice_upd lmp a [] = lmp``,
  REPEAT GEN_TAC THEN FUN_EQ_TAC THEN
  SIMP_TAC hol_ss [slice_upd]);
val len_pull_slice = store_thm(
  "len_pull_slice",
  ``!lmp a n. LENGTH (pull_slice lmp a n) = n``,
  SIMP_TAC hol_ss [pull_slice, LENGTH_GENLIST])

val snoc_firstn = store_thm(
  "snoc_firstn",
  ``!l n. n < LENGTH l ==>
          (SNOC (EL n l) (FIRSTN n l) = FIRSTN (n + 1) l)``,
  INDUCT_THEN rich_listTheory.SNOC_INDUCT STRIP_ASSUME_TAC THEN
  SIMP_TAC hol_ss [LENGTH_SNOC, rich_listTheory.FIRSTN_SNOC,
                   arithmeticTheory.ADD1] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC ``n = LENGTH l`` THENL [
    ELIM_TAC THEN SIMP_TAC hol_ss [rich_listTheory.EL_LENGTH_SNOC,
      rich_listTheory.FIRSTN_LENGTH_ID,
      (ISPEC ``SNOC a l`` >-
       SIMP_RULE hol_ss [LENGTH_SNOC, arithmeticTheory.ADD1])
        rich_listTheory.FIRSTN_LENGTH_ID,
      rich_listTheory.FIRSTN_SNOC],
    SUBGOAL_THEN ``n < LENGTH l`` ASSUME_TAC THENL [
      ASM_SIMP_TAC hol_ss [],
      ALL_TAC
    ] THEN
    FULL_SIMP_TAC hol_ss [rich_listTheory.EL_SNOC, rich_listTheory.FIRSTN_SNOC]
  ]);

val ADD1 = arithmeticTheory.ADD1
val genlist_firstn = store_thm(
  "genlist_firstn",
  ``!n l. n <= LENGTH l ==>
          (GENLIST (\n. EL n l) n = FIRSTN n l)``,
  SingleStep.Induct THEN ASM_SIMP_TAC hol_ss [GENLIST, snoc_firstn, ADD1])

val genlist_id = store_thm(
  "genlist_id",
  ``!l. GENLIST (\n. EL n l) (LENGTH l) = l``,
  SIMP_TAC hol_ss [genlist_firstn, rich_listTheory.FIRSTN_LENGTH_ID])

val pull_upd_inv_lemma = store_thm(
  "pull_upd_inv_lemma",
  ``!n v lmp a.
       (n <= LENGTH v) ==>
       (pull_slice (slice_upd lmp a v) a n = FIRSTN n v)``,
  numLib.INDUCT_TAC THEN
  FULL_SIMP_TAC hol_ss [pull_slice, slice_upd, snoc_firstn, GENLIST, ADD1])
val pull_upd_inverse = save_thm(
  "pull_upd_inverse",
  (SPECL [``n:num``, ``v:'a list``] >-
   INST [``n:num`` |-> ``LENGTH v``]  >-
   SIMP_RULE hol_ss [rich_listTheory.FIRSTN_LENGTH_ID])
  pull_upd_inv_lemma);
val disjoint_range_sets = store_thm(
  "disjoint_range_sets",
  ``!a b n m.
       DISJOINT (range_set a n) (range_set b m) =
       (a + n < b + 1) \/ (b + m < a + 1) \/ (n = 0) \/ (m = 0)``,
  SIMP_TAC hol_ss [range_set, DISJOINT_DEF, EXTENSION, IN_INTER,
                    NOT_IN_EMPTY] THEN
  SIMP_TAC hol_ss [SPECIFICATION] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC hol_ss [] THEN
  myCONTR_TAC THEN FULL_SIMP_TAC hol_ss [] THEN
  MAP_EVERY (fn q =>
              FIRST_ASSUM (Q.SPEC q >- SIMP_RULE hol_ss [] >- ASSUME_TAC))
            [`a`, `b`] THEN
  CLEAR_ASMS is_forall THEN
  FULL_SIMP_TAC hol_ss [ARITH_PROVE ``~(x < x + y) = (y = 0)``]);
val GENLIST_eq = store_thm(
  "GENLIST_eq",
  ``!f1 f2 m1 m2.
       (GENLIST f1 m1 = GENLIST f2 m2) =
       (m1 = m2) /\ (!n. n < m1 ==> (f1 n = f2 n))``,
  rmove_out_TAC ``m1:num`` THEN numLib.INDUCT_TAC THENL [
    SIMP_TAC (hol_ss ++ impnorm_set) [GENLIST, EQ_IMP_THM,
                                      FORALL_AND_THM] THEN
    REPEAT STRIP_TAC THEN
    SingleStep.Cases_on `m2` THEN FULL_SIMP_TAC hol_ss [GENLIST],
    REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      SingleStep.Cases_on `m2` THEN FULL_SIMP_TAC hol_ss [GENLIST] THEN
      ASM_MESON_TAC [],
      SingleStep.Cases_on `m2` THEN FULL_SIMP_TAC hol_ss [GENLIST] THEN
      ASM_CASES_TAC ``n < m1`` THENL [
        ASM_MESON_TAC [],
        SUBGOAL_THEN ``n:num = m1`` SUBST_ALL_TAC THENL [
          ASM_SIMP_TAC hol_ss [],
          ASM_MESON_TAC []
        ]
      ],
      ELIM_TAC THEN ASM_SIMP_TAC hol_ss [GENLIST]
    ]
  ]);
val append_snoc = store_thm(
  "append_snoc",
  ``!l1 l2 h.
       APPEND l1 (CONS h l2) = APPEND (SNOC h l1) l2``,
  SingleStep.Induct THEN ASM_SIMP_TAC hol_ss []);

val GENLIST =
  CONV_RULE (conj2_CONV (swap_vars THENC numLib.SUC_ELIM_CONV)) GENLIST

fun pswith t thms = SUBGOAL_THEN t STRIP_ASSUME_TAC THENL [
  ASM_SIMP_TAC hol_ss thms THEN ASM_MESON_TAC thms,
  ALL_TAC
]

val append_genlist = store_thm(
  "append_genlist",
  ``!l2 l1.
       APPEND l1 l2 =
       GENLIST (\n. if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2)
               (LENGTH l1 + LENGTH l2)``,
  SingleStep.Induct THENL [
    SIMP_TAC hol_ss [] THEN GEN_TAC THEN
    CONV_TAC (lhs_CONV (REWR_CONV (GSYM genlist_id))) THEN
    SIMP_TAC hol_ss [GENLIST_eq],
    ASM_SIMP_TAC hol_ss [GENLIST, append_snoc, ADD1,
                         rich_listTheory.LENGTH_SNOC] THEN
    REPEAT STRIP_TAC THENL [
      SingleStep.Cases_on `LENGTH l2` THENL [
        SIMP_TAC hol_ss [rich_listTheory.EL_LENGTH_SNOC],
        SIMP_TAC hol_ss [ADD1]
      ],
      SIMP_TAC hol_ss [GENLIST_eq] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THENL [
        COND_CASES_TAC THENL [
          ASM_SIMP_TAC hol_ss [rich_listTheory.EL_SNOC],
          SUBGOAL_THEN ``n = LENGTH l1`` SUBST_ALL_TAC THENL [
            ASM_SIMP_TAC hol_ss [],
            SIMP_TAC hol_ss [rich_listTheory.EL_LENGTH_SNOC]
          ]
        ],
        ASM_SIMP_TAC hol_ss [] THEN pswith ``LENGTH l1 < n`` [] THEN
        pswith ``n - LENGTH l1 = SUC (n - (LENGTH l1 + 1))`` [] THEN
        POP_ASSUM SUBST_ALL_TAC THEN SIMP_TAC hol_ss [GENLIST]
      ]
    ]
  ])

val pull_upd = store_thm(
  "pull_upd",
  ``!n v f a1 a2.
      (DISJOINT (range_set a2 n) (range_set a1 (LENGTH v)) ==>
      (pull_slice (slice_upd f a1 v) a2 n = pull_slice f a2 n))``,
  SIMP_TAC hol_ss [disjoint_range_sets, pull_slice, slice_upd] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC hol_ss [GENLIST_eq]);

val pull_slice_fromfront = store_thm(
  "pull_slice_fromfront",
  ``!sz lmp loc.
       pull_slice lmp loc (sz + 1) =
       CONS (lmp loc) (pull_slice lmp (loc + 1) sz)``,
  numLib.INDUCT_TAC THEN FULL_SIMP_TAC hol_ss [pull_slice, GENLIST, ADD1]);
val EL_pull_slice = store_thm(
  "EL_pull_slice",
  ``!f a n m. n < m ==> (EL n (pull_slice f a m) = f (a + n))``,
  SIMP_TAC hol_ss [pull_slice] THEN rmove_out_TAC ``m:num`` THEN
  numLib.INDUCT_TAC THEN SIMP_TAC hol_ss [GENLIST] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC ``n < m`` THENL [
    ASM_SIMP_TAC hol_ss [rich_listTheory.LENGTH_GENLIST,
      rich_listTheory.EL_SNOC],
    SUBGOAL_THEN ``n:num = m`` SUBST_ALL_TAC THENL [
      ASM_SIMP_TAC hol_ss [],
      SUBGOAL_THEN ``m = LENGTH (GENLIST (\n. f (a + n)) m)``
        (fn th => CONV_TAC (lhs_CONV (arg_CONV 1 (REWR_CONV th))) THEN
           SIMP_TAC hol_ss [rich_listTheory.EL_LENGTH_SNOC]) THEN
      SIMP_TAC hol_ss [rich_listTheory.LENGTH_GENLIST]
    ]
  ]);
(* \#line miscellanea.nw 1680 *)
val range_set_EMPTY = store_thm(
  "range_set_EMPTY",
  --`!x. range_set x 0 = EMPTY`--,
  SIMP_TAC hol_ss [range_set, EXTENSION, NOT_IN_EMPTY,
                    SPECIFICATION]);
val range_set_SING = store_thm(
  "range_set_SING",
  --`!x. range_set x 1 = {x}`--,
  SIMP_TAC hol_ss [range_set, EXTENSION, NOT_IN_EMPTY, IN_INSERT,
                    SPECIFICATION]);
val range_set_sum = store_thm(
  "range_set_sum",
  --`!n x y. range_set n (x + y) =
             range_set n x UNION range_set (n + x) y`--,
  SIMP_TAC hol_ss [range_set, EXTENSION, IN_UNION, SPECIFICATION]);
(* \#line miscellanea.nw 1474 *)
val _ = export_theory();

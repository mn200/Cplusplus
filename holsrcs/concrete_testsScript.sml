open HolKernel Parse boolLib boolSimps
open bossLib finite_mapTheory class_infoTheory pred_setTheory utilsTheory

open aggregatesTheory memoryTheory

val _ = new_theory "concrete_tests"

val cname_def = Define`cname = Base "c"`;
fun Store_thm(x as (n,t,tac)) = (store_thm x before export_rewrites [n])
fun Save_thm (x as (n,th)) = (save_thm x before export_rewrites [n])

val is_abs_id_cname = Store_thm(
  "is_abs_id_cname",
  ``is_abs_id cname = F``,
  SRW_TAC [][typesTheory.Base_def, cname_def, typesTheory.is_abs_id_def]);

val state1_def = Define`
  state1 = <|
    env :=
     FTNode (<| classenv :=
                  FEMPTY |+
                   (SFName "c",
                    FTNode (<| info :=
                                 SOME (<| fields :=
                                            [(FldDecl "foo" (Signed Char), F,
                                              Public);
                                             (FldDecl "bar" (Signed Int), F,
                                              Public)];
                                            ancestors := [] |>, {}) |>)
                           FEMPTY) |>)
            FEMPTY
|>
`;

val simp = SIMP_CONV (srw_ss()) [state1_def]

open environmentsTheory

val elookup_class_cname = Save_thm(
  "elookup_class_cname",
  SIMP_CONV (srw_ss()) [elookup_class_def,cname_def, typesTheory.Base_def,
                        state1_def, FLOOKUP_UPDATE]
            ``elookup_class state1.env cname``);

val lookup_class_cname = Save_thm(
  "lookup_class_cname",
  SIMP_CONV (srw_ss()) [lookup_class_def, lift_lookup_def]
            ``lookup_class state1 cname``)

val c_is_class_name_env = Store_thm(
  "c_is_class_name_env",
  ``is_class_name_env state1.env cname``,
  SRW_TAC [][is_class_name_env_def]);
val c_is_class_name = Store_thm(
  "c_is_class_name",
  ``is_class_name state1 cname``,
  SRW_TAC [][is_class_name_def]);
val c_IN_class_name = Store_thm(
  "c_IN_class_name",
  ``cname IN is_class_name state1``,
  SRW_TAC [][IN_DEF]);

val cinfo0_state1 = Save_thm(
  "cinfo0_state1",
  SIMP_CONV (srw_ss()) [cinfo0_def] ``cinfo0 state1 cname``)

val defined_classes = Store_thm(
  "defined_classes",
  ``cname IN defined_classes state1``,
  SRW_TAC [][defined_classes_def]);

val cinfo_state1_c = Save_thm(
  "cinfo_state1_c",
  SIMP_CONV (srw_ss()) [cinfo_def] ``cinfo state1 cname``);

val nsdmembers_state1 = SIMP_CONV (srw_ss()) [nsdmembers_def]
                           ``nsdmembers state1 cname``

val fmap_lemma = prove(
  ``!f. { c | ?v. c IN FDOM f /\ (f ' c = SOME v) } = FDOM (deNONE f)``,
  SRW_TAC [][EXTENSION] THEN Q.ID_SPEC_TAC `f` THEN
  HO_MATCH_MP_TAC finite_mapTheory.fmap_INDUCT THEN SRW_TAC [][] THEN
  Cases_on `y` THEN SRW_TAC [][finite_mapTheory.DOMSUB_NOT_IN_DOM] THENL [
    Cases_on `x = x'` THEN SRW_TAC [][] THENL [
      METIS_TAC [FDOM_deNONE_SUBSET],
      SRW_TAC [][FAPPLY_FUPDATE_THM]
    ],
    Cases_on `x = x'` THEN SRW_TAC [][FAPPLY_FUPDATE_THM]
  ]);

val gcc = store_thm(
  "gcc",
  ``get_class_constituents state1 mdp cname =
      [NSD "foo" (Signed Char); NSD "bar" (Signed Int)]``,
  SRW_TAC [][get_class_constituents_def] THEN
  Q.SPECL_THEN [`state1`, `cname`] MP_TAC
               get_class_constituents0_def THEN
  SIMP_TAC (srw_ss()) [nsdmembers_state1, get_direct_bases_def,
                       get_virtual_bases_def] THEN
  ONCE_REWRITE_TAC [sortingTheory.PERM_SYM] THEN
  SRW_TAC [][sortingTheory.PERM_CONS_EQ_APPEND] THEN
  Cases_on `M` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `get_class_constituents0 w x = y` SUBST_ALL_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [])

val sizeofmap = save_thm(
  "sizeofmap",
    SIMP_CONV (srw_ss()) [sizeofmap_def, nsdmembers_state1,
                          fmap_lemma, LET_THM,
                          ASSUME ``FINITE (is_class_name state1)``,
                          finite_mapTheory.FUN_FMAP_DEF, gcc]
              ``sizeofmap state1 mdp ' cname``)

val FDOM_sizeofmap = save_thm(
  "FDOM_sizeofmap",
  SIMP_CONV (srw_ss()) [sizeofmap_def, FUN_FMAP_DEF,
                        ASSUME ``FINITE (is_class_name state1)``]
            ``FDOM (sizeofmap state1 mdp)``);

val base_not_empty = store_thm(
  "base_not_empty",
  ``~empty_class (sizeofmap state1) mdp cname``,
  ONCE_REWRITE_TAC [empty_class_cases] THEN
  SRW_TAC [][sizeofmap]);

val align_int = prove(``align m mdp (Signed Int) a = (a = int_align)``,
                      ONCE_REWRITE_TAC [align_cases] THEN
                      SRW_TAC [][bit_align_def])
val align_char = prove(``align m mdp (Signed Char) a = (a = 1)``,
                       ONCE_REWRITE_TAC [align_cases] THEN
                       SRW_TAC [][bit_align_def])

val sizeof_char = prove(``sizeof mdp m (Signed Char) sz = (sz = 1)``,
                        ONCE_REWRITE_TAC [sizeof_cases] THEN
                        SRW_TAC [][bit_size_def])

val align_lemma = prove(
  ``align (sizeofmap state1) mdp (Class cname) a =
    (a = int_align)``,
  ONCE_REWRITE_TAC [align_cases] THEN
  SIMP_TAC (srw_ss() ++ DNF_ss)
           [sizeofmap, FDOM_sizeofmap,
            base_not_empty, listTheory.listRel_CONS, align_int,
            align_char, lcml_def]);

val roundup_1 = prove(
  ``0 < b ==> (roundup b 1 = b)``,
  SRW_TAC [][roundup_def] THENL [
    SPOSE_NOT_THEN ASSUME_TAC THEN
    `1 < b` by DECIDE_TAC THEN
    `1 MOD b = 1` by METIS_TAC [arithmeticTheory.LESS_MOD] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    Q_TAC SUFF_TAC `1 DIV b = 0` THEN1 SRW_TAC [][] THEN
    MATCH_MP_TAC arithmeticTheory.DIV_UNIQUE THEN SRW_TAC [][] THEN
    SPOSE_NOT_THEN ASSUME_TAC THEN
    `b = 1` by DECIDE_TAC THEN FULL_SIMP_TAC (srw_ss()) []
  ]);

val offset_1 = prove(
  ``offset (sizeofmap state1) [NSD "foo" (Signed Char);
                               NSD "bar" (Signed Int)] 1 off
     =
    (off = int_align)``,
  ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][] THEN
  STRIP_ASSUME_TAC int_align THEN SRW_TAC [ARITH_ss][roundup_1]);

val sizeof_c = store_thm(
  "sizeof_c",
  ``sizeof mdp (sizeofmap state1) (Class cname) sz =
        (sz = roundup int_align (int_align + int_size))``,
  ONCE_REWRITE_TAC [sizeof_cases] THEN
  SRW_TAC [][sizeofmap, base_not_empty, FDOM_sizeofmap, align_lemma,
             offset_1]);

val _ = export_theory()
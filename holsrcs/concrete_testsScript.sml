open HolKernel Parse boolLib boolSimps
open bossLib finite_mapTheory class_infoTheory pred_setTheory utilsTheory

val _ = new_theory "concrete_tests"

val state1_def = Define`
  state1 = ARB with classmap updated_by
      (\fm. fm |+ (Base "c",
                   SOME <| fields := [(FldDecl "foo" (Signed Char), F, Public);
                                      (FldDecl "bar" (Signed Int), F, Public)];
                           ancestors := NONE |>))
`;

val simp = SIMP_CONV (srw_ss()) [state1_def]

val state1_applied_base = save_thm(
  "state1_applied_base",
  CONJ (simp ``state1.classmap ' (Base "c")``)
       (simp ``deNONE state1.classmap ' (Base "c")``))
val _ = export_rewrites ["state1_applied_base"]

val base_in_classmap = store_thm(
  "base_in_classmap",
  ``Base "c" IN FDOM (deNONE state1.classmap) /\
    Base "c" IN FDOM state1.classmap``,
  SRW_TAC [][state1_def]);
val _ = export_rewrites ["base_in_classmap"]

val nsdmembers_state1 = SIMP_CONV (srw_ss()) [nsdmembers_def,
                                       finite_mapTheory.FLOOKUP_DEF]
                           ``nsdmembers state1 (Base "c")``

val layout = (SIMP_CONV (srw_ss()) [calc_subobjs] THENC
              ONCE_REWRITE_CONV [calc_rsubobjs] THENC
              SIMP_CONV (srw_ss()) [ancestor_def])
             ``class_layout { so | (Base "c", so) IN subobjs state1 }``

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

val class_szmap = save_thm(
  "class_szmap",
    SIMP_CONV (srw_ss()) [class_szmap_def, nsdmembers_state1, layout,
                          fmap_lemma, LET_THM, base_in_classmap,
                          finite_mapTheory.FUN_FMAP_DEF]
              ``class_szmap state1 ' (Base "c")``)

open memoryTheory
val align_int = prove(``align m (Signed Int) a = (a = int_align)``,
                      ONCE_REWRITE_TAC [align_cases] THEN
                      SRW_TAC [][bit_align_def])
val align_char = prove(``align m (Signed Char) a = (a = 1)``,
                       ONCE_REWRITE_TAC [align_cases] THEN
                       SRW_TAC [][bit_align_def])

val sizeof_char = prove(``sizeof m (Signed Char) sz = (sz = 1)``,
                        ONCE_REWRITE_TAC [sizeof_cases] THEN
                        SRW_TAC [][bit_size_def])

val align_lemma = prove(
  ``align (class_szmap state1) (Class (Base "c")) a = (a = int_align)``,
  ONCE_REWRITE_TAC [align_cases] THEN
  SIMP_TAC (srw_ss()) [class_szmap, base_in_classmap] THEN
  SIMP_TAC (srw_ss() ++ DNF_ss) [align_int, align_char] THEN
  ASSUME_TAC int_align THEN DECIDE_TAC)

val subobj_offset =
    (SIMP_CONV (srw_ss() ++ ARITH_ss)
               [subobj_offset_def, LET_THM,
                genoffset_def, layout, nsdmembers_state1,
                roundup_def, align_lemma, int_align])
      ``subobj_offset state1 (Base "c") [Base "c"]``

val nsds_bases = store_thm(
  "nsds_bases",
  ``nsds_bases state1 (Base "c") = [(SOME "foo", Signed Char, 0);
                                    (SOME "bar", Signed Int, int_align)]``,

  SIMP_TAC (srw_ss()) [nsds_bases_def, nsdmembers_state1, class_layout_def,
                       calc_subobjs] THEN
  ONCE_REWRITE_TAC [calc_rsubobjs] THEN
  SIMP_TAC (srw_ss()) [ancestor_def, base_in_classmap] THEN
  SIMP_TAC (srw_ss()) [LET_THM, subobj_offset, align_int, align_char,
                       roundup_def, sizeof_char] THEN
  ASSUME_TAC int_align THEN
  Cases_on `int_align = 1` THENL [
    SRW_TAC [][],
    `1 < int_align` by DECIDE_TAC THEN
    `1 MOD int_align = 1` by (MATCH_MP_TAC arithmeticTheory.MOD_UNIQUE THEN
                              Q.EXISTS_TAC `0` THEN SRW_TAC [][]) THEN
    `1 DIV int_align = 0` by (MATCH_MP_TAC arithmeticTheory.DIV_UNIQUE THEN
                              Q.EXISTS_TAC `1` THEN SRW_TAC [][]) THEN
    SRW_TAC [][]
  ]);

val _ = export_theory()
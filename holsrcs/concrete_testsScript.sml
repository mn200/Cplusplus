open HolKernel Parse boolLib boolSimps
open bossLib finite_mapTheory class_infoTheory pred_setTheory utilsTheory

open aggregatesTheory memoryTheory name_resolutionTheory

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
                                            [(FldDecl (SFName "foo")
                                                      (Signed Char),
                                              F,
                                              Public);
                                             (FldDecl (SFName "bar")
                                                      (Signed Int), F,
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

val RTC_class_lt_cname = Store_thm(
  "RTC_class_lt_cname",
  ``(state1,{}) |- b <= cname = (b = cname)``,
  SRW_TAC [][EQ_IMP_THM, RTC_class_lt_def, relationTheory.RTC_RULES] THEN
  POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [relationTheory.RTC_CASES2]) THEN
  SRW_TAC [][is_direct_base_def, get_direct_bases_def, is_virtual_base_def,
             get_virtual_bases_def, relationTheory.RUNION]);

val is_abstract_cname = Store_thm(
  "is_abstract_cname",
  ``is_abstract state1 cname = F``,
  SRW_TAC [][is_abstract_def] THEN
  Cases_on `bnm = cname` THEN SRW_TAC [][]);

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

(* ----------------------------------------------------------------------
    Test Two
   ---------------------------------------------------------------------- *)

(* do name resolution on the following program

   char c;
   namespace n {
     int x;
     namespace n2 {
       int y;
     }
     int z;
   }
   char d;
   namespace n {
     namespace n2 { int w; }
     namespace n3 { int u; }
   }
   template <template <class> U> U<int> f(U<char>);

   namespace n {
     int v1 = c;
     int v2 = ::c;
     int v3 = n2::y;
     int v4 = x;
     int v5 = n::x;
   }

*)
val CI_def = Define`CI e = CopyInit (mExpr e base_se)`
val _ = export_rewrites ["CI_def"]

val t2_program_def = Define`
  t2_program = [
    Decl (VDec BChar (Base "c"));
    NameSpace "n" [Decl (VDec (Signed Int) (Base "x"));
                   NameSpace "n2" [Decl (VDec (Signed Int) (Base "y"))];
                   Decl (VDec (Signed Int) (Base "z"))];
    Decl (VDec BChar (Base "d"));
    NameSpace "n" [NameSpace "n2" [Decl (VDec (Signed Int) (Base "w"))];
                   NameSpace "n3" [Decl (VDec (Signed Int) (Base "u"))]];
    TemplateDef [TTemp (Base "U")]
                (Decl (VDec (Function
                             (TypeID (IDConstant F []
                                      (SFTempCall "U" [TType (Signed Int)])))
                             [TypeID (IDConstant F []
                                      (SFTempCall "U" [TType BChar]))])
                            (Base "f")));
    NameSpace "n" [Decl (VDecInit (Signed Int)
                                  (Base "v1")
                                  (CI (Var (Base "c"))));
                   Decl (VDecInit (Signed Int)
                                  (Base "v2")
                                  (CI (Var (IDConstant T [] (SFName "c")))));
                   Decl (VDecInit (Signed Int)
                                  (Base "v3")
                                  (CI (Var (IDConstant F [SFName "n2"]
                                                         (SFName "y")))));
                   Decl (VDecInit (Signed Int)
                                  (Base "v4")
                                  (CI (Var (Base "x"))));
                   Decl (VDecInit (Signed Int)
                                  (Base "v5")
                                  (CI (Var (IDConstant F [SFName "n"]
                                                       (SFName "x")))))]
 ]
`

val NREL_def = Define`
  (NREL R 0 x y = (x = y)) /\
  (NREL R (SUC n) x y = ?z. R x z /\ NREL R n z y)
`;

val NREL_rwt = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV NREL_def

val NREL_sum = prove(
  ``!n m x y.
        NREL R (n + m) x y = ?z. NREL R n x z /\ NREL R m z y``,
  Induct_on `n` THEN SRW_TAC [][NREL_def, arithmeticTheory.ADD_CLAUSES] THEN
  METIS_TAC []);


val FUNION_FEMPTY = prove(
  ``(FUNION FEMPTY fm = fm) /\ (FUNION fm FEMPTY = fm)``,
  SRW_TAC [][finite_mapTheory.fmap_EXT, finite_mapTheory.FUNION_DEF]);

val FUNION_FUPDATE = store_thm(
  "FUNION_FUPDATE",
  ``FUNION (fm1 |+ (k,v)) fm2 = (FUNION fm1 fm2) |+ (k,v)``,
  SRW_TAC [][finite_mapTheory.fmap_EXT, finite_mapTheory.FUNION_DEF,
             INSERT_UNION_EQ] THEN
  SRW_TAC [][finite_mapTheory.FAPPLY_FUPDATE_THM,
             finite_mapTheory.FUNION_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [])

val FUN_FMAP_INSERT = prove(
  ``!s. FINITE s ==>
         !x. FUN_FMAP f (x INSERT s) = FUN_FMAP f s |+ (x, f x)``,
  HO_MATCH_MP_TAC pred_setTheory.FINITE_INDUCT THEN
  SIMP_TAC (srw_ss() ++ CONJ_ss ++ DNF_ss)
           [finite_mapTheory.fmap_EXT, finite_mapTheory.FUN_FMAP_DEF,
            finite_mapTheory.FAPPLY_FUPDATE_THM] THEN
  SRW_TAC [][])

val _ = augment_srw_ss [rewrites [typesTheory.Base_def, rewrite_type_def,
                                  fmaptreeTheory.fupd_at_path_def,
                                  fmaptreeTheory.apply_path_def,
                                  empty_env_def, FUNION_FEMPTY,
                                  FUNION_FUPDATE,
                                  CONJUNCT1 NREL_def, FUN_FMAP_INSERT]]


val open_ftnode_thm = CONJ (Q.SPEC `[]` open_ftnode_def)
                           (GEN_ALL (Q.SPEC `h::t` open_ftnode_def))

val open_path_thm =
    CONJ (SIMP_RULE list_ss [] (Q.INST [`todo` |-> `[]`] open_path_def))
         (SIMP_RULE list_ss [] (Q.INST [`todo` |-> `h::t`] open_path_def))

val id_objtype_thm = let
  val base = SPEC_ALL id_objtype_def
in
  CONJ (SIMP_RULE (srw_ss()) [] (Q.INST [`id` |-> `IDConstant b [] sf`] base))
       (SIMP_RULE (srw_ss()) []
                  (Q.INST [`id` |-> `IDConstant b (h::t) sf`] base))
end

(* attach conditional congruence rule to stop evaluation of branches *)

val vardecl =
    ONCE_REWRITE_CONV [NREL_rwt] THENC
    ONCE_REWRITE_CONV [phase1_cases] THENC
    SIMP_CONV (srw_ss()) [] THENC
    SIMP_CONV (srw_ss()) [EnterNSpace_def, open_path_thm, LET_THM,
                          open_ftnode_thm, NewGVar_def, state_NewGVar_def,
                          ExitNSpace_def, newlocal_def, id_objtype_thm,
                          phase1_fndefn_def, empty_p1_def,
                          is_class_name_def, is_class_name_env_def,
                          elookup_class_def,
                          finite_mapTheory.FAPPLY_FUPDATE_THM,
                          instantiationTheory.IDhd_inst_def] THENC
    SIMP_CONV (srw_ss() ++ DNF_ss) [finite_mapTheory.FUPDATE_COMMUTES,
                                   mk_last_init_def, LET_THM];

fun NCONV n c = if n <= 0 then ALL_CONV else c THENC NCONV (n - 1) c;

val recalc = ref false
val istate = statesTheory.initial_state_def
fun mk_initial prog = ``(MAP P1Decl ^prog, empty_p1 [] initial_state)``

fun fourmore pfx prog n = let
  fun recurse n =
    if not (!recalc) andalso can theorem (pfx^Int.toString n) then
      print ("Cache hit for "^pfx^Int.toString n^"\n")
    else let
        fun mkn i = numSyntax.mk_numeral (Arbnum.fromInt i)
        val prev0 = (n div 4) * 4
        val (diff,prev) = if prev0 = n then (4,n-4) else (n - prev0,prev0)
        val n_t = mkn n
        val nth = DECIDE ``^n_t = ^(mkn (n - diff)) + ^(mkn diff)``
        val t = ``NREL phase1 ^n_t ^(mk_initial (lhs (concl prog))) (p, s)``
        val tac = if n > 4 then let
                      val _ = recurse prev
                      val th = theorem (pfx^Int.toString prev)
                    in
                      ONCE_REWRITE_CONV [nth] THENC
                      SIMP_CONV (srw_ss()) [NREL_sum, GEN_ALL th,
                                            pairTheory.EXISTS_PROD] THENC
                      NCONV diff vardecl
                    end
                  else
                    SIMP_CONV (srw_ss()) [prog, istate, empty_p1_def] THENC
                    NCONV n vardecl
      in
        save_thm(pfx^Int.toString n, tac t);
        print (pfx^Int.toString n^"\n")
      end
in
  recurse n
end

val _ = fourmore "t2_step_" t2_program_def 27

(* ----------------------------------------------------------------------
    test #3

    int x;
    int f(int n) { return n + x; }
   ---------------------------------------------------------------------- *)

val t3_program_def = Define`
  t3_program = [Decl (VDec (Signed Int) (Base "x"));
                FnDefn (Signed Int)
                       (Base "f")
                       [("n", Signed Int)]
                       (Ret (mExpr (CApBinary CPlus
                                              (Var (Base "n"))
                                              (Var (Base "x")))
                                   base_se))]
`;

val _ = fourmore "t3_step_" t3_program_def 2

local
  val th = theorem "t3_step_2"
  val s_t = lhs (rand (rand (concl th)))
  val assertion = can prove(``LAST ^s_t.accdecls =
                          FnDefn (Signed Int) (IDConstant T [] (SFName "f"))
                                 [("n", Signed Int)]
                                 (Ret (mExpr
                                       (CApBinary
                                          CPlus
                                          (Var (IDConstant F [] (SFName "n")))
                                          (Var (IDConstant T [] (SFName "x")))
                                          )
                                       base_se))``,
                         SRW_TAC [][])
in
val _ = if assertion then print "Test #3 assertion passes\n"
        else print "Test #3 assertion fails\n"
end






val _ = export_theory()

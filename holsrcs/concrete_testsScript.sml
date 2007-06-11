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
                   (IDName "c",
                    FTNode (<| info :=
                                 SOME (<| fields :=
                                            [(FldDecl (IDName "foo")
                                                      (Signed Char),
                                              F,
                                              Public);
                                             (FldDecl (IDName "bar")
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
  ``(state1,{}) |- cname <= b = (b = cname)``,
  SRW_TAC [][EQ_IMP_THM, RTC_class_lt_def, relationTheory.RTC_RULES] THEN
  POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [relationTheory.RTC_CASES1]) THEN
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
val CI_def = Define`CI e = CopyInit (EX e base_se)`
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
                                      (IDTempCall "U" [TType (Signed Int)])))
                             [TypeID (IDConstant F []
                                      (IDTempCall "U" [TType BChar]))])
                            (Base "f")));
    NameSpace "n" [Decl (VDecInit (Signed Int)
                                  (Base "v1")
                                  (CI (Var (Base "c"))));
                   Decl (VDecInit (Signed Int)
                                  (Base "v2")
                                  (CI (Var (IDConstant T [] (IDName "c")))));
                   Decl (VDecInit (Signed Int)
                                  (Base "v3")
                                  (CI (Var (IDConstant F [IDName "n2"]
                                                         (IDName "y")))));
                   Decl (VDecInit (Signed Int)
                                  (Base "v4")
                                  (CI (Var (Base "x"))));
                   Decl (VDecInit (Signed Int)
                                  (Base "v5")
                                  (CI (Var (IDConstant F [IDName "n"]
                                                       (IDName "x")))))]
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
val COND_EVAL_CONG = prove(
  ``(b = b') ==> ((if b then t else f) = (if b' then t else f))``,
  SRW_TAC [][])
val option_CASE_EVAL_CONG = prove(
  ``(opt = opt') ==> (option_case nc sc opt = option_case nc sc opt')``,
  SRW_TAC [][]);
val ID_CASE_EVAL_CONG = prove(
  ``(id = id') ==> (CPP_ID_case ic id = CPP_ID_case ic id')``,
  SRW_TAC [][]);

val EVAL_ss = simpLib.SSFRAG { ac = [], congs = [COND_EVAL_CONG,
                                                 option_CASE_EVAL_CONG,
                                                 ID_CASE_EVAL_CONG],
                               convs = [], dprocs = [], filter = NONE,
                               rewrs = [] }
val _ = augment_srw_ss [EVAL_ss]

val empty_frees_thm = prove(
  ``({}.tyfvs = {}) /\ ({}.tempfvs = {})``,
  SRW_TAC [][freesTheory.empty_freerec_def]);
val _ = augment_srw_ss [rewrites [empty_frees_thm]]

val RTC_class_lt_thm =
    (SIMP_RULE (srw_ss() ++ DNF_ss) [GSYM RTC_class_lt_def] o
     SIMP_RULE (srw_ss()) [Once relationTheory.RTC_CASES1,
                           relationTheory.RUNION, cinfo_def, cinfo0_def,
                           is_direct_base_def, is_virtual_base_def,
                           get_direct_bases_def, get_virtual_bases_def] o
     Q.INST [`c1` |-> `IDConstant b sfs sf`, `s` |-> `st,Set`]  o
     SPEC_ALL) RTC_class_lt_def
val lift_lookup_thm =
    CONJ ((SIMP_RULE (srw_ss()) [] o
           Q.INST [`id` |-> `IDConstant T sfs sf`] o
           SPEC_ALL) lift_lookup_def)
         ((SIMP_RULE (srw_ss()) [] o
           Q.INST [`id` |-> `IDConstant F sfs sf`] o
           SPEC_ALL) lift_lookup_def)

val expr_type_rewrites =
    REWRITE_RULE [ONCE_REWRITE_CONV [EQ_SYM_EQ]
                                    ``lookup_type env id = SOME ty``]
                 staticsTheory.expr_type_rewrites

val cinfo_thm = Q.INST [`cnm` |-> `IDConstant b sfs sf`] (SPEC_ALL cinfo_def)
val cinfo0_thm = Q.INST [`cnm` |-> `IDConstant b sfs sf`] (SPEC_ALL cinfo0_def)
val defined_classes_thm =
    SIMP_CONV (srw_ss()) [defined_classes_def]
              ``IDConstant b sfs sf IN defined_classes s``
val is_class_name_thm =
    SIMP_CONV (srw_ss()) [is_class_name_def]
                        ``is_class_name s (IDConstant b sfs sf)``
val subobjs_thm =
  SIMP_CONV (srw_ss()) [calc_subobjs]
            ``(IDConstant b sfs sf, Cs) IN subobjs s``
val rsubobjs_thm =
    SIMP_CONV (srw_ss()) [Once calc_rsubobjs]
              ``(IDConstant b sfs sf, Cs) IN rsubobjs s``

val open_classnode_thm = (Q.INST [`cnm` |-> `IDConstant b sfs sf`] o
                          SPEC_ALL) open_classnode_def


val vardecl =
    ONCE_REWRITE_CONV [NREL_rwt] THENC
    ONCE_REWRITE_CONV [phase1_cases] THENC
    SIMP_CONV (srw_ss()) [] THENC
    SIMP_CONV (srw_ss())
              [EnterNSpace_def, open_path_thm, LET_THM,
               open_ftnode_thm, NewGVar_def, state_NewGVar_def,
               ExitNSpace_def, newlocal_def, id_objtype_thm,
               lookup_type_def, lift_lookup_thm,
               phase1_fndefn_def, empty_p1_def,
               is_class_name_thm, is_class_name_env_def,
               elookup_class_def, freesTheory.tempfree_sing_def,
               finite_mapTheory.FAPPLY_FUPDATE_THM,
               finite_mapTheory.FLOOKUP_DEF, cinfo_thm,
               cinfo0_thm, defined_classes_thm, expr_type_rewrites,
               local_class_def, is_virtual_def,
               RTC_class_lt_thm, elookup_class_def,
               elookup_type_def, mk_dynobj_id_def, subobjs_thm,
               rsubobjs_thm, empty_frees_thm, open_classnode_thm,
               instantiationTheory.IDhd_inst_def] THENC
    SIMP_CONV (srw_ss() ++ DNF_ss ++ CONJ_ss)
              [finite_mapTheory.FUPDATE_COMMUTES,
               mk_last_init_def, LET_THM];

fun NCONV n c = if n <= 0 then ALL_CONV else c THENC NCONV (n - 1) c;

val recalc = ref false
val istate = statesTheory.initial_state_def
fun mk_initial prog = ``(MAP P1Decl ^prog, empty_p1 [] initial_state)``

fun fourmore pfx0 prog n = let
  val pfx = pfx0^"_step_"
  fun recurse n =
      case (!recalc, Lib.total theorem (pfx^Int.toString n)) of
        (false, SOME th) => (if !Globals.interactive then
                               print ("Cache hit for "^pfx^Int.toString n^"\n")
                             else ();
                             th)
      | _ => let
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
          save_thm(pfx^Int.toString n, tac t)
          before
          (if !Globals.interactive then print (pfx^Int.toString n^"\n")
           else ())
      end
in
  recurse n
end

val _ = fourmore "t2" t2_program_def 31

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
                       (Ret (EX (CApBinary CPlus
                                              (Var (Base "n"))
                                              (Var (Base "x")))
                                   base_se))]
`;

val _ = fourmore "t3" t3_program_def 2

local
  val th = theorem "t3_step_2"
  val s_t = lhs (rand (rand (concl th)))
  val assertion = can prove(``LAST ^s_t.accdecls =
                          FnDefn (Signed Int) (IDConstant T [] (IDName "f"))
                                 [("n", Signed Int)]
                                 (Ret (EX
                                       (CApBinary
                                          CPlus
                                          (Var (IDConstant F [] (IDName "n")))
                                          (Var (IDConstant T [] (IDName "x")))
                                          )
                                       base_se))``,
                         SRW_TAC [][])
in
val _ = if assertion then print "Test #3 assertion passes\n"
        else print "Test #3 assertion fails\n"
end

(* ----------------------------------------------------------------------
    test #4

    int x;
    int f(int x) { return x + x; }
   ---------------------------------------------------------------------- *)

val t4_program_def = Define`
  t4_program = [Decl (VDec (Signed Int) (Base "x"));
                FnDefn (Signed Int)
                       (Base "f")
                       [("x", Signed Int)]
                       (Ret (EX (CApBinary CPlus
                                              (Var (Base "x"))
                                              (Var (Base "x")))
                                   base_se))]
`;

val _ = fourmore "t4" t4_program_def 2

local
  val th = theorem "t4_step_2"
  val s_t = lhs (rand (rand (concl th)))
  val assertion = can prove(``LAST ^s_t.accdecls =
                          FnDefn (Signed Int) (IDConstant T [] (IDName "f"))
                                 [("x", Signed Int)]
                                 (Ret (EX
                                       (CApBinary
                                          CPlus
                                          (Var (IDConstant F [] (IDName "x")))
                                          (Var (IDConstant F [] (IDName "x")))
                                          )
                                       base_se))``,
                         SRW_TAC [][])
in
val _ = if assertion then print "Test #4 assertion passes\n"
        else print "Test #4 assertion fails\n"
end

(* ----------------------------------------------------------------------
    test #5

    int x;
    int f(int i)
    {
      int j = i + x;
      if (j > 0) {
        int x = 3;
        j = j - x + ::x;
      }
      return j;
    }

   ---------------------------------------------------------------------- *)

val t5_program_def = Define`
  t5_program =
     [Decl (VDec (Signed Int) (Base "x"));
      FnDefn (Signed Int)
             (Base "f")
             [("i", Signed Int)]
             (Block F [VDecInit (Signed Int)
                                (Base "j")
                                (CI (CApBinary CPlus
                                               (Var (Base "i"))
                                               (Var (Base "x"))))]
                      [CIf (EX (CApBinary CGreat
                                             (Var (Base "j"))
                                             (Cnum 0))
                                  base_se)
                           (Block F [VDecInit (Signed Int)
                                              (Base "x")
                                              (CI (Cnum 3))]
                            [Standalone
                               (EX
                                  (Assign
                                     NONE
                                     (Var (Base "j"))
                                     (CApBinary CPlus
                                                (CApBinary
                                                   CMinus
                                                   (Var (Base "j"))
                                                   (Var (Base "x")))
                                                (Var (IDConstant
                                                        T [] (IDName "x")))))
                                  base_se)])
                           EmptyStmt;
                       Ret (EX (Var (Base "j")) base_se)])]
`;

val _ = fourmore "t5" t5_program_def 2

(* ----------------------------------------------------------------------
    test #6

    int x;
    int f()
    {
      struct s {
        int g() { return x; }
        int x;
      };
      s val;
      val.x = x;
      return val.g();
    }

   ---------------------------------------------------------------------- *)

val _ = Globals.linewidth := 160;
val t6_program_def = Define`
  t6_program =
    [Decl (VDec (Signed Int) (Base "x"));
     FnDefn (Signed Int) (Base "f") []
       (Block F
          [VStrDec (Base "s")
             (SOME
               <| ancestors := [];
                  fields := [(CFnDefn F (Signed Int) (IDName "g") []
                                (SOME (SOME (Ret (EX (Var (Base "x"))
                                                        base_se)))),
                                F, Public);
                             (FldDecl (IDName "x") (Signed Int), F, Public)]
               |>);
           VDec (Class (Base "s")) (Base "val")]
          [Standalone
             (EX
              (Assign NONE
                      (SVar (Var (Base "val")) (Base "x"))
                      (Var (Base "x")))
              base_se);
           Ret (EX (FnApp (SVar (Var (Base "val")) (Base "g")) [])
                      base_se)])]
`;

val let_thms = prove(
  ``(LET (\x. v1) v2 = v1) /\ (LET (\x. f1 x) [] = f1 []) /\
    (LET f (v1,v2) =
       LET (\x. LET (\y. f (x, y)) v2) v1) /\
    (LET f' (IDConstant T [] sf) = f' (IDConstant T [] sf)) /\
    (LET f' (IDConstant F [] sf) = f' (IDConstant F [] sf)) /\
    (LET f' (IDConstant b sfs sf) =
       let b0 = b in let sfs0 = sfs in let sf0 = sf in
         f' (IDConstant b0 sfs0 sf0)) /\
    (LET f2 (STRING c cs) = f2 (STRING c cs)) /\
    (LET f3 (Function ty1 ty2) =
       LET (\ret. LET (\argtys. f3 (Function ret argtys)) ty2) ty1) /\
    (LET f3 (Signed Int) = f3 (Signed Int)) /\
    (LET f3 (Class id) = let id0 = id in f3 (Class id0)) /\
    (LET f5 (h :: t) = LET (\h0. LET (\t0. f5 (h0::t0)) t) h) /\
    (LET f6 FEMPTY = f6 FEMPTY) /\
    (LET f6 ((fm: 'a |-> 'b) |+ kv) =
      LET (\fm0. LET (\kv0. f6 (fm0 |+ kv0)) kv) fm) /\
    (LET f7 <|current_nspath := cns; dynclasses := dcs; dynobjs := dos;
              dynns := dns; global := glob;
              accdecls := acs |> =
       LET (\cns0. LET (\dcs0. LET (\dos0. LET (\dns0. LET (\glob0.
             LET (\acs0. f7
                  <|current_nspath := cns0; dynclasses := dcs0;
                    dynobjs := dos0;
                    dynns := dns0; global := glob0;
                    accdecls := acs0 |>) acs) glob) dns) dos) dcs) cns) /\
    (LET f8 T = f8 T) /\ (LET f8 F = f8 F) /\
    (LET f9 dNormalObj = f9 dNormalObj) /\
    (LET f9 dMember = f9 dMember) /\
    (LET f10    <|allocmap := am; hallocmap := hm; initmap := im; 
                  fnmap := fnm; fnencode := fem; fndecode := fdm;
                 genv := genv ;
                 env := env; stack := stk; thisvalue := this;
                 blockclasses := bcs; exprclasses := ecs|> =
       let am0 = am in let hm0 = hm in let fnm0 = fnm in let fem0 = fem in
       let fdm0 = fdm in
       let genv0 = genv in let env0 = env in let im0 = im in let stk0 = stk in
       let this0 = this in let bcs0 = bcs in let ecs0 = ecs in
         f10  <|allocmap := am0; hallocmap := hm0; initmap := im0; 
                fnmap := fnm0;
                  fnencode := fem0; fndecode := fdm0;
                 genv := genv0 ;
                 env := env0; stack := stk0;
                 thisvalue := this0;
                 blockclasses := bcs0; exprclasses := ecs0|>) /\
    (LET f11 NONE = f11 NONE) /\
    (LET f11 (SOME x) = let x0 = x in f11 (SOME x0)) /\
    (LET f12 ({}:'a -> bool) = f12 {}) /\
    (LET f12 (x INSERT s) = let x0 = x in let s0 = s in f12 (x0 INSERT s0)) /\
    (LET f13 ({}:frees_record) = f13 {}) /\
    (LET f14 (Decl d) = f14 (Decl d)) /\
    (LET f15 (FTNode i m) = f15 (FTNode i m)) /\
    (LET f16 <| fields := fs; ancestors := ancs |> =
       let fs0 = fs in let ancs0 = ancs in
         f16 <| fields := fs0; ancestors := ancs0 |>) /\
    (LET f17 (CFnDefn b ty nm pms st) =
       let b0 = b in let ty0 = ty in let nm0 = nm in let pms0 = pms in
          f17 (CFnDefn b0 ty0 nm0 pms0 st)) /\
    (LET f17 (FldDecl sf ty) = let ty0 = ty in let sf0 = sf in
                                                 f17 (FldDecl sf0 ty0)) /\
    (LET f18 Public = f18 Public) /\
    (LET f19 (IDName str) = f19 (IDName str)) /\
    (LET f20 (<| typemap := tm; tempmap := tm'; valmap := vm |>) =
         f20 <| typemap := tm; tempmap := tm'; valmap := vm |>) /\
    (LET f21 (Ret e) = f21 (Ret e)) /\
    (LET f21 (Standalone e) = f21 (Standalone e)) /\
    (LET f21 (Block b vds sts) = 
         let b0 = b in let vds0 = vds in let sts0 = sts in 
           f21 (Block b0 vds0 sts0)) /\
    (LET f22 (VStrDec id ci) =
       let id0 = id in let ci0 = ci in f22 (VStrDec id0 ci0)) /\
    (LET f22 (VDec ty id) =
       let id0 = id in let ty0 = ty in f22 (VDec ty0 id0)) /\
    (LET f23 (Var id) = let id0 = id in f23 (Var id0)) /\
    (LET f24 (SVar exp id) = let exp0 = exp in 
                             let id0 = id in f24 (SVar exp0 id0))
``,
  SRW_TAC [][LET_THM]);
val _ = augment_srw_ss [rewrites [let_thms]]

val LET_CONG = prove(``(v = v') ==> (LET f v = LET f v')``, SRW_TAC [][])

val RTC_REFL = prove(``RTC R x x``, SRW_TAC [][relationTheory.RTC_RULES])
val pGSPEC_U = prove(
  ``GSPEC (\ (p,q). (f p q, s1 p q \/ s2 p q)) =
      GSPEC (\ (p,q). (f p q, s1 p q)) UNION
      GSPEC (\ (p,q). (f p q, s2 p q))``,
  SRW_TAC [][pred_setTheory.EXTENSION, EQ_IMP_THM] THEN METIS_TAC []);
val pGSPEC_SING = prove(
  ``GSPEC (\ (p,q). ((p,q), (x = p) /\ (q = y))) = {(x,y)}``,
  SRW_TAC [][pred_setTheory.EXTENSION, EQ_IMP_THM]);
val pGSPEC_F = prove(
  ``GSPEC (\ (p,q). (f p q, F)) = {}``,
  SRW_TAC [][pred_setTheory.EXTENSION]);
val setfn_2 = prove(
  ``~(x = y) ==> ({(x,u); (y,v)} ' x = u) /\
                 ({(x,u); (y,v)} ' y = v)``,
  SRW_TAC [][] THEN MATCH_MP_TAC SETFN_UNIQUE THEN
  SRW_TAC [][]);

val setfn_1 = prove(``{(x,v)} ' x = v``,
                    MATCH_MP_TAC SETFN_UNIQUE THEN SRW_TAC [][]);

val _ = augment_srw_ss [rewrites [pGSPEC_F, pGSPEC_SING, pGSPEC_U,
                                  pred_setTheory.INSERT_UNION_EQ,
                                  okfield_def, RTC_REFL, fieldname_def,
                                  fieldtype_def, FLOOKUP_DEF, setfn_1,
                                  FAPPLY_FUPDATE_THM, expr_type_rewrites, 
                                  mk_dynobj_id_def
                       ]]


val t6_2_1 = let
  val t = ``NREL phase1 2 ^(mk_initial (rhs (concl t6_program_def))) (p,s)``
  val th0 = SIMP_CONV (srw_ss()) [NREL_rwt, pairTheory.EXISTS_PROD,
                                  empty_p1_def,
                                  statesTheory.initial_state_def] t
  val _ = print "0 "
  val th1 = SIMP_RULE (srw_ss()) [Once phase1_cases, NewGVar_def, LET_THM,
                                  state_NewGVar_def] th0
  val _ = print "1 "
  val th2 = SIMP_RULE (srw_ss()) [Once phase1_cases, Cong LET_CONG,
                                  state_NewGVar_def,
                                  phase1_fndefn_def, NewGVar_def] th1
  val _ = print "2 ";
  val th3 = SIMP_RULE (srw_ss()) [open_path_thm, open_classnode_thm,
                                  Cong LET_CONG, pairTheory.EXISTS_PROD,
                                  fieldty_via_def, FieldDecls_def,
                                  subobjs_thm, rsubobjs_thm,
                                  defined_classes_thm, is_virtual_base_def,
                                  is_direct_base_def, get_virtual_bases_def,
                                  get_direct_bases_def, is_class_name_thm,
                                  is_class_name_env_def, cinfo_thm,
                                  cinfo0_thm,
                                  RTC_class_lt_thm] th2
  val _ = print "3 ";
  val th4 = SIMP_RULE (srw_ss()) [methodty_via_def, subobjs_thm, rsubobjs_thm,
                                  defined_classes_thm, MethodDefs_def,
                                  Cong LET_CONG, cinfo_thm, cinfo0_thm,
                                  is_class_name_thm, is_class_name_env_def,
                                  is_virtual_base_def,
                                  is_direct_base_def, get_virtual_bases_def,
                                  get_direct_bases_def, RTC_class_lt_thm] th3
  val _ = print "4 ";
  val th5 = SIMP_RULE (srw_ss()) [injected_via_def, subobjs_thm, rsubobjs_thm,
                                  defined_classes_thm, InjectedClasses_def,
                                  Cong LET_CONG, cinfo_thm, cinfo0_thm,
                                  is_class_name_thm, is_class_name_env_def,
                                  is_virtual_base_def,
                                  is_direct_base_def, get_virtual_bases_def,
                                  get_direct_bases_def, RTC_class_lt_thm,
                                  nested_class_def] th4
  val _ = print "5 ";
  val th6 = SIMP_RULE (srw_ss() ++ CONJ_ss) [Cong LET_CONG] th5
  val _ = print "6 ";
  val th7 = SIMP_RULE (srw_ss()) [Cong LET_CONG, open_classnode_thm,
                                  pairTheory.EXISTS_PROD, open_path_thm,
                                  fieldty_via_def, FieldDecls_def,
                                  subobjs_thm, rsubobjs_thm,
                                  defined_classes_thm, is_virtual_base_def,
                                  is_direct_base_def, get_virtual_bases_def,
                                  get_direct_bases_def, is_class_name_thm,
                                  is_class_name_env_def, cinfo_thm,
                                  cinfo0_thm, methodty_via_def, MethodDefs_def,
                                  injected_via_def, InjectedClasses_def,
                                  RTC_class_lt_thm] th6
  val _ = print "7 ";
  val th8 = SIMP_RULE (srw_ss() ++ DNF_ss) [Cong LET_CONG, setfn_2] th7
  val _ = print "8 ";
  val th9 = SIMP_RULE (srw_ss()) [Cong LET_CONG, open_classnode_thm,
                                  pairTheory.EXISTS_PROD, open_path_thm,
                                  fieldty_via_def, FieldDecls_def,
                                  subobjs_thm, rsubobjs_thm,
                                  defined_classes_thm, is_virtual_base_def,
                                  is_direct_base_def, get_virtual_bases_def,
                                  get_direct_bases_def, is_class_name_thm,
                                  is_class_name_env_def, cinfo_thm,
                                  cinfo0_thm, methodty_via_def, MethodDefs_def,
                                  injected_via_def, InjectedClasses_def,
                                  RTC_class_lt_thm] th8
  val _ = print "9 ";
  val th10 = SIMP_RULE (srw_ss() ++ DNF_ss) [Cong LET_CONG] th9
  val _ = print "10 ";
  val th11 = SIMP_RULE (srw_ss()) [is_virtual_def, Cong LET_CONG,
                                   RTC_class_lt_thm, cinfo_thm, cinfo0_thm]
             th10
  val _ = print "11 ";
  val th12 = SIMP_RULE (srw_ss()) [Cong LET_CONG, open_classnode_thm,
                                  pairTheory.EXISTS_PROD, open_path_thm,
                                  fieldty_via_def, FieldDecls_def,
                                  subobjs_thm, rsubobjs_thm,
                                  defined_classes_thm, is_virtual_base_def,
                                  is_direct_base_def, get_virtual_bases_def,
                                  get_direct_bases_def, is_class_name_thm,
                                  is_class_name_env_def, cinfo_thm,
                                  cinfo0_thm, methodty_via_def, MethodDefs_def,
                                  injected_via_def, InjectedClasses_def,
                                  RTC_class_lt_thm, nested_class_def] th11
  val _ = print "12 ";
  val th13 = SIMP_RULE (srw_ss() ++ DNF_ss) [Cong LET_CONG] th12
  val _ = print "13 ";
  val th14 = SIMP_RULE (srw_ss() ++ CONJ_ss) [Cong LET_CONG] th13
  val _ = print "14 ";
  val th15 = SIMP_RULE (srw_ss()) [Cong LET_CONG, FAPPLY_FUPDATE_THM] th14
  val _ = print "15 ";
  val th16 = SIMP_RULE (srw_ss()) [Cong LET_CONG, newlocal_def] th15
  val _ = print "16 ";
  val th17 = SIMP_RULE (srw_ss()) [Cong LET_CONG, 
                                   lookup_type_def, lift_lookup_def,
                                   elookup_type_def] th16
  val _ = print "17 ";
  val th18 = SIMP_RULE (srw_ss() ++ CONJ_ss) [Cong LET_CONG] th17
  val _ = print "18 ";
  val th19 = SIMP_RULE (srw_ss()) [Cong LET_CONG, open_classnode_thm,
                                  pairTheory.EXISTS_PROD, open_path_thm,
                                  fieldty_via_def, FieldDecls_def,
                                  subobjs_thm, rsubobjs_thm,
                                  defined_classes_thm, is_virtual_base_def,
                                  is_direct_base_def, get_virtual_bases_def,
                                  get_direct_bases_def, is_class_name_thm,
                                  is_class_name_env_def, cinfo_thm,
                                  cinfo0_thm, methodty_via_def, MethodDefs_def,
                                  injected_via_def, InjectedClasses_def,
                                  RTC_class_lt_thm, nested_class_def] th18
  val _ = print "19 ";
  val th20 = SIMP_RULE (srw_ss() ++ DNF_ss) [Cong LET_CONG, setfn_2] th19
  val _ = print "20 ";
  val th21 = SIMP_RULE (srw_ss()) [Cong LET_CONG, open_classnode_thm,
                                  pairTheory.EXISTS_PROD, open_path_thm,
                                  fieldty_via_def, FieldDecls_def,
                                  subobjs_thm, rsubobjs_thm,
                                  defined_classes_thm, is_virtual_base_def,
                                  is_direct_base_def, get_virtual_bases_def,
                                  get_direct_bases_def, is_class_name_thm,
                                  is_class_name_env_def, cinfo_thm,
                                  cinfo0_thm, methodty_via_def, MethodDefs_def,
                                  injected_via_def, InjectedClasses_def,
                                  RTC_class_lt_thm, nested_class_def] th20
  val _ = print "21 ";
  val th22 = SIMP_RULE (srw_ss() ++ DNF_ss) [Cong LET_CONG] th21
  val _ = print "22 ";
  val th23 = SIMP_RULE (srw_ss()) [is_virtual_def, Cong LET_CONG,
                                   RTC_class_lt_thm, cinfo_thm, cinfo0_thm]
             th22
  val _ = print "23 ";
  val th24 = SIMP_RULE (srw_ss()) [Cong LET_CONG, open_classnode_thm,
                                  pairTheory.EXISTS_PROD, open_path_thm,
                                  fieldty_via_def, FieldDecls_def,
                                  subobjs_thm, rsubobjs_thm,
                                  defined_classes_thm, is_virtual_base_def,
                                  is_direct_base_def, get_virtual_bases_def,
                                  get_direct_bases_def, is_class_name_thm,
                                  is_class_name_env_def, cinfo_thm,
                                  cinfo0_thm, methodty_via_def, MethodDefs_def,
                                  injected_via_def, InjectedClasses_def,
                                  RTC_class_lt_thm, nested_class_def] th23
  val _ = print "24 ";
  val th25 = SIMP_RULE (srw_ss() ++ DNF_ss) [Cong LET_CONG] th24
  val _ = print "25 ";
  val th26 = SIMP_RULE (srw_ss() ++ CONJ_ss) [Cong LET_CONG] th25
  val _ = print "26 ";
  val th27 = SIMP_RULE (srw_ss()) [Cong LET_CONG, mk_dynobj_id_def,
                                   FAPPLY_FUPDATE_THM] th26
  val _ = print "27\n";
in
  save_thm("t6_final", SIMP_RULE (srw_ss()) [LET_THM] th27)
end

val _ = export_theory()

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

val deNONE = store_thm(
  "deNONE",
  ``k IN FDOM f /\ ~(f ' k = NONE) ==> (deNONE f ' k = THE (f ' k))``,
  SRW_TAC [][finite_mapTheory.DRESTRICT_DEF, deNONE_def,
             finite_mapTheory.o_f_DEF])


(* ----------------------------------------------------------------------
    establish type of branching tree
   ---------------------------------------------------------------------- *)

val (is_tree_rules, is_tree_ind, is_tree_cases) = Hol_reln`
  (!a. is_tree (\p. INL (a:'a))) /\
  (!f (b:'b). (!(d:'d). is_tree (f d)) ==>
         is_tree (\p. if p = [] then INR b
                      else f (HD p) (TL p)))
`

val inftree = new_type_definition(
  "inftree",
  prove(``?x : ('d list -> 'a + 'b). is_tree x``, METIS_TAC [is_tree_rules]))

val inftree_bijections = define_new_type_bijections {
  ABS = "to_inftree", REP = "from_inftree",
  name = "inftree_bijections", tyax = inftree
};

val fromto_id = prove(
  ``is_tree f ==> (from_inftree (to_inftree f) = f)``,
  METIS_TAC [inftree_bijections])

val is_tree_from_inftree = prove(
  ``is_tree (from_inftree x)``,
  METIS_TAC [inftree_bijections])
val _ = BasicProvers.augment_srw_ss [rewrites [is_tree_from_inftree]]

val from_inftree_11 = prove(
  ``(from_inftree t1 = from_inftree t2) = (t1 = t2)``,
  METIS_TAC [inftree_bijections])
val _ = BasicProvers.augment_srw_ss [rewrites [from_inftree_11]]

val iLf_def = Define`
  iLf a = to_inftree (\p. INL a)
`

val iNd_def = Define`
  iNd b f = to_inftree (\p. if p = [] then INR b
                            else from_inftree (f (HD p)) (TL p))
`

val iNd_is_tree = store_thm(
  "iNd_is_tree",
  ``!b f. is_tree (\p. if p = [] then INR b
                       else from_inftree (f (HD p)) (TL p))``,
  REPEAT GEN_TAC THEN
  Q_TAC SUFF_TAC `is_tree (\p. if p = [] then INR b
                               else (from_inftree o f) (HD p) (TL p))`
        THEN1 SRW_TAC [][] THEN
  MATCH_MP_TAC (#2 (CONJ_PAIR is_tree_rules)) THEN
  SRW_TAC [][])

val inftree_11 = store_thm(
  "inftree_11",
  ``((iLf a1 = iLf a2 : ('a,'b,'c) inftree) = (a1 = a2)) /\
    ((iNd b1 f1 = iNd b2 f2 : ('a,'b,'c)inftree) = (b1 = b2) /\ (f1 = f2))``,
  SRW_TAC [][iLf_def, iNd_def] THENL [
    SRW_TAC [][EQ_IMP_THM] THEN
    POP_ASSUM (MP_TAC o AP_TERM ``from_inftree``) THEN
    SIMP_TAC std_ss [fromto_id, is_tree_rules, FUN_EQ_THM],

    REVERSE EQ_TAC THEN1 SRW_TAC [][] THEN
    DISCH_THEN (MP_TAC o AP_TERM ``from_inftree``) THEN
    RW_TAC std_ss [fromto_id, FUN_EQ_THM, iNd_is_tree] THENL [
      POP_ASSUM (Q.SPEC_THEN `[]` MP_TAC) THEN SRW_TAC [][],
      POP_ASSUM (Q.SPEC_THEN `x::t` (MP_TAC o GEN ``t:'c list``)) THEN
      SRW_TAC [][] THEN
      Q_TAC SUFF_TAC `from_inftree (f1 x) = from_inftree (f2 x)`
            THEN1 SRW_TAC [][] THEN
      ASM_SIMP_TAC std_ss [FUN_EQ_THM]
    ]
  ]);
val _ = export_rewrites ["inftree_11"]

val inftree_distinct = store_thm(
  "inftree_distinct",
  ``~(iLf a = iNd b f)``,
  SRW_TAC [][iLf_def, iNd_def] THEN
  DISCH_THEN (MP_TAC o AP_TERM ``from_inftree``) THEN
  SIMP_TAC std_ss [fromto_id, iNd_is_tree, is_tree_rules, FUN_EQ_THM] THEN
  Q.EXISTS_TAC `[]` THEN SRW_TAC [][])
val _ = export_rewrites ["inftree_distinct"]

val strong_ind =
    SIMP_RULE std_ss [is_tree_rules]
              (Q.SPEC `\f. is_tree f /\ P f` is_tree_ind)

val forall_inftree = prove(
  ``(!t. P t) = (!f. is_tree f ==> P (to_inftree f))``,
  METIS_TAC [inftree_bijections]);

val inftree_ind = store_thm(
  "inftree_ind",
  ``!P.
       (!a. P (iLf a)) /\
       (!b f. (!d. P (f d)) ==> P (iNd b f)) ==>
       !t. P t``,
  SIMP_TAC (srw_ss()) [forall_inftree, iNd_def, iLf_def] THEN
  GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC strong_ind THEN CONJ_TAC THEN1 SRW_TAC [][] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``b:'b``) THEN
  DISCH_THEN (Q.SPEC_THEN `to_inftree o f` MP_TAC) THEN
  SRW_TAC [][fromto_id]);

val (relrec_rules, relrec_ind, relrec_cases) = Hol_reln`
  (!lf nd a. relrec lf nd (iLf a) (lf a)) /\
  (!lf nd b df g. (!d. relrec lf nd (df d) (g d)) ==>
                  relrec lf nd (iNd b df) (nd b g))
`

val relrec_fn = prove(
  ``!lf nd t r1. relrec lf nd t r1 ==> !r2. relrec lf nd t r2 ==> (r1 = r2)``,
  HO_MATCH_MP_TAC relrec_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL [
    ONCE_REWRITE_TAC [relrec_cases] THEN SRW_TAC [][],
    STRIP_TAC THEN ONCE_REWRITE_TAC [relrec_cases] THEN
    SRW_TAC [][] THEN Q_TAC SUFF_TAC `g = g'` THEN1 SRW_TAC [][] THEN
    SRW_TAC [][FUN_EQ_THM]
  ])

val relrec_total = prove(
  ``!t. ?r. relrec lf nd t r``,
  HO_MATCH_MP_TAC inftree_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [relrec_cases] THEN SRW_TAC [][] THEN
  METIS_TAC [])

val inftree_rec_def = Define`
  inftree_rec lf nd t = @r. relrec lf nd t r
`

val inftree_rec_thm = prove(
  ``(inftree_rec lf nd (iLf a) = lf a) /\
    (inftree_rec lf nd (iNd b d) = nd b (inftree_rec lf nd o d))``,
  SRW_TAC [][inftree_rec_def] THEN
  ONCE_REWRITE_TAC [relrec_cases] THEN SRW_TAC [][] THEN
  `inftree_rec lf nd = \t. @r. relrec lf nd t r`
     by (SRW_TAC [][inftree_rec_def, FUN_EQ_THM]) THEN
  SRW_TAC [][combinTheory.o_DEF] THEN POP_ASSUM (K ALL_TAC) THEN
  Q_TAC SUFF_TAC `!g. (!d'. relrec lf nd (d d') (g d')) =
                      (g = \x. @r. relrec lf nd (d x) r)`
        THEN1 SRW_TAC [][] THEN
  SRW_TAC [][FUN_EQ_THM, EQ_IMP_THM] THENL [
    SELECT_ELIM_TAC THEN METIS_TAC [relrec_total, relrec_fn],
    POP_ASSUM (K ALL_TAC) THEN SELECT_ELIM_TAC THEN
    METIS_TAC [relrec_total]
  ])

val inftree_Axiom0 = prove(
  ``!lf nd. ?f : ('a,'b,'c) inftree -> 'd.
       (!a. f (iLf a) = lf a) /\
       (!b d. f (iNd b d) = nd b (f o d))``,
  REPEAT GEN_TAC THEN Q.EXISTS_TAC `inftree_rec lf nd` THEN
  SRW_TAC [][inftree_rec_thm])

val inftree_Axiom = store_thm(
  "inftree_Axiom",
  ``!lf nd. ?f : ('a,'b,'c)inftree -> 'd.
       (!a. f (iLf a) = lf a) /\
       (!b d. f (iNd b d) = nd b d (f o d))``,
  REPEAT GEN_TAC THEN
  Q.SPECL_THEN [`\a. (lf a, iLf a)`,
                 `\b f. (nd b (SND o f) (FST o f), iNd b (SND o f))`]
               STRIP_ASSUME_TAC
               (INST_TYPE [delta |-> ``:'d # ('a,'b,'c)inftree``]
                          inftree_Axiom0) THEN
  Q.EXISTS_TAC `FST o f` THEN
  SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `SND o f o d = d` THEN1 SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `!x. SND (f x) = x` THEN1 SRW_TAC [][FUN_EQ_THM] THEN
  HO_MATCH_MP_TAC inftree_ind THEN SRW_TAC [][FUN_EQ_THM])


val inftree_case_def = new_specification(
  "inftree_case_def",
  ["inftree_case"],
  (SIMP_RULE bool_ss [SKOLEM_THM, FORALL_AND_THM] o Q.GEN `lf` o Q.GEN `nd` o
   SPECL [``lf : 'a -> 'd``,
          ``\ (b:'b) (d:'c -> ('a,'b,'c)inftree) (r:'c->'d). nd b d : 'd``])
  inftree_Axiom)
val _ = export_rewrites ["inftree_case_def"]

val inftree_nchotomy = store_thm(
  "inftree_nchotomy",
  ``!t. (?a. t = iLf a) \/ (?b d. t = iNd b d)``,
  HO_MATCH_MP_TAC inftree_ind THEN SRW_TAC [][]);

val inftree_cong = store_thm(
  "inftree_cong",
  ``!t1 t2 lf nd.
       (t1 = t2) /\ (!a. (t2 = iLf a) ==> (lf a = lf' a)) /\
       (!b d. (t2 = iNd b d) ==> (nd b d = nd' b d)) ==>
       (inftree_case lf nd t1 = inftree_case lf' nd' t2)``,
  SRW_TAC [][] THEN
  Q.SPEC_THEN `t1` FULL_STRUCT_CASES_TAC inftree_nchotomy THEN
  FULL_SIMP_TAC (srw_ss()) [])

val tyinfo = let
  open TypeBasePure
in
  gen_datatype_info { ax = inftree_Axiom,
                      ind = inftree_ind,
                      case_defs = [inftree_case_def]}
end

val _ = export_theory()


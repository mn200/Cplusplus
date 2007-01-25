(* Calculating sizes for types, and offsets for objects within classes *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local
  open wordsTheory integer_wordTheory finite_mapTheory containerTheory
       sortingTheory rich_listTheory dividesTheory
in end

(* C++ ancestor theories  *)
open memoryTheory typesTheory

val _ = new_theory "aggregates";


val _ = Hol_datatype`
  class_constituent = NSD of string => CPP_Type
                    | DBase of CPPname
                    | VirtualBase of CPPname
`;

val cc_case_MONO = store_thm(
  "cc_case_MONO",
  ``(!s ty. nsf s ty ==> nsf' s ty) /\ (!n. bf n ==> bf' n) /\
    (!n. vf n ==> vf' n) ==>
    (class_constituent_case nsf bf vf v ==>
     class_constituent_case nsf' bf' vf' v)``,
  Cases_on `v` THEN SRW_TAC [][]);
val _ = export_mono "cc_case_MONO"

val cc_type_def = Define`
  (cc_type (NSD nm ty) = ty) /\
  (cc_type (VirtualBase cnm) = Class cnm) /\
  (cc_type (DBase cnm) = Class cnm)
`;
val _ = export_rewrites ["cc_type_def"]

val nsdp_def = Define`
  (nsdp (NSD nm ty) = T) /\
  (nsdp _ = F)
`;
val _ = export_rewrites ["nsdp_def"]

val empty_base_size_def = new_specification(
  "empty_base_size_def",
  ["empty_base_size"],
  SIMP_RULE bool_ss [SKOLEM_THM]
  (prove(``?n. 0n <= n``, SRW_TAC [][])))

val empty_base_align_def = new_specification(
  "empty_base_align_def",
  ["empty_base_align"],
  (prove(``?n. 0n <= n /\ n <= empty_base_size``,
         Q.EXISTS_TAC `0` THEN SRW_TAC [][])))


val (empty_class_rules, empty_class_ind, empty_class_cases) = Hol_reln`
  (!cnm.
       EVERY (\cc. case cc of
                      DBase n -> empty_class s F n
                   || VirtualBase n -> empty_class s F n
                   || NSD nm ty -> F)
             (s mdp ' cnm)
   ==>
       empty_class s mdp cnm)
`;

(* SANITY *)
val nil_empty_class = store_thm(
  "nil_empty_class",
  ``(s mdp ' cnm = []) ==> empty_class s mdp cnm``,
  SRW_TAC [][Once empty_class_cases]);

val lcml_def = Define`
  (lcml [] = 1) /\
  (lcml (h::t) = lcm h (lcml t))
`;

val (align_rules, align_ind, align_cases) = Hol_reln`
  (!smap mdp. align smap mdp BChar 1) /\  (* same as Char *)

  (!smap mdp. align smap mdp Bool bool_align) /\

  (!smap mdp ty. align smap mdp (Signed ty) (bit_align ty)) /\

  (!smap mdp ty. align smap mdp (Unsigned ty) (bit_align ty)) /\

   (!smap mdp ty.
     T
   ==>
     align smap mdp (Ptr ty) (ptr_align ty))

   /\

   (!smap mdp ty a.
     align smap mdp ty a
   ==>
     align smap mdp (Const ty) a)

  /\


  (* BAD_ASSUMPTION *)
  (!smap mdp c ty. align smap mdp (MPtr c ty) (ptr_align ty)) /\

  (!smap mdp ty n a. align smap T ty a ==> align smap mdp (Array ty n) a) /\

  (!smap mdp cnm aligns.
      cnm IN FDOM (smap mdp) /\ ~empty_class smap mdp cnm /\
      listRel (cc_align smap) (smap mdp ' cnm) aligns
         ==>
      align smap mdp (Class cnm) (lcml aligns))

   /\

   (!smap mdp cnm.
      cnm IN FDOM (smap mdp) /\ empty_class smap mdp cnm ==>
      align smap mdp (Class cnm) empty_class_align)

   /\


   (!smap nm ty a.
     align smap T ty a
   ==>
     cc_align smap (NSD nm ty) a)

   /\


   (!smap cnm.
     empty_class smap F cnm
   ==>
     cc_align smap (DBase cnm) empty_base_align)

   /\

   (!smap cnm.
     empty_class smap F cnm
   ==>
     cc_align smap (VirtualBase cnm) empty_base_align)

   /\

   (!smap cnm a.
     ~empty_class smap F cnm /\ align smap F (Class cnm) a
   ==>
     cc_align smap (DBase cnm) a)

   /\

   (!smap cnm a.
     ~empty_class smap F cnm /\ align smap F (Class cnm) a
   ==>
     cc_align smap (VirtualBase cnm) a)
`;

(* SANITY : alignment relation is deterministic *)
val align_det = store_thm(
  "align_det",
  ``(!smap mdp ty a. align smap mdp ty a ==>
                     !b. align smap mdp ty b ==> (a = b)) /\
    (!smap cc a. cc_align smap cc a ==> !b. cc_align smap cc b ==> (a = b))``,
  HO_MATCH_MP_TAC align_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  ((Q.MATCH_ABBREV_TAC `align U X Y Z ==> P` THEN
    Q.UNABBREV_ALL_TAC THEN
    ONCE_REWRITE_TAC [align_cases]) ORELSE
   (STRIP_TAC THEN ONCE_REWRITE_TAC [align_cases])) THEN
  SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `aligns = aligns'` THEN1 SRW_TAC [][] THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN
  Q_TAC SUFF_TAC
        `!ccs als. listRel (cc_align smap) ccs als ==>
                   !als'. listRel (\cc a. !b. cc_align smap cc b ==> (a = b))
                                  ccs
                                  als' ==>
                          (als = als')` THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC listTheory.listRel_ind THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [listTheory.listRel_CONS]);

(* SANITY: cc_alignment on NSDs is the same as align *)
val ccalign_NSD = store_thm(
  "ccalign_NSD",
  ``cc_align s (NSD nm ty) a = align s T ty a``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [align_cases])) THEN
  SRW_TAC [][]);
val _ = export_rewrites ["ccalign_NSD"]

(* SANITY *)
val align_int = store_thm(
  "align_int",
  ``(align smap mdp (Signed Int) a = (a = int_align)) /\
    (align smap mdp (Unsigned Int) a = (a = int_align))``,
  ONCE_REWRITE_TAC [align_cases] THEN SRW_TAC [][])
val _ = export_rewrites ["align_int"]

val align_char = store_thm(
  "align_char",
  ``(align smap mdp (Signed Char) a = (a = 1)) /\
    (align smap mdp (Unsigned Char) a = (a = 1)) /\
    (align smap mdp BChar a = (a = 1))``,
  ONCE_REWRITE_TAC [align_cases] THEN SRW_TAC [][])
val _ = export_rewrites ["align_char"]

(* ----------------------------------------------------------------------
    type sizes and field offsets within classes
   ---------------------------------------------------------------------- *)

val roundup_def = Define`
  roundup base n = if n MOD base = 0 then n else (n DIV base + 1) * base
`;



(* sizeof :
     bool -> (bool -> CPPname |-> class_constituent list) -> CPP_Type ->
     num -> bool

   First:  bool indicates whether or not the type is a most-derived class
   Second: bool -> finite-map returns the constituents of a class, the
           boolean is true if the class is "most-derived".
   Third:  type to find size
   Fourth: the size
*)
val (sizeof_rules, sizeof_ind, sizeof_cases) = Hol_reln`

  (!s mdp. sizeof mdp s BChar 1) /\

  (!s mdp. sizeof mdp s Bool bool_size) /\

  (!s b mdp. sizeof mdp s (Signed b) (bit_size b)) /\

  (!s b mdp. sizeof mdp s (Unsigned b) (bit_size b)) /\

  (!s t mdp. sizeof mdp s (Ptr t) (ptr_size t)) /\

  (!s c t mdp. sizeof mdp s (MPtr c t) (ptr_size t)) /\ (* BAD_ASSUMPTION *)

  (!s m n t mdp.
     sizeof mdp s t m
  ==>
     sizeof mdp s (Array t n) (m * n))

  /\

  (!s c mdp cclist a lastoff lastsz.
        c IN FDOM (s mdp) /\
        (cclist = s mdp ' c) /\ ~empty_class s mdp c /\
        align s mdp (Class c) a /\
        offset s cclist (LENGTH cclist - 1) lastoff /\
        ccsizeof s (EL (LENGTH cclist - 1) cclist) lastsz
      ==>
        sizeof mdp s (Class c) (roundup a (lastoff + lastsz)))

  /\

  (!s c mdp.
    c IN FDOM (s mdp) /\ empty_class s mdp c
  ==>
    sizeof mdp s (Class c) empty_class_size)

  /\


  (!s c f.
    c IN FDOM (s F) /\ empty_class s F c /\ ((f = VirtualBase) \/ (f = DBase))
  ==>
    ccsizeof s (f c) empty_base_size)

  /\

  (!f s c sz.
    c IN FDOM (s F) /\ ~empty_class s F c /\
    sizeof F s (Class c) sz /\ ((f = VirtualBase) \/ (f = DBase))
  ==>
    ccsizeof s (f c) sz)

  /\

  (!s nm ty sz.
    sizeof T s ty sz
  ==>
    ccsizeof s (NSD nm ty) sz)

  /\

  (!s cclist.  offset s cclist 0 0) /\
  (!s cclist n a offn sizen.
        offset s cclist n offn /\
        ccsizeof s (EL n cclist) sizen /\
        cc_align s (EL (SUC n) cclist) a
      ==>
        offset s cclist (SUC n) (roundup a (offn + sizen)))
`;


(* SANITY: sizeof and offset are deterministic *)
val det_lemma = prove(
  ``(!mdp s ty n. sizeof mdp s ty n ==> !m. sizeof mdp s ty m ==> (n = m)) /\
    (!s cc n. ccsizeof s cc n ==> !m. ccsizeof s cc m ==> (n = m)) /\
    (!s tylist n off1.
              offset s tylist n off1 ==>
              !off2. offset s tylist n off2 ==> (off1 = off2))``,
  HO_MATCH_MP_TAC sizeof_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  TRY (ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][] THEN NO_TAC)
  THENL [
    (* array *)
    STRIP_TAC THEN ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][] THEN
    METIS_TAC [],
    (* non-empty class size *)
    STRIP_TAC THEN ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [align_det],
    (* empty class size *)
    STRIP_TAC THEN ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][] THEN
    RES_TAC,
    (* cc non-empty base *)
    SRW_TAC [][] THEN POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][] THEN RES_TAC,
    (* cc NSD *)
    STRIP_TAC THEN ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][] THEN
    RES_TAC,
    (* offset SUC *)
    STRIP_TAC THEN ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][] THEN
    METIS_TAC [align_det, listTheory.EL]
  ])
val sizeof_det = save_thm("sizeof_det", CONJUNCT1 det_lemma)
val ccsizeof_det = save_thm("offset_det", CONJUNCT1 (CONJUNCT2 det_lemma))
val offset_det = save_thm("offset_det", CONJUNCT2 (CONJUNCT2 det_lemma))

(* SANITY: only object types have sizes *)
val only_objects_have_sizes = store_thm(
  "only_objects_have_sizes",
  ``!mdp s ty n. sizeof mdp s ty n ==> object_type ty``,
  ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][object_type_def] THEN
  SRW_TAC [][]);

(* SANITY: for example, functions don't have sizes *)
val functions_have_no_size = store_thm(
  "functions_have_no_size",
  ``~sizeof mdp s (Function retty argtys) n``,
  STRIP_TAC THEN IMP_RES_TAC only_objects_have_sizes THEN
  FULL_SIMP_TAC (srw_ss()) [object_type_def])

(* SANITY *)
val ccsizeof_NSD = store_thm(
  "ccsizeof_NSD",
  ``ccsizeof smap (NSD nm ty) sz = sizeof T smap ty sz``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [sizeof_cases])) THEN
  SRW_TAC [boolSimps.DNF_ss][]);
val _ = export_rewrites ["ccsizeof_NSD"]

(* SANITY *)
val sizeof_char = store_thm(
  "sizeof_char",
  ``(sizeof mdp smap (Signed Char) sz = (sz = 1)) /\
    (sizeof mdp smap (Unsigned Char) sz = (sz = 1)) /\
    (sizeof mdp smap BChar sz = (sz = 1))``,
  ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][])
val _ = export_rewrites ["sizeof_char"]

(* SANITY *)
val sizeof_int = store_thm(
  "sizeof_int",
  ``(sizeof mdp smap (Signed Int) sz = (sz = int_size)) /\
    (sizeof mdp smap (Unsigned Int) sz = (sz = int_size))``,
  ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][]);
val _ = export_rewrites ["sizeof_int"]

val offset_0 = store_thm(
  "offset_0",
  ``offset smap els 0 off = (off = 0)``,
  ONCE_REWRITE_TAC [sizeof_cases] THEN SRW_TAC [][]);
val _ = export_rewrites ["offset_0"]


val _ = export_theory();

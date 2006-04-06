(* C++ memory model - principally sections 3.9 and 3.9.1 of the standard *)

(* Michael Norrish *)

(* all bits zero must be a representation of zero *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory
local open wordsTheory in end

(* C++ ancestor theories  *)
open typesTheory

val _ = new_theory "memory";

(* set up the type of bytes - which are words of at least 8 bits width *)
val byte_index_typedef =
  new_type_definition("byte_index",
                      prove(``?n. (\m. m < CHAR_BIT) n``,
                            ASSUME_TAC typesTheory.CHAR_BIT THEN
                            BETA_TAC THEN intLib.ARITH_TAC))

(* prove that the byte_index type is finite *)
val FINITE_byte_index = store_thm(
  "FINITE_byte_index",
  ``FINITE (UNIV : byte_index set)``,
  SRW_TAC [][FINITE_WEAK_ENUMERATE] THEN
  STRIP_ASSUME_TAC (MATCH_MP ABS_REP_THM byte_index_typedef) THEN
  MAP_EVERY Q.EXISTS_TAC [`abs`, `CHAR_BIT`] THEN METIS_TAC []);

(* prove that the byte_index type is in bijection with count CHAR_BIT *)
val byte_index_BIJ_count = store_thm(
  "byte_index_BIJ_count",
  ``?f. BIJ f (UNIV : byte_index set) (count CHAR_BIT)``,
  SRW_TAC [][BIJ_DEF, INJ_DEF, SURJ_DEF, IN_COUNT] THEN
  STRIP_ASSUME_TAC byte_index_typedef THEN
  FULL_SIMP_TAC (srw_ss()) [TYPE_DEFINITION] THEN
  Q.EXISTS_TAC `rep` THEN METIS_TAC []);

(* prove that the size of the byte_index type is CHAR_BIT *)
val dimindex_byte_index = store_thm(
  "dimindex_byte_index",
  ``dimindex (s : byte_index -> bool) = CHAR_BIT``,
  SRW_TAC [][fcpTheory.dimindex, FINITE_byte_index] THEN
  METIS_TAC [FINITE_BIJ_CARD_EQ, FINITE_COUNT, CARD_COUNT, FINITE_byte_index,
             byte_index_BIJ_count]);
val _ = export_rewrites ["dimindex_byte_index"]

(* establish bytes as the word type of length CHAR_BIT *)
val _ = type_abbrev("byte", ``:bool ** byte_index``)

(* 1.7

     "The fundamental storage unit in the C++ memory model is the
      byte.  A byte is at least large enough to contain any member of
      the basic execution character set and is composed of a
      contiguous sequence of bits, the number of which is
      implementation defined [to be CHAR_BIT - MN].  The least
      significant bit is called the low-order bit; the most
      significant is called the high-order bit.  The memory available
      to a C++ program consists of one or more sequences of contiguous
      bytes.  Every byte has a unique address."

*)


(* ----------------------------------------------------------------------
    sizes of integral and pointer types
   ---------------------------------------------------------------------- *)

val two_lemma = prove(
  --`!n. 2 <= n ==> ?m. n = SUC (SUC m)`--,
  REPEAT STRIP_TAC THEN Q.EXISTS_TAC `n - 2` THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []);
val exp_mono_lemma = prove(
  --`!b n. 2 <= b ==> b EXP n < b EXP (n + 1)`--,
  REPEAT STRIP_TAC THEN IMP_RES_TAC two_lemma THEN SRW_TAC [][] THEN
  ASSUME_TAC (SPECL [--`n:num`--, --`m:num`--] LESS_EXP_SUC_MONO) THEN
  FULL_SIMP_TAC (srw_ss()) [ADD1]);
val exp_mono_lemma2 = prove(
  --`!b d x. 2 <= b /\ 0 < d ==> b EXP x < b EXP (x + d)`--,
  Induct_on `d` THEN
  REWRITE_TAC [prim_recTheory.LESS_REFL] THEN
  REPEAT STRIP_TAC THEN
  REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC
    (SPEC (--`d:num`--) num_CASES) THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [exp_mono_lemma, ADD1] THEN
  REWRITE_TAC [DECIDE (--`n + (x + 2n) = (n + (x + 1)) + 1`--)] THEN
  PROVE_TAC [LESS_TRANS, exp_mono_lemma]);
val exp_monotonicity = prove(
  --`!b x y. 2 <= b /\ x < y ==> b EXP x < b EXP y`--,
  REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_ADD_1 THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC exp_mono_lemma2 THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []);
val log_lemma = prove(
  --`!b x. 2 <= b ==> ?n. x <= b EXP n`--,
  Induct_on `x` THEN REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC `0` THEN SIMP_TAC (srw_ss()) [],
    RES_TAC THEN
    IMP_RES_THEN (ASSUME_TAC o SPEC_ALL) exp_mono_lemma THEN
    Q.EXISTS_TAC `SUC n` THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [ADD1]
  ]);
val x_less_CHAR_BIT = prove(
  --`!x. x < 8 ==> x < CHAR_BIT`--,
  ASSUME_TAC CHAR_BIT THEN DECIDE_TAC);
val exp2CB_gt_2 = prove(
  --`2 <= 2 EXP CHAR_BIT`--,
  Q_TAC SUFF_TAC `2 < 2 EXP CHAR_BIT` THEN1 DECIDE_TAC THEN
  MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `2 ** 1` THEN
  CONJ_TAC THEN1 SRW_TAC [][] THEN
  MATCH_MP_TAC exp_monotonicity THEN SIMP_TAC (srw_ss()) [x_less_CHAR_BIT]);

fun size_spec n t = let
  val sz_t = rand (rator (#2 (dest_exists t)))
in
  Rsyntax.new_specification {
    consts = [{const_name = n, fixity = Prefix}],
    name = n,
    sat_thm = prove(t, SIMP_TAC list_ss [integerTheory.INT_EXP] THEN
                       Q.SUBGOAL_THEN `?n. ^sz_t = &n`
                        (CHOOSE_THEN SUBST_ALL_TAC) THENL [
                          PROVE_TAC [integerTheory.NUM_POSINT_EXISTS,
                                     integerTheory.INT_LE_TRANS,
                                     type_size_constants,
                                     integerTheory.INT_LE,
                                     ZERO_LESS_EQ],
                          SIMP_TAC list_ss [integerTheory.INT_LE,
                                           log_lemma, exp2CB_gt_2]
                       ])}
end;
val short_size = size_spec "short_size"
  (--`?x. USHRT_MAX <= (2 ** CHAR_BIT) ** x`--);
val int_size = size_spec "int_size"
  (--`?x. UINT_MAX <= (2 ** CHAR_BIT) ** x`--);
val long_size = size_spec "long_size"
  (--`?x. ULONG_MAX <= (2 ** CHAR_BIT) ** x`--);

(* bit = "basic integral type" here *)
val bit_size = Define`
  (bit_size Char = 1) /\ (bit_size Short = short_size) /\
  (bit_size Int = int_size) /\ (bit_size Long = long_size)
`;
val ptr_size = Rsyntax.new_specification {
  consts = [{const_name = "voidptr_size", fixity = Prefix},
            {const_name = "ptr_size", fixity = Prefix}],
  name = "ptr_size",
  sat_thm = CONV_RULE (QUANT_CONV SKOLEM_CONV) (prove(
    --`?v. !t. ?x.
          ((t = Unsigned Char) \/ (t = Signed Char) \/
           (t = Void) ==> (x = v)) /\ 1n <= x /\ x <= v`--,
    Q.EXISTS_TAC `1` THEN GEN_TAC THEN Q.EXISTS_TAC `1` THEN
    SIMP_TAC list_ss []))};
(* val ptr_size = Rsyntax.new_specification {
  consts = [{const_name = "ptr_size", fixity = Prefix}],
  name = "ptr_size",
  sat_thm = prove(--`?x. 1n <= x`--, SIMP_TAC hol_ss [LESS_OR_EQ])}; *)

val int_size_def = Define`
  (int_size (Signed x) = bit_size x) /\
  (int_size (Unsigned x) = bit_size x) /\
  (int_size BChar = 1)
`;

(* There are a few encoding functions required to turn bytes from
   memory into real values that can be manipulated.  The domain of the
   function will always be byte list, but the range will differ,
   depending on the desired type.

   Values don't always need to be manipulated (i.e., have
   value-dependent operations performed upon them).  Often they can
   just be copied around.  This is what happens to POD-structs, for
   example.

   Integral types (whether signed, or unsigned) will map into
   integers.

   Floating types will map into reals (probably - modelling just what
   reals are representable might be a pain).

   Ptr types (pointers to objects) will map into natural numbers (the
   byte address).

   Ptr types (pointers to functions) will map into
   ((qualified) function) names.

   MPtr types will map into (field) names.  This will be OK because
   such pointers can only be dereferenced in a scope where the class
   name and the associated member defintions are accessible.

   ----------------------------------------------------------------------
   Properties of the Integral Valuation
   ----------------------------------------------------------------------

   int_value : CPP_Type -> byte list -> int option
   rep_int   : CPP_Type -> int -> byte list option

      int_value (Unsigned Char) [b] = SOME (int_of_num (w2n b))
      rep_int   (Unsigned Char) i   =
           SOME (n2w (Num (i % int_of_num UCHAR_MAX)))

      ~word_msb b ==>
         (int_value (Signed Char) [b] = int_value (Unsigned Char) [b])

      word_msb b ==>
         ?i. int_value (Signed Char) [b] = SOME i /\
             SCHAR_MIN <= i /\ i <= 0

      rep_int (Signed Char) (THE (int_value (Signed Char) [b])) = SOME [b]

      SCHAR_MIN <= i /\ i <= SCHAR_MAX ==>
        int_value (Signed Char) (THE (rep_int (Signed Char) i)) = SOME i


      int_value BChar [b] = if BCHAR_IS_SIGNED then
                              int_value (Signed Char) [b]
                            else
                              int_value (Unsigned Char) [b]

      LENGTH bytes = sizeof ty /\ integral_type ty /\
      SOME i = int_value ty bytes ==>
         type_min ty <= i /\ i <= type_max ty

      integral_type ty /\ type_min ty <= i /\ i <= type_max ty ==>
        ?rep. rep_int ty i = SOME rep /\ LENGTH rep = sizeof ty /\
              int_value ty rep = SOME i
*)


(* show that rep_int and int_value functions of the desired behaviours
   exist *)

val int_representation = prove(
  ``?rep_int int_value.
       (!b:byte. int_value (Unsigned Char) [b] = SOME (int_of_num (w2n b))) /\
       (!i. rep_int (Unsigned Char) i =
              SOME (n2w (Num (i % UCHAR_MAX)))) /\
       (!b. ~word_msb b ==>
            (int_value (Signed Char) [b] = int_value (Unsigned Char) [b])) /\
       (!b. word_msb b ==>
               ?i. (int_value (Signed Char) [b] = SOME i) /\
                   SCAHR_MIN <= i /\ i <= 0)``,






val (sizeof_rules, sizeof_induction, sizeof_cases) =
  IndDefLib.Hol_reln`

(* \#line cholera-model.nw 1088 *)
(!s b. sizeof s (INL (Signed b)) (bit_size b)) /\
(!s b. sizeof s (INL (Unsigned b)) (bit_size b)) /\
(!s t. sizeof s (INL (Ptr t)) ptr_size) /\
(!s ret args. sizeof s (INL (Function ret args)) fnptr_size)
(* \#line cholera-model.nw 1046 *)
                                       /\

(* \#line cholera-model.nw 1099 *)
(!s. sizeof s (INR []) 0) /\
(!s hdt tlt hds tls.
      sizeof s (INL hdt) hds /\
      sizeof s (INR tlt) tls ==>
      sizeof s (INR (hdt :: tlt)) (hds + tls))
(* \#line cholera-model.nw 1047 *)
                                       /\

(* \#line cholera-model.nw 1110 *)
(!s t tsize n. sizeof s (INL t) tsize ==>
               sizeof s (INL (Array t n)) (tsize * n))
(* \#line cholera-model.nw 1048 *)
                                       /\

(* \#line cholera-model.nw 1122 *)
(!s name sz.
    sizeof s (INR (MAP SND (s name).struct_info)) sz ==>
    sizeof s (INL (Struct name)) sz)
(* \#line cholera-model.nw 1049 *)
                                        `
(* \#line cholera-model.nw 1132 *)
val (sizeof_rewrites0, _) = install_indrel {
  cases_thm = sizeof_cases,
  name    = "sizeof",
  ind_thm = sizeof_induction,
  position = 2
};
val sizeof_rewrites = save_thm(
  "sizeof_rewrites",
  LIST_CONJ sizeof_rewrites0);
(* \#line cholera-model.nw 1051 *)
local
  val myth = DB.fetch "choltype"
  open choltypeTheory
  val gsz_goal = prove(
    --`!t. ?n. !s.
         ((?b. t = Unsigned b) \/ (?b. t = Signed b) \/
          (?t'. t = Ptr t') \/ (?t' lst. t = Function t' lst)) ==>
         sizeof s (INL t) n`--,
    GEN_TAC THEN CONV_TAC EX_OUT_CONV THEN
    REWRITE_TAC [DISJ_IMP_THM] THEN
    STRUCT_CASES_TAC (Q.SPEC `t` CType_nchotomy) THEN
    SIMP_TAC hol_ss [sizeof_rewrites, GSYM CType_distinct, CType_11,
                     CType_distinct]);
in
  val gsizeof = Rsyntax.new_specification {
    consts = [{const_name = "gsizeof", fixity = Prefix}],
    name   = "gsizeof",
    sat_thm = CONV_RULE SKOLEM_CONV gsz_goal}
end;
val gsizeof_THM = store_thm(
  "gsizeof_THM",
  --`!b t tlst.
        (gsizeof (Unsigned b) = bit_size b) /\
        (gsizeof (Signed b) = bit_size b) /\
        (gsizeof (Ptr t) = ptr_size) /\
        (gsizeof (Function t tlst) = fnptr_size)`--,
  REPEAT STRIP_TAC THENL (map (fn t =>
    ACCEPT_TAC (SIMP_RULE hol_ss [
      sizeof_rewrites,choltypeTheory.CType_11
    ] (SPEC t gsizeof))) [--`Unsigned b`--, --`Signed b`--,
      --`Ptr t`--, --`Function t tlst`--]));
(* \#line cholera-model.nw 1148 *)
val sizeof_det_lemma = prove(
  --`sizeof s t n ==> (\s t n.
                         !n'. sizeof s t n' ==> (n' = n)) s t n`--,
  MATCH_MP_TAC sizeof_induction THEN SIMP_TAC hol_ss [] THEN
  ONCE_REWRITE_TAC [sizeof_rewrites] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN ASM_SIMP_TAC hol_ss []);
val sizeof_det =
  save_thm("sizeof_det", GEN_ALL (SIMP_RULE hol_ss [] sizeof_det_lemma));
(* \#line cholera-model.nw 1168 *)
val declarable_type = new_definition (
  "declarable_type",
  ``declarable_type s t = ?n. sizeof s (INL t) n /\ ~(n = 0)``);
(* \#line cholera-model.nw 1181 *)
val (offset'_rules, offset'_induction, offset'_cases) = IndDefLib.Hol_reln`
    (!s n t rest. offset' s (CONS (n,t) rest) n 0n) /\
    (!s rest n off fsize x xt.
         sizeof s (INL xt) fsize /\ ~(n = x) /\
         offset' s rest n off ==>
         offset' s ((x,xt)::rest) n (fsize + off))`;
val offset = new_definition (
  "offset",
  (--`offset s stid fld off =
         offset' s (s stid).struct_info fld off`--));
val (offset'_rewrites, _) = install_indrel {
  name = "offset'", ind_thm = definition "offset'",
  position = 2,
  cases_thm = offset'_cases
};
val offset'_rewrites = save_thm(
  "offset'_rewrites",
  LIST_CONJ offset'_rewrites);
val offset'_det = prove(
  --`!s l fld n. offset' s l fld n ==>
                 (!n'. offset' s l fld n' ==> (n' = n))`--,
  HO_MATCH_MP_TAC offset'_induction THEN
  SIMP_TAC hol_ss [offset'_rewrites] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN IMP_RES_TAC sizeof_det THEN
  ELIM_TAC THEN RWT);
val offset_det = store_thm (
  "offset_det",
  --`!s i fld n. offset s i fld n ==>
                 !n'. offset s i fld n' ==> (n' = n)`--,
  SIMP_TAC hol_ss [offset] THEN PROVE_TAC [offset'_det]);
(* \#line cholera-model.nw 1221 *)
val wf_type_sizeof = prove(
  ``!smap vstd t.
       wf_type smap vstd t ==> ~(t = Void) ==>
       ?n. sizeof smap (INL t) n``,
  HO_MATCH_MP_TAC (choltypeTheory.wf_type_strong_induction) THEN
  SIMP_TAC hol_ss [choltypeTheory.CType_11,
                    choltypeTheory.CType_distinct] THEN
  ONCE_REWRITE_TAC [sizeof_rewrites] THEN
  SIMP_TAC hol_ss [choltypeTheory.str_info_struct_info] THEN
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC
    (Q.SPEC `smap (sn:string)` (choltypeTheory.str_info_nchotomy)) THEN
  FULL_SIMP_TAC hol_ss [choltypeTheory.str_info_struct_info] THEN
  POP_ASSUM_LIST (MAP_EVERY (fn th =>
    if (free_in ``str_info`` (concl th) orelse
        free_in ``[]:(string # CType) list`` (concl th)) then
       ALL_TAC
    else
       MP_TAC th)) THEN
  MAP_EVERY (dub >- SPEC_TAC) [``vstd:string->bool``,
                               ``l:(string # CType) list``] THEN
  INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THEN
  SIMP_TAC hol_ss [sizeof_rewrites] THEN ASM_MESON_TAC []);

val well_formed_type_sizeof = store_thm(
  "well_formed_type_sizeof",
  ``!smap t.
        well_formed_type smap t ==>
        ~(t = Void) ==>
        ?n. sizeof smap (INL t) n``,
  MESON_TAC [choltypeTheory.well_formed_type, wf_type_sizeof]);
val sizeof_fn_DEF = Rsyntax.new_specification {
  consts = [{const_name = "sizeof_fn", fixity = Prefix}],
  name = "sizeof_fn_DEF",
  sat_thm = CONV_RULE (rmove_out ``n:num`` THENC SKOLEM_CONV)
                      well_formed_type_sizeof};
(* \#line cholera-model.nw 1263 *)
val ctype_11 = choltypeTheory.CType_11
val ctype_distinct = let val t = choltypeTheory.CType_distinct
                     in  CONJ t (GSYM t) end;
val wf_type_rewrites = choltypeTheory.wf_type_rewrites
val well_formed_type_THM = choltypeTheory.well_formed_type_THM
fun start_off (asl, g) =
  let val lhs_term = lhs g
      val (_, [smap,cty]) = strip_comb lhs_term
  in
      MP_TAC (SPECL [smap, cty] sizeof_fn_DEF) THEN
      SIMP_TAC hol_ss [ctype_distinct, well_formed_type_THM] THEN
      ONCE_REWRITE_TAC [sizeof_rewrites, well_formed_type_THM] THEN
      ASM_SIMP_TAC hol_ss []
  end (asl, g)
val ptr_rewrite = prove(
  ``!smap pt.
      well_formed_type smap pt ==>
      (sizeof_fn smap (Ptr pt) = ptr_size)``,
  REPEAT STRIP_TAC THEN start_off THEN
  FULL_SIMP_TAC hol_ss [well_formed_type_THM]);
val num_rewrite = prove(
  ``(!smap bt. sizeof_fn smap (Signed bt) = bit_size bt) /\
    (!smap bt. sizeof_fn smap (Unsigned bt) = bit_size bt)``,
  REPEAT STRIP_TAC THEN start_off);
val fnptr_rewrite = prove(
  ``!smap f args.
       well_formed_type smap f /\ ~array_type f /\
       EVERY (\t. well_formed_type smap t /\ ~(t = Void) /\
                  ~array_type t) args ==>
       (sizeof_fn smap (Function f args) = fnptr_size)``,
  REPEAT STRIP_TAC THEN start_off THEN
  FULL_SIMP_TAC hol_ss [well_formed_type_THM, EVERY_MEM]);
(* \#line cholera-model.nw 1300 *)
val array_rewrite = prove(
  ``!smap bt n.
       well_formed_type smap bt /\ ~(bt = Void) /\ ~(n = 0) ==>
       (sizeof_fn smap (Array bt n) = n * sizeof_fn smap bt)``,
  REPEAT STRIP_TAC THEN start_off THEN IMP_RES_TAC sizeof_fn_DEF THEN
  FULL_SIMP_TAC hol_ss [well_formed_type_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC hol_ss [EQ_MULT_LCANCEL] THEN
  IMP_RES_TAC sizeof_det);
(* \#line cholera-model.nw 1315 *)
val struct_rewrite = prove(
  ``!smap sn.
       well_formed_type smap (Struct sn) ==>
       (sizeof_fn smap (Struct sn) =
          FOLDR (\x y. sizeof_fn smap x + y)
                0
                (MAP SND (smap sn).struct_info))``,
  REPEAT GEN_TAC THEN DISCH_THEN (fn th =>
    MP_TAC th THEN
    MP_TAC (MATCH_MP (REWRITE_RULE [GSYM IMP2_THM] sizeof_fn_DEF) th))
  THEN SIMP_TAC hol_ss [ctype_distinct] THEN
  ONCE_REWRITE_TAC [sizeof_rewrites] THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC hol_ss [choltypeTheory.str_info_struct_info,
                         well_formed_type_THM,
                         pred_setTheory.NOT_IN_EMPTY] THEN
  POP_ASSUM_LIST (MAP_EVERY (fn th =>
    if (free_in ``nodup_flds`` (concl th) orelse
        free_in ``[]:(string # CType) list`` (concl th) orelse
        free_in ``wf_type`` (concl th)) then
       ALL_TAC
    else MP_TAC th)) THEN
  SPEC_TAC (``sizeof_fn smap (Struct sn)``, ``n:num``) THEN
  REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC
    (Q.SPEC `smap (sn:string)`
           (choltypeTheory.str_info_nchotomy)) THEN
  SIMP_TAC hol_ss [choltypeTheory.str_info_struct_info] THEN
  SPEC_TAC (dub ``l:(string # CType) list``) THEN
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL [
    SIMP_TAC hol_ss [sizeof_rewrites],
    SIMP_TAC hol_ss [sizeof_rewrites, well_formed_type_THM,
                      DISJ_IMP_THM, FORALL_AND_THM] THEN
    REPEAT STRIP_TAC THEN IMP_RES_TAC sizeof_fn_DEF THEN
    POP_ASSUM (GSYM >- ASSUME_TAC) THEN
    FIRST_X_ASSUM (res_search false [] []) THEN
    res_search_then true [] [] SUBST_ALL_TAC sizeof_det THEN
    ELIM_TAC THEN FULL_SIMP_TAC hol_ss [sizeof_rewrites]
  ]);
(* \#line cholera-model.nw 1358 *)
val sizeof_fn = save_thm(
  "sizeof_fn",
  LIST_CONJ [num_rewrite, ptr_rewrite, fnptr_rewrite, struct_rewrite,
             array_rewrite]);
(* \#line cholera-model.nw 1368 *)
val wf_type_offset = store_thm(
  "wf_type_offset",
  ``!smap sn. well_formed_type smap (Struct sn) ==>
              !fld t. lookup_field_info (smap sn) fld t ==>
                      ?n. offset smap sn fld n``,
  SIMP_TAC (hol_ss ++ impnorm_set) [offset,
    choltypeTheory.lookup_field_info,
    choltypeTheory.str_info_struct_info] THEN
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC (choltypeTheory.well_formed_structs) THEN
  FULL_SIMP_TAC hol_ss [well_formed_type_THM] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FULL_SIMP_TAC hol_ss [choltypeTheory.str_info_struct_info] THEN
  POP_ASSUM_LIST (MAP_EVERY (fn th =>
    if (free_in ``nodup_flds`` (concl th) orelse
        free_in ``[]:(string # CType) list`` (concl th)) then
       ALL_TAC
    else MP_TAC th)) THEN
  SPEC_TAC (dub ``l:(string # CType) list``) THEN
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN SIMP_TAC hol_ss [] THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC ``h:string # CType`` pair_CASES) THEN
  SIMP_TAC hol_ss [DISJ_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
                   FORALL_AND_THM] THEN
  ONCE_REWRITE_TAC [offset'_rewrites] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC [well_formed_type_sizeof]);
(* \#line cholera-model.nw 1402 *)
val bit_cases = choltypeTheory.basic_integral_type_nchotomy
val bit_size_nonzero = store_thm(
  "bit_size_nonzero",
  --`!b. ~(bit_size b = 0)`--,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `b` bit_cases) THEN
  SIMP_TAC hol_ss [bit_size] THEN
  STRIP_ASSUME_TAC (choltypeTheory.type_size_constants) THENL
  (map (fn th =>
    ASSUME_TAC th THEN STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC hol_ss [integerTheory.INT_EXP_CALCULATE] THEN
    POP_ASSUM (fn th =>
       Q.PAT_ASSUM `^(rand (rator (concl th))) = X`
         (fn th2 => ASSUME_TAC th THEN SUBST_ALL_TAC th2)) THEN
    IMP_RES_THEN IMP_RES_TAC integerTheory.INT_LE_TRANS THEN
    FULL_SIMP_TAC (hol_ss ++ intSimps.INT_REDUCE_ss) [])
   [short_size, int_size, long_size]));
(* \#line cholera-model.nw 1421 *)
val simple_arith = ARITH_PROVE (--`!c:num. 1 <= c ==> ~(c = 0)`--)
val sizeof_not_zero_lemma = prove(
  ``!smap x n.
       sizeof smap x n ==>
       (!t. (x = INL t) ==> well_formed_type smap t ==>
            ~(t = Void) ==> ~(n = 0)) /\
       (!tl. (x = INR tl) ==> ~(tl = []) ==>
             EVERY (well_formed_type smap) tl ==>
             EVERY ($~ o $= Void) tl ==> ~(n = 0))``,
  HO_MATCH_MP_TAC sizeof_induction THEN
  REPEAT CONJ_TAC THEN SIMP_TAC hol_ss [ctype_distinct,
    sizeof_rewrites, bit_size_nonzero, ptr_size, simple_arith,
    fnptr_size, combinTheory.o_THM]
  THENL [
    SIMP_TAC hol_ss [well_formed_type_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC
      (Q.SPEC `n` num_CASES) THEN
    FULL_SIMP_TAC hol_ss [RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB,
                           MULT_CLAUSES] THEN
    STRIP_TAC THEN RES_TAC THEN FULL_SIMP_TAC hol_ss [],
    SIMP_TAC hol_ss [EVERY_MEM, EXISTS_MEM, combinTheory.o_THM] THEN
    REPEAT STRIP_TAC THEN IMP_RES_TAC (choltypeTheory.well_formed_structs) THEN
    FULL_SIMP_TAC hol_ss [well_formed_type_THM]
  ]);
val sizeof_not_zero = save_thm(
  "sizeof_not_zero",
  CONJUNCT1 (SIMP_RULE (hol_ss ++ impnorm_set) [
      GSYM RIGHT_FORALL_IMP_THM, FORALL_AND_THM]
  sizeof_not_zero_lemma));
val sizeof_fn_not_zero = store_thm(
  "sizeof_fn_not_zero",
  ``!smap t. well_formed_type smap t /\ ~(t = Void) ==>
             ~(sizeof_fn smap t = 0)``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC sizeof_fn_DEF THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC [sizeof_not_zero]);
(* \#line cholera-model.nw 1481 *)
val convert_unsigned = new_definition (
  "convert_unsigned",
  --`convert_unsigned (v:MemObj list) t1 t2 =
       let len1 = gsizeof t1 in
       let len2 = gsizeof t2 in
         (len1 > len2 => LASTN len2 v
                      |  APPEND (num2mval (len2 - len1) 0) v)`--);
val convert_unsigned_same_types = store_thm(
  "convert_unsigned_same_types",
  ``!v t1. convert_unsigned v t1 t1 = v``,
  SIMP_TAC hol_ss [LET_THM, convert_unsigned, num2mval, split2bytes]);
val bit_less_than = new_definition (
  "bit_less_than",
  ``bit_less_than bt1 bt2 =
      (bt1 = Char) /\ ~(bt2 = Char) \/
      (bt1 = Short) /\ ~(bt2 IN {Char; Short}) \/
      (bt1 = Int) /\ (bt2 = Long)``);
val convert_signed2unsigned = new_definition(
  "convert_signed2unsigned",
  ``convert_signed2unsigned (v1, bt1) (v2, bt2) =
      ?n. n < 2 EXP (CHAR_BIT * bit_size bt1) /\
          (v1 = num2mval (bit_size bt1) n) /\
          (v2 = num2mval (bit_size bt2) n)``);
val convert_val = new_definition (
  "convert_val",
  --`convert_val s (v1, t1) (v2, t2) =
       (sizeof s (INL t1) (LENGTH v1) \/ (t1 = Void) /\ (v1 = [])) /\
       ((?bt. t1 = Unsigned bt) /\ (?bt. t2 = Unsigned bt) /\
        (v2 = convert_unsigned v1 t1 t2) \/
        (?bt1 bt2. (t1 = Signed bt1) /\ (t2 = Unsigned bt2) /\
                   convert_signed2unsigned (v1, bt1) (v2, bt2)) \/
        pointer_type t1 /\ pointer_type t2 /\ (v2 = v1) \/
        (t1 = t2) /\ (v2 = v1) \/
        (t2 = Void) /\ (v2 = []))`--);
(* \#line cholera-model.nw 1526 *)
val RES_FORALL = res_quanTheory.RES_FORALL
val len_split2bytes = store_thm(
  "len_split2bytes",
  --`!n w:'a word. LENGTH (split2bytes n w) = n`--,
  numLib.INDUCT_TAC THEN
  ASM_SIMP_TAC hol_ss [split2bytes, rich_listTheory.LENGTH_SNOC]);
val len_num2mval = store_thm(
  "len_num2mval",
  --`!l n. LENGTH (num2mval l n) = l`--,
  numLib.INDUCT_TAC THEN ASM_SIMP_TAC hol_ss [num2mval, len_split2bytes]);
val FOLDL_MAP = prove(
  (--`!(f:'a->'b->'a) (g:'c->'b) l e.
         FOLDL f e (MAP g l) = FOLDL (\x y. f x (g y)) e l`--),
  REPEATN 2 GEN_TAC THEN SingleStep.Induct THEN
  ASM_SIMP_TAC hol_ss []);
val BNVAL_WCAT =
  CONV_RULE (SIMP_CONV hol_ss [word_baseTheory.PWORDLEN, RES_FORALL])
            bword_numTheory.BNVAL_WCAT
open SingleStep
infix 8 by
infix |->
val LESS_DIV = prove(
  (--`!x y z. 0 < y /\ x < y * z ==> x DIV y < z`--),
  REPEAT STRIP_TAC THEN
  `~(y = 0)` by ASM_SIMP_TAC hol_ss [] THEN
  POP_ASSUM (fn th =>
    `?n. y = SUC n` by ASM_MESON_TAC [arithmeticTheory.num_CASES, th]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC (K (SYM (INST
                      [(--`m:num`--) |-> (--`x DIV (SUC n)`--),
                       (--`i:num`--) |-> (--`z:num`--)]
                    (SPEC_ALL arithmeticTheory.LESS_MULT_MONO)))) THEN
  CONV_TAC (arg_CONV 1 (REWR_CONV arithmeticTheory.MULT_SYM)) THEN
  ASSUME_TAC (CONJUNCT1 (SPEC (--`x:num`--)
                        (MATCH_MP DIVISION
                                  (ASSUME (--`0 < SUC n`--))))) THEN
  IMP_RES_TAC (ARITH_PROVE (--`(x:num = y + z) ==> (y <= x)`--)) THEN
  POP_ASSUM (STRIP_ASSUME_TAC o
             REWRITE_RULE [arithmeticTheory.LESS_OR_EQ]) THENL [
    ASM_MESON_TAC [arithmeticTheory.LESS_TRANS],
    ASM_SIMP_TAC hol_ss []
  ]);
val WSPLIT_WCAT = prove(
  (--`!x y n. (WORDLEN (x:'a word) = n) ==>
              (WSPLIT n (WCAT(y,x)) = (y,x))`--),
  REPEAT GEN_TAC THEN
  MAP_EVERY (fn t => REPEAT_TCL STRIP_THM_THEN SUBST1_TAC
                     (ISPEC t word_baseTheory.word_cases))
            [(--`x:'a word`--), (--`y:'a word`--)] THEN
  let open wordTheory word_baseTheory
  in
    REWRITE_TAC [WORDLEN_DEF, WCAT_DEF, WSPLIT_DEF, PAIR_EQ, WORD_11]
  end THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC (ARITH_PROVE (--`(x = n:num) ==> (x <= n)`--)) THENL [
    ASM_SIMP_TAC hol_ss [rich_listTheory.BUTLASTN_APPEND1,
                         rich_listTheory.BUTLASTN],
    ASM_SIMP_TAC hol_ss [rich_listTheory.LASTN_APPEND1,
                         rich_listTheory.LASTN]
  ]);
val mult_over_add = prove(
  (--`(!x:num y z. x * (y + z) = x * y + x * z) /\
      (!x:num y z. (y + z) * x = x * y + x * z)`--),
  CONV_TAC (conj2_CONV (STRIP_QUANT_CONV (lhs_CONV
    (REWR_CONV (arithmeticTheory.MULT_SYM))))) THEN RWT THEN
  numLib.INDUCT_TAC THENL [
    REWRITE_TAC [arithmeticTheory.ADD_CLAUSES, arithmeticTheory.MULT_CLAUSES],
    ONCE_REWRITE_TAC [arithmeticTheory.MULT_SYM] THEN
    REWRITE_TAC [arithmeticTheory.MULT_SUC] THEN
    ONCE_REWRITE_TAC [arithmeticTheory.MULT_SYM] THEN ARWT THEN
    REPEAT GEN_TAC THEN CONV_TAC ARITH_CONV
  ]);
val two_exp_gt_zero = prove(
  ``!n. 0 < 2 EXP n``,
  SIMP_TAC hol_ss [ARITH_PROVE ``0n < n = ~(n = 0)``] THEN
  REWRITE_TAC [ARITH_PROVE ``2 = SUC 1``, NOT_EXP_0])
local
  open bword_numTheory
  val BNVAL_WCAT =
    CONV_RULE (SIMP_CONV hol_ss [word_baseTheory.PWORDLEN, RES_FORALL])
               bword_numTheory.BNVAL_WCAT
in
  val num2mval_safe = store_thm(
    "num2mval_safe",
    ``!nb n. (n < 2 EXP (CHAR_BIT * nb)) ==>
               (coerce_to_num (num2mval nb n) = n)``,
    SIMP_TAC hol_ss [coerce_to_num, num2mval, obj2byte, FOLDL_MAP,
                     pairTheory.CURRY_DEF] THEN Induct
    THENL [
      SIMP_TAC hol_ss [MULT_CLAUSES] THEN REPEAT STRIP_TAC THEN
      IMP_RES_TAC (ARITH_PROVE (--`n < 1n ==> (n = 0)`--)) THEN
      ELIM_TAC THEN SIMP_TAC hol_ss [split2bytes,
                                     bword_numTheory.BNVAL0],
      SIMP_TAC bool_ss [MULT_CLAUSES, NBWORD_SPLIT, WSPLIT_WCAT,
                        WORDLEN_NBWORD, split2bytes] THEN
      SIMP_TAC hol_ss [rich_listTheory.FOLDL_SNOC, BNVAL_WCAT] THEN
      ONCE_REWRITE_TAC [
        GSYM (SPEC ``CHAR_BIT`` bword_numTheory.NBWORD_MOD)] THEN
      SIMP_TAC hol_ss [bword_numTheory.BNVAL_NBWORD, DIVISION, two_exp_gt_zero,
                       arithmeticTheory.EXP_ADD] THEN
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC hol_ss [LESS_DIV, two_exp_gt_zero, WORDLEN_NBWORD] THEN
      SYM_TAC THEN
      ACCEPT_TAC (CONJUNCT1
        (SPEC ``n:num``
              (MATCH_MP DIVISION (SPEC ``CHAR_BIT`` two_exp_gt_zero))))
    ])
end;
(* \#line cholera-model.nw 1639 *)
val convert_val_det = store_thm(
  "convert_val_det",
  ``!s v1 t1 v2 t2.
          convert_val s (v1, t1) (v2, t2) ==>
          !v'. convert_val s (v1, t1) (v', t2) ==> (v' = v2)``,
  SIMP_TAC hol_ss [convert_val] THEN REPEAT STRIP_TAC THEN
  ELIM_TAC THEN FULL_SIMP_TAC hol_ss [
    choltypeTheory.pointer_type, convert_unsigned_same_types,
    convert_signed2unsigned, pred_setTheory.IN_INSERT,
    pred_setTheory.NOT_IN_EMPTY, choltypeTheory.CType_11,
    choltypeTheory.CType_distinct] THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [sizeof_cases]) THEN
  FULL_SIMP_TAC hol_ss [choltypeTheory.CType_distinct,
                         choltypeTheory.CType_11] THEN
  ELIM_TAC THEN ARWT THEN
  FIRST_X_ASSUM (AP_TERM ``coerce_to_num`` >- MP_TAC) THEN
  ASM_SIMP_TAC hol_ss [num2mval_safe]);
val convert_preserves_sizes = store_thm(
  "convert_preserves_sizes",
  --`!vt v2 t2 s. convert_val s vt (v2, t2) ==> ~(t2 = Void) ==>
                  sizeof s (INL t2) (LENGTH v2)`--,
  REPEAT GEN_TAC THEN CONV_TAC (ant_CONV (arg_CONV 2 pair_CONV)) THEN
  SIMP_TAC hol_ss [convert_val] THEN REPEAT STRIP_TAC THEN
  ELIM_TAC THEN FULL_SIMP_TAC hol_ss [] THENL [
    FULL_SIMP_TAC hol_ss [
      sizeof_rewrites, convert_unsigned, gsizeof_THM, LET_THM] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC hol_ss [
      rich_listTheory.LENGTH_LASTN, LENGTH_APPEND, len_num2mval],
    FULL_SIMP_TAC hol_ss [convert_signed2unsigned, len_num2mval,
                           sizeof_rewrites],
    FULL_SIMP_TAC hol_ss [choltypeTheory.pointer_type,
      sizeof_rewrites] THEN ELIM_TAC THEN
    FIRST_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC hol_ss [sizeof_rewrites],
    FULL_SIMP_TAC hol_ss [choltypeTheory.CType_distinct],
    FULL_SIMP_TAC hol_ss [convert_signed2unsigned, len_num2mval,
                           sizeof_rewrites],
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    FULL_SIMP_TAC hol_ss [choltypeTheory.CType_distinct,
      choltypeTheory.pointer_type]
  ]);
(* \#line cholera-model.nw 713 *)
val _ = export_theory();

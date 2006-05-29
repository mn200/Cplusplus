(* C++ memory model - principally sections 3.9 and 3.9.1 of the standard *)

(* Michael Norrish *)

(* NOTE: all bits zero must be a representation of zero *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

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

open logrootTheory
val log_lemma = prove(
  ``!b x. 2 <= b ==> ?n. x <= b EXP n``,
  REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `SUC(LOG b x)` THEN
  Cases_on `x = 0` THEN1 SRW_TAC [][] THEN
  ASSUME_TAC (Q.SPECL [`b`, `x`] LOG) THEN
  DECIDE_TAC)
val x_less_CHAR_BIT = prove(
  --`!x. x < 8 ==> x < CHAR_BIT`--,
  ASSUME_TAC CHAR_BIT THEN DECIDE_TAC);
val exp2CB_gt_2 = prove(
  --`2 <= 2 EXP CHAR_BIT`--,
  Q_TAC SUFF_TAC `1 <= CHAR_BIT` THEN1
    METIS_TAC [EXP_BASE_LE_MONO, DECIDE ``1n < 2``, EXP_1] THEN
  ASSUME_TAC x_less_CHAR_BIT THEN intLib.ARITH_TAC)

fun size_spec n t = let
  val sz_t = rand (rator (#2 (dest_exists t)))
in
  Rsyntax.new_specification {
    consts = [{const_name = n, fixity = Prefix}],
    name = n,
    sat_thm = prove(t, SIMP_TAC list_ss [INT_EXP] THEN
                       Q.SUBGOAL_THEN `?n. ^sz_t = &n`
                        (CHOOSE_THEN SUBST_ALL_TAC) THENL [
                          PROVE_TAC [NUM_POSINT_EXISTS, INT_LE_TRANS,
                                     type_size_constants, INT_LE,
                                     ZERO_LESS_EQ],
                          SIMP_TAC list_ss [INT_LE, log_lemma, exp2CB_gt_2]
                       ])}
end;
val short_size = size_spec "short_size"
  (--`?x. USHRT_MAX <= (2 ** CHAR_BIT) ** x`--);
val short_size_nonzero = store_thm(
  "short_size_nonzero",
  ``0 < short_size``,
  Q_TAC SUFF_TAC `~(short_size = 0)` THEN1 DECIDE_TAC THEN
  ASSUME_TAC short_size THEN STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [EXP] THEN
  `65535 <= USHRT_MAX` by SRW_TAC [][type_size_constants] THEN
  intLib.ARITH_TAC)

val int_size = size_spec "int_size"
  (--`?x. UINT_MAX <= (2 ** CHAR_BIT) ** x`--);
val int_size_nonzero = store_thm(
  "int_size_nonzero",
  ``0 < int_size``,
  Q_TAC SUFF_TAC `~(int_size = 0)` THEN1 DECIDE_TAC THEN
  ASSUME_TAC int_size THEN STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [EXP] THEN
  `65535 <= UINT_MAX` by SRW_TAC [][type_size_constants] THEN
  intLib.ARITH_TAC)

val long_size = size_spec "long_size"
  (--`?x. ULONG_MAX <= (2 ** CHAR_BIT) ** x`--)
val long_size_nonzero = store_thm(
  "long_size_nonzero",
  ``0 < long_size``,
  Q_TAC SUFF_TAC `~(long_size = 0)` THEN1 DECIDE_TAC THEN
  ASSUME_TAC long_size THEN STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [EXP] THEN
  `4294967295 <= ULONG_MAX` by SRW_TAC [][type_size_constants] THEN
  intLib.ARITH_TAC)

(* bit = "basic integral type" here *)
val bit_size = Define`
  (bit_size Char = 1) /\ (bit_size Short = short_size) /\
  (bit_size Int = int_size) /\ (bit_size Long = long_size)
`;

val bool_size = new_specification(
  "bool_size",
  ["bool_size"],
  prove(``?n. 1n <= n``, intLib.ARITH_TAC))


(* pointer to void can contain all other pointers to objects (3.9.2 s4)
   "void *" has same rep and alignment as "char *" (3.9.2 s4)
*)
val ptr_size = new_specification (
  "ptr_size",
  ["ptr_size"],
  prove(``?f. (f BChar = f Void) /\
              !ty. (object_type ty ==> f ty <= f Void) /\
                   1n <= f ty``,
        Q.EXISTS_TAC `K 1` THEN SRW_TAC [][]))

(* size of integral types *)
val int_sizeof_def = Define`
  (int_sizeof (Signed x) = bit_size x) /\
  (int_sizeof (Unsigned x) = bit_size x) /\
  (int_sizeof BChar = 1) /\
  (int_sizeof Bool = bool_size)
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

(* currently this is NOT COMPLETE - not all properties are listed *)
val char_onecomp_def = Define`
  char_onecomp = (SCHAR_MIN = ~SCHAR_MAX)
`;
open wordsTheory
val mod_add_lemma = prove(
  ``0 < c ==> (x MOD c = (x + c) MOD c)``,
  METIS_TAC [ADD_MODULUS_LEFT])
val SUB_RIGHT_ADD' = prove(
  ``x - y + (z : num) = if y <= x then x + z - y else z``,
  DECIDE_TAC);

val mod_sub_lemma = prove(
  ``0 < c /\ y <= x ==> ((x - y) MOD c = (x MOD c + (c - y MOD c)) MOD c)``,
  STRIP_TAC THEN
  Q.SPEC_THEN `c` MP_TAC arithmeticTheory.DIVISION THEN ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fn th =>
                 (MAP_EVERY (fn q => Q.SPEC_THEN q STRIP_ASSUME_TAC th)
                            [`x`,`y`])) THEN
  Q.ABBREV_TAC `q = y DIV c` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = y MOD c` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `s = x DIV c` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `t = x MOD c` THEN POP_ASSUM (K ALL_TAC) THEN
  ASM_REWRITE_TAC [arithmeticTheory.SUB_PLUS] THEN
  `q * c <= s * c`
      by (SRW_TAC [ARITH_ss][LE_MULT_RCANCEL] THEN
          SPOSE_NOT_THEN ASSUME_TAC THEN
          `s + 1 <= q` by DECIDE_TAC THEN
          `(s + 1) * c <= q * c`
             by SRW_TAC [ARITH_ss][LE_MULT_RCANCEL] THEN
          `s * c + t < q * c`
             by (FULL_SIMP_TAC bool_ss [RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
                 DECIDE_TAC) THEN
          DECIDE_TAC) THEN
  `r <= (s - q) * c + t` by DECIDE_TAC THEN
  `s * c + t - q * c = (s - q) * c + t`
     by ASM_SIMP_TAC bool_ss [RIGHT_SUB_DISTRIB, SUB_RIGHT_ADD'] THEN
  `((s-q)*c + t - r) MOD c = ((s-q)*c + t - r + c) MOD c`
      by PROVE_TAC [mod_add_lemma] THEN
  `(s - q) * c + t - r + c = (s - q) * c + (t + (c - r))`
      by ASM_SIMP_TAC bool_ss
                      [SUB_RIGHT_ADD',
                       DECIDE ``r < (z:num) ==>
                                (x + y + z - r = x + (y + (z - r)))``] THEN
  ASM_SIMP_TAC bool_ss [MOD_TIMES]);

val word_sub_n2w_1 = prove(
  ``m <= n ==> (n2w n - n2w m = n2w (n - m))``,
  SRW_TAC [][word_sub_def, word_2comp_def, word_add_n2w] THEN
  `0 < 2 ** dimindex (UNIV : 'a set)` by SRW_TAC [][] THEN
  SRW_TAC [][mod_sub_lemma] THEN
  Q_TAC SUFF_TAC `!x y c. 0 < c ==> ((x MOD c + y) MOD c = (x + y) MOD c)`
        THEN1 SRW_TAC [][] THEN
  METIS_TAC [MOD_MOD, MOD_PLUS])

val CHAR_BIT_BOUNDS = store_thm(
  "CHAR_BIT_BOUNDS",
  ``1n <= 2 ** CHAR_BIT /\ 2n <= 2 ** CHAR_BIT /\ 1 <= CHAR_BIT``,
  `1 <= CHAR_BIT` by (ASSUME_TAC CHAR_BIT THEN DECIDE_TAC) THEN
  SRW_TAC [][DECIDE ``1n <= x = 0 < x``] THEN
  METIS_TAC [EXP_1, EXP_BASE_LE_MONO, DECIDE ``1n < 2``]);

val TWICE_SCHAR_MAX = store_thm(
  "TWICE_SCHAR_MAX",
  ``2n * 2 ** (CHAR_BIT - 1) = 2 ** CHAR_BIT``,
  `CHAR_BIT = SUC (CHAR_BIT - 1)`
     by (ASSUME_TAC CHAR_BIT_BOUNDS THEN DECIDE_TAC) THEN
  METIS_TAC [EXP, MULT_COMM])

val SCHAR_MAX = store_thm(
  "SCHAR_MAX",
  ``SCHAR_MAX = 2 ** (CHAR_BIT - 1) - 1``,
  `SCHAR_MAX = (UCHAR_MAX - 1) / 2` by SRW_TAC [][type_size_constants] THEN
  `UCHAR_MAX = 2 ** CHAR_BIT - 1` by SRW_TAC [][type_size_constants] THEN
  `1n <= 2 ** (CHAR_BIT - 1)` by SRW_TAC [][DECIDE ``1n <= x = 0 < x``] THEN
  STRIP_ASSUME_TAC CHAR_BIT_BOUNDS THEN
  SRW_TAC [ARITH_ss][INT_SUB] THEN
  Q.ABBREV_TAC `C1 = CHAR_BIT - 1` THEN
  `CHAR_BIT = SUC C1` by SRW_TAC [ARITH_ss][Abbr`C1`] THEN
  `2n ** CHAR_BIT - 2 = 2 * (2 ** C1 - 1)`
      by SRW_TAC [][EXP, LEFT_SUB_DISTRIB] THEN
  METIS_TAC [MULT_DIV, DECIDE ``0n < 2``, MULT_COMM])

val int_representation = prove(
  ``?(rep_int : CPP_Type -> int -> byte list option)
     (int_value : CPP_Type -> byte list -> int option).
       (!b:byte. int_value (Unsigned Char) [b] = SOME (int_of_num (w2n b))) /\
       (!i. 0 <= i /\ i <= UCHAR_MAX ==>
            (rep_int (Unsigned Char) i = SOME [n2w (Num i)])) /\
       (!b. ~word_msb b ==>
            (int_value (Signed Char) [b] = int_value (Unsigned Char) [b])) /\
       (!b. word_msb b ==>
               ?i. (int_value (Signed Char) [b] = SOME i) /\
                   SCHAR_MIN <= i /\ i <= 0) /\
       (!i. SCHAR_MIN <= i /\ i <= SCHAR_MAX ==>
            ?b. (rep_int (Signed Char) i = SOME [b]) /\
                (int_value (Signed Char) [b] = SOME i)) /\
       (rep_int BChar = if BCHAR_IS_SIGNED then rep_int (Signed Char)
                        else rep_int (Unsigned Char)) /\
       (int_value BChar = if BCHAR_IS_SIGNED then int_value (Signed Char)
                          else int_value (Unsigned Char))``,
  Q.EXISTS_TAC
    `\ty i.
         if (ty = Unsigned Char) \/ (ty = BChar) /\ ~BCHAR_IS_SIGNED then
           SOME [n2w (Num (i % 2 ** CHAR_BIT))]
         else if (ty = Signed Char) \/ (ty = BChar) /\ BCHAR_IS_SIGNED then
           if char_onecomp then
             if i < 0 then SOME [n2w (Num (~i)) + word_L]
             else SOME [n2w (Num i)]
           else SOME [i2w i]
         else NONE` THEN SIMP_TAC (srw_ss()) [] THEN
  Q.EXISTS_TAC
    `\ty bytes.
       if (ty = Unsigned Char) \/ (ty = BChar) /\ ~BCHAR_IS_SIGNED then
         SOME (&(w2n (HD bytes)))
       else if (ty = Signed Char) \/ (ty = BChar) /\ BCHAR_IS_SIGNED then
         if char_onecomp then
           if word_msb (HD bytes) then
             SOME (~(& (w2n (HD bytes - word_L))))
           else SOME (w2i (HD bytes))
         else SOME (w2i (HD bytes))
       else NONE` THEN
  SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN REPEAT CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN
    `?n. i = &n` by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES THEN
                     FULL_SIMP_TAC (srw_ss()) []) THEN
    SRW_TAC [][],

    SRW_TAC [][integer_wordTheory.w2i_def],

    Q.X_GEN_TAC `w` THEN STRIP_TAC THEN
    Q.ISPEC_THEN `w` STRIP_ASSUME_TAC wordsTheory.ranged_word_nchotomy THEN
    FULL_SIMP_TAC (srw_ss()) [wordsTheory.word_msb_n2w_numeric] THEN
    `0 < n` by METIS_TAC [LESS_LESS_EQ_TRANS, bitTheory.ZERO_LT_TWOEXP] THEN
    `INT_MAX (UNIV : byte_index set) < &n`
       by SRW_TAC [ARITH_ss][integer_wordTheory.INT_MAX_def, INT_SUB] THEN
    `n <= UINT_MAX (UNIV : byte_index set)`
       by SRW_TAC [ARITH_ss][integer_wordTheory.UINT_MAX_def] THEN
    SRW_TAC [][integer_wordTheory.w2i_n2w_neg, INT_LE_SUB_RADD,
               INT_LE_SUB_LADD] THEN
    `1 <= CHAR_BIT` by (ASSUME_TAC CHAR_BIT THEN DECIDE_TAC) THEN
    Cases_on `char_onecomp` THEN SRW_TAC [][] THENL [
      SRW_TAC [][wordsTheory.word_L_def] THEN
      `SCHAR_MIN = ~SCHAR_MAX`
        by FULL_SIMP_TAC (srw_ss()) [char_onecomp_def] THEN
      SRW_TAC [][SCHAR_MAX] THEN
      SRW_TAC [ARITH_ss][word_sub_n2w_1, bitTheory.MOD_2EXP_LT] THEN
      SRW_TAC [ARITH_ss][GSYM INT_SUB] THEN
      Q_TAC SUFF_TAC `2n * (2 ** (CHAR_BIT - 1)) = 2 ** CHAR_BIT` THEN1
            intLib.ARITH_TAC THEN
      SRW_TAC [][TWICE_SCHAR_MAX],

      `SCHAR_MIN = ~SCHAR_MAX - 1`
         by METIS_TAC [char_onecomp_def, type_size_constants] THEN
      SRW_TAC [][SCHAR_MAX, INT_LE_SUB_LADD] THEN
      Q.MATCH_ABBREV_TAC `~x + y <= z:int` THEN
      Q_TAC SUFF_TAC `y <= x + z` THEN1 intLib.ARITH_TAC THEN
      Q.UNABBREV_ALL_TAC THEN SRW_TAC [][INT_ADD] THEN
      ASSUME_TAC TWICE_SCHAR_MAX THEN DECIDE_TAC,

      `SCHAR_MIN = ~SCHAR_MAX - 1`
         by METIS_TAC [char_onecomp_def, type_size_constants] THEN
      SRW_TAC [][SCHAR_MAX, INT_LE_SUB_RADD]
    ],

    Q.X_GEN_TAC `i` THEN STRIP_TAC THEN
    Cases_on `char_onecomp` THENL [
      ASM_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `i < 0` THENL [
        ASM_SIMP_TAC (srw_ss()) [word_msb_n2w_numeric, word_add_n2w,
                                 word_L_def] THEN
        `?n. (i = ~&n) /\ ~(n = 0)`
           by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES  THEN
               FULL_SIMP_TAC (srw_ss()) []) THEN
        ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [word_sub_n2w_1] THEN
        `SCHAR_MIN = ~SCHAR_MAX` by METIS_TAC [char_onecomp_def] THEN
        FULL_SIMP_TAC (srw_ss()) [SCHAR_MAX] THEN
        `&n + 1 <= &(2 ** (CHAR_BIT - 1))` by intLib.ARITH_TAC THEN
        `n + 1 <= 2 ** (CHAR_BIT - 1)`
           by FULL_SIMP_TAC (srw_ss()) [INT_ADD] THEN
        `n + 2 ** (CHAR_BIT - 1) < 2 ** CHAR_BIT`
           by (ASSUME_TAC TWICE_SCHAR_MAX THEN DECIDE_TAC) THEN
        SRW_TAC [][LESS_MOD] THEN DECIDE_TAC,

        ASM_SIMP_TAC (srw_ss()) [word_msb_n2w_numeric] THEN
        `?n. (i = &n)`
           by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES THEN
               FULL_SIMP_TAC (srw_ss()) []) THEN
        FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [SCHAR_MAX, INT_SUB] THEN
        `n < 2 ** CHAR_BIT`
           by (`~(2n ** (CHAR_BIT - 1) = 0)` by SRW_TAC [][] THEN
               ASSUME_TAC TWICE_SCHAR_MAX THEN
               DECIDE_TAC) THEN
        `0 < 2n ** (CHAR_BIT - 1)` by SRW_TAC [][] THEN
        ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)[LESS_MOD] THEN
        MATCH_MP_TAC integer_wordTheory.w2i_n2w_pos THEN
        SRW_TAC [][integer_wordTheory.INT_MAX_def, INT_SUB]
      ],

      (* not one's complement (or sign-magnitude either) *)
      ASM_SIMP_TAC (srw_ss()) [] THEN
      MATCH_MP_TAC integer_wordTheory.w2i_i2w THEN
      `SCHAR_MIN = ~SCHAR_MAX - 1`
         by METIS_TAC [type_size_constants, char_onecomp_def] THEN
      FULL_SIMP_TAC (srw_ss()) [integer_wordTheory.INT_MAX_def,
                                integer_wordTheory.INT_MIN_def,
                                SCHAR_MAX]
    ],


    Cases_on `BCHAR_IS_SIGNED` THEN SRW_TAC [][],
    Cases_on `BCHAR_IS_SIGNED` THEN SRW_TAC [][]

  ])

val C_INT_REP = new_specification(
  "C_INT_REP",
  ["REP_INT", "INT_VAL"],
  int_representation)


(* ----------------------------------------------------------------------
    calculating type sizes

    This has to be done in conjunction with a map specifying the fields
    that occur in a struct
   ---------------------------------------------------------------------- *)

(* -- alignment -- *)

(* alignment of basic integral types *)
(* ASSUMPTION: basic types will never need to be aligned at boundaries
               greater than their sizes.
               For example, if sizeof short == 2, then shorts won't need
               to be aligned on 4 byte boundaries. *)
val short_align = new_specification ("short_align",
  ["short_align"],
  prove(``?n. 1 <= n /\ n <= short_size``,
        ASSUME_TAC short_size_nonzero THEN
        intLib.ARITH_TAC))
val int_align = new_specification("int_align",
  ["int_align"],
  prove(``?n. 1 <= n /\ n <= int_size``,
        ASSUME_TAC int_size_nonzero THEN
        intLib.ARITH_TAC))
val long_align = new_specification("long_align",
  ["long_align"],
  prove(``?n. 1 <= n /\ n <= long_size``,
        ASSUME_TAC long_size_nonzero THEN
        intLib.ARITH_TAC))
val ptr_align = new_specification("ptr_align",
  ["ptr_align"],
  prove(``?f. !ty. 1 <= f ty /\ f ty <= ptr_size ty /\ (f BChar = f Void)``,
        Q.EXISTS_TAC `K 1` THEN SRW_TAC [][ptr_size]))
val bool_align = new_specification("bool_align",
  ["bool_align"],
  prove(``?n. 1 <= n /\ n <= bool_size``,
        ASSUME_TAC bool_size THEN intLib.ARITH_TAC))

(* alignment of the basic integral types *)
val bit_align = Define`
  (bit_align Char = 1) /\
  (bit_align Short = short_align) /\
  (bit_align Int = int_align) /\
  (bit_align Long = long_align)
`;


val _ = overload_on ("set", ``list$LIST_TO_SET``)

(* alignment of class types being maximum alignment of member fields is
   plausible, but should probably count as an ASSUMPTION *)
val (align_rules, align_ind, align_cases) = Hol_reln`
  (!smap. align smap BChar 1) /\  (* same as Char *)

  (!smap. align smap Bool bool_align) /\

  (!smap ty. align smap (Signed ty) (bit_align ty)) /\

  (!smap ty. align smap (Unsigned ty) (bit_align ty)) /\

  (!smap ty. align smap (Ptr ty) (ptr_align ty)) /\

  (!smap c ty. align smap (MPtr c ty) (ptr_align ty)) (* BAD_ASSUMPTION *) /\

  (!smap ty n a. align smap ty a ==> align smap (Array ty n) a) /\

  (!smap cnm max.
      cnm IN FDOM smap /\
      (!ty. ty IN set (smap ' cnm) ==>
            ?a. align smap ty a /\ a <= max) /\
      (?ty. ty IN set (smap ' cnm) /\ align smap ty max)
         ==>
      align smap (Class cnm) max)

`;

(* SANITY : alignment relation is deterministic *)
val align_det = store_thm(
  "align_det",
  ``!smap ty a. align smap ty a ==>
                !b. align smap ty b ==> (a = b)``,
  HO_MATCH_MP_TAC align_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  ((Q.MATCH_ABBREV_TAC `align X Y Z ==> P` THEN
    Q.UNABBREV_ALL_TAC THEN
    ONCE_REWRITE_TAC [align_cases]) ORELSE
   (STRIP_TAC THEN ONCE_REWRITE_TAC [align_cases])) THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [listTheory.IN_LIST_TO_SET] THEN
  METIS_TAC [DECIDE ``a:num <= b /\ b <= a ==> (a = b)``])


(* ----------------------------------------------------------------------
    type sizes and field offsets within classes
   ---------------------------------------------------------------------- *)

val roundup_def = Define`
  roundup base n = if n MOD base = 0 then n else (n DIV base + 1) * base
`;

(* C++ NOTE: classes must have non-zero size, even if they contain
   no fields.  *)


val (offsizeof_rules, offsizeof_ind, offsizeof_cases) = Hol_reln`

  (!s. sizeof s BChar 1) /\

  (!s. sizeof s Bool bool_size) /\

  (!s b. sizeof s (Signed b) (bit_size b)) /\

  (!s b. sizeof s (Unsigned b) (bit_size b)) /\

  (!s t. sizeof s (Ptr t) (ptr_size t)) /\

  (!s c t. sizeof s (MPtr c t) (ptr_size t)) /\ (* BAD_ASSUMPTION *)

  (!s m n t. sizeof s t m ==> sizeof s (Array t n) (m * n)) /\

  (!s c tylist a lastoff lastsz.
        c IN FDOM s /\ (s ' c = tylist) /\
        align s (Class c) a /\
        offset s tylist (LENGTH tylist - 1) lastoff /\
        sizeof s (EL (LENGTH tylist - 1) tylist) lastsz
      ==>
        sizeof s (Class c) (roundup a (lastoff + lastsz))) /\

  (!s tylist.  offset s tylist 0 0) /\
  (!s tylist n a offn sizen.
        offset s tylist n offn /\
        sizeof s (EL n tylist) sizen /\
        align s (EL (SUC n) tylist) a
      ==>
        offset s tylist (SUC n) (roundup a (offn + sizen)))
`;


(* SANITY: sizeof and offset are deterministic *)
val det_lemma = prove(
  ``(!s ty n. sizeof s ty n ==> !m. sizeof s ty m ==> (n = m)) /\
    (!s tylist n off1.
              offset s tylist n off1 ==>
              !off2. offset s tylist n off2 ==> (off1 = off2))``,
  HO_MATCH_MP_TAC offsizeof_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THENL [
    ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][],
    ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][],
    ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][],
    ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][],
    ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][],
    ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][],
    (* array *)
    STRIP_TAC THEN ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][] THEN
    METIS_TAC [],
    (* class size *)
    STRIP_TAC THEN ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][] THEN
    METIS_TAC [align_det],
    (* offset 0 *)
    ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][],
    (* offset SUC *)
    STRIP_TAC THEN ONCE_REWRITE_TAC [offsizeof_cases] THEN SRW_TAC [][] THEN
    METIS_TAC [align_det, listTheory.EL]
  ])
val sizeof_det = save_thm("sizeof_det", CONJUNCT1 det_lemma)
val offset_det = save_thm("offset_det", CONJUNCT2 det_lemma)

val _ = export_theory();

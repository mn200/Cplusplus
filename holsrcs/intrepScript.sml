open HolKernel Parse boolLib bossLib

open wordsTheory

val _ = new_theory "intrep"

val n2ws_def = Define`
  (n2ws 0 n : 'a word list = []) /\
  (n2ws (SUC m) n =
     let base = dimword (:'a) ** m
     in
         n2w ((n DIV base) MOD dimword (:'a)) :: n2ws m (n MOD base))
`;
val _ = export_rewrites ["n2ws_def"]

val ws2n_def = Define`
  (ws2n ([] : 'a word list) = 0) /\
  (ws2n (h::t) = w2n h * dimword(:'a) ** LENGTH t + ws2n t)
`
val _ = export_rewrites ["ws2n_def"]

val ws2n_lt_base = store_thm(
  "ws2n_lt_base",
  ``ws2n (bytes:'a word list) < dimword (:'a) ** LENGTH bytes``,
  Induct_on `bytes` THEN SRW_TAC [][arithmeticTheory.EXP] THEN
  `w2n h < dimword (:'a)` by SRW_TAC [][w2n_lt] THEN
  Q_TAC SUFF_TAC `!h b bn y:num. y < bn /\ h < b ==> h * bn + y < b * bn`
        THEN1 SRW_TAC [][] THEN
  REPEAT (POP_ASSUM (K ALL_TAC)) THEN
  SRW_TAC [][] THEN
  `(b = 0) \/ ?b0. b = SUC b0` by (Cases_on `b` THEN SRW_TAC [][]) THEN
  FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.MULT_CLAUSES] THEN
  Q_TAC SUFF_TAC `h * bn <= b0 * bn` THEN1 DECIDE_TAC THEN
  SRW_TAC [ARITH_ss][]);


val n2ws_num = store_thm(
  "n2ws_num",
  ``n2ws (LENGTH bytes) (ws2n bytes) = bytes``,
  Induct_on `bytes` THEN SRW_TAC [][ws2n_def] THEN
  CONJ_TAC THENL [
    ALL_TAC,
    Q_TAC SUFF_TAC
          `(w2n h * base + ws2n bytes) MOD base = ws2n bytes` THEN1
          SRW_TAC [][] THEN
    MATCH_MP_TAC arithmeticTheory.MOD_MULT THEN
    SRW_TAC [][BasicProvers.Abbr`base`, ws2n_lt_base]
  ] THEN
  `(w2n h * base + ws2n bytes) DIV base = w2n h`
     by (MATCH_MP_TAC arithmeticTheory.DIV_MULT THEN
         SRW_TAC [][BasicProvers.Abbr`base`, ws2n_lt_base]) THEN
  SRW_TAC [][arithmeticTheory.LESS_MOD, w2n_lt]);

val LENGTH_n2ws = store_thm(
  "LENGTH_n2ws",
  ``!m n. LENGTH (n2ws m n) = m``,
  Induct_on `m` THEN SRW_TAC [][] THEN SRW_TAC [][])
val _ = export_rewrites ["LENGTH_n2ws"]

val lbyte_n2ws = store_thm(
  "lbyte_n2ws",
  ``!m n. ws2n (n2ws m n : 'a word list) = n MOD (dimword(:'a) ** m)``,
  Induct_on `m` THEN SRW_TAC [][arithmeticTheory.EXP] THEN
  SRW_TAC [][] THEN
  `0 < base` by SRW_TAC [][BasicProvers.Abbr`base`] THEN
  SRW_TAC [][] THEN
  `0 < dimword (:'a)` by SRW_TAC [][ZERO_LT_dimword] THEN
  SRW_TAC [][arithmeticTheory.DIV_MOD_MOD_DIV] THEN
  Q_TAC SUFF_TAC `n MOD base = n MOD (dimword(:'a) * base) MOD base`
        THEN1 METIS_TAC [arithmeticTheory.MULT_COMM,
                         arithmeticTheory.DIVISION] THEN
  METIS_TAC [arithmeticTheory.MOD_MULT_MOD, arithmeticTheory.MULT_COMM]);

val _ = export_theory()

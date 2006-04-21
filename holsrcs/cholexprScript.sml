(* \#line cholera-model.nw 26 *)
open HolKernel boolLib Parse mnUtils Psyntax
open simpLib bossLib boolSimps arithmeticTheory pred_setTheory
infix >-

val hol_ss = bossLib.list_ss

(* \#line cholera-model.nw 1865 *)
local open cholmemTheory in end;
open Datatype

val _ = new_theory "cholexpr";
(* \#line cholera-model.nw 1888 *)
val c_binops = Hol_datatype
    `c_binops = CPlus | CMinus  | CLess  | CGreat | CLessE | CGreatE |
                CEq   | CTimes | CDiv   | CMod   | CNotEq`;
(* \#line cholera-model.nw 1902 *)
val c_unops = Hol_datatype
    `c_unops = CUnPlus | CUnMinus | CComp | CNot | CNullFunRef`;
(* \#line cholera-model.nw 1917 *)
val memval = ty_antiq (==`:MemObj list`==)

val _ = Hol_datatype
  `CExpr = Cnum of num   | Cchar of num      | Cnullptr of CType |
           Var of string | CFunRef of string |
           COr of CExpr => CExpr |
           CAnd of CExpr => CExpr |
           CCond of CExpr => CExpr => CExpr |
           CApBinary of c_binops => CExpr => CExpr |
           CApUnary of c_unops => CExpr |
           Deref of CExpr |
           Addr of CExpr |
           Assign of c_binops option => CExpr => CExpr => (num -> num) |
           SVar of CExpr => string |
           FnApp of CExpr => CExpr list |
           CommaSep of CExpr => CExpr |
           Cast of CType => CExpr |
           PostInc of CExpr |
           
(* \#line cholera-model.nw 1961 *)
CAndOr_sqpt of CExpr |
FnApp_sqpt of CExpr => CExpr list |
LVal of num => CType |
RValreq of CExpr |
ECompVal of MemObj list => CType |
UndefinedExpr
(* \#line cholera-model.nw 1935 *)
                                           `;
(* \#line cholera-model.nw 1971 *)
val every_eliminate = prove(
  ``(!x. P x) ==> (!xl. EVERY P xl)``,
  STRIP_TAC THEN INDUCT_THEN listTheory.list_INDUCT ASSUME_TAC THEN
  ASM_SIMP_TAC hol_ss []);
val quick_induction = save_thm(
  "quick_induction",
  (SPECL [``P:CExpr->bool``, ``EVERY (P:CExpr->bool)``] >-
   SIMP_RULE (hol_ss ++ CONJ_ss) [every_eliminate] >- GEN_ALL)
  (TypeBase.induction_of ``:CExpr``))
(* \#line cholera-model.nw 1988 *)
val rec_expr_P_def = Define`
    (rec_expr_P (Cnum i) = \P. P (Cnum i)) /\
    (rec_expr_P (Cchar c) = \P. P (Cchar c)) /\
    (rec_expr_P (Cnullptr t) = \P. P (Cnullptr t)) /\
    (rec_expr_P (Var n) = \P. P (Var n)) /\
    (rec_expr_P (CFunRef n) = \P. P (CFunRef n)) /\
    (rec_expr_P (COr e1 e2) =
      \P. P (COr e1 e2) /\ rec_expr_P e1 P /\ rec_expr_P e2 P) /\
    (rec_expr_P (CAnd e1 e2) =
      \P. P (CAnd e1 e2) /\ rec_expr_P e1 P /\ rec_expr_P e2 P) /\
    (rec_expr_P (CCond e1 e2 e3) =
      \P. P (CCond e1 e2 e3) /\ rec_expr_P e1 P /\ rec_expr_P e2 P /\
          rec_expr_P e3 P) /\
    (rec_expr_P (CApBinary f e1 e2) =
      \P. P (CApBinary f e1 e2) /\ rec_expr_P e1 P /\
          rec_expr_P e2 P) /\
    (rec_expr_P (CApUnary f' e) =
      \P. P (CApUnary f' e) /\ rec_expr_P e P) /\
    (rec_expr_P (Deref e) = \P. P (Deref e) /\ rec_expr_P e P) /\
    (rec_expr_P (Addr e) = \P. P (Addr e) /\ rec_expr_P e P) /\
    (rec_expr_P (Assign fo e1 e2 b) =
      \P. P (Assign fo e1 e2 b) /\ rec_expr_P e1 P /\ rec_expr_P e2 P) /\
    (rec_expr_P (SVar e fld) =
      \P. P (SVar e fld) /\ rec_expr_P e P) /\
    (rec_expr_P (FnApp e args) =
      \P. P (FnApp e args) /\ rec_expr_P e P /\ rec_exprl_P args P) /\
    (rec_expr_P (CommaSep e1 e2) =
      \P. P (CommaSep e1 e2) /\ rec_expr_P e1 P /\ rec_expr_P e2 P) /\
    (rec_expr_P (Cast t e) = \P. P (Cast t e) /\ rec_expr_P e P) /\
    (rec_expr_P (PostInc e) = \P. P (PostInc e) /\ rec_expr_P e P) /\
    (rec_expr_P (CAndOr_sqpt e) =
      \P. P (CAndOr_sqpt e) /\ rec_expr_P e P) /\
    (rec_expr_P (FnApp_sqpt e args) =
      \P. P (FnApp_sqpt e args) /\ rec_expr_P e P /\
          rec_exprl_P args P) /\
    (rec_expr_P (LVal a t) = \P. P (LVal a t)) /\
    (rec_expr_P (RValreq e) = \P. P (RValreq e) /\ rec_expr_P e P) /\
    (rec_expr_P (ECompVal v t) = \P. P (ECompVal v t)) /\
    (rec_expr_P UndefinedExpr = \P. P UndefinedExpr) /\
    (rec_exprl_P [] = \P. T) /\
    (rec_exprl_P (CONS e es) =
      \P. rec_expr_P e P /\ rec_exprl_P es P)`;
val rec_expr_P = save_thm("rec_expr_P", rec_expr_P_def);
(* \#line cholera-model.nw 2040 *)
open SingleStep
val rec_expr_simple = store_thm(
  "rec_expr_simple",
  (--`!P e. rec_expr_P e P ==> P e`--),
  REPEAT GEN_TAC THEN Cases_on `e` THEN
  SIMP_TAC hol_ss [rec_expr_P]);
(* \#line cholera-model.nw 2051 *)
val rec_exprl_EVERY = store_thm(
  "rec_exprl_EVERY",
  (--`!el P. rec_exprl_P el P = EVERY (\e. rec_expr_P e P) el`--),
  INDUCT_THEN (listTheory.list_INDUCT) ASSUME_TAC THEN
  ASM_SIMP_TAC hol_ss [rec_expr_P]);
(* \#line cholera-model.nw 2061 *)
val e_cases =
  (concl >- strip_forall >- snd >- strip_disj >-
   map (strip_exists >- snd >- rhs))
  (theorem "CExpr_nchotomy")
val has_no_undefineds_DEF = new_definition(
  "has_no_undefineds_DEF",
  ``has_no_undefineds e = rec_expr_P e (\e. ~(e = UndefinedExpr))``);
local
  val e_thms = map
    (C SPEC has_no_undefineds_DEF >-
     SIMP_RULE hol_ss [rec_expr_P, theorem "CExpr_distinct"] >- GEN_ALL >-
     SIMP_RULE hol_ss [GSYM has_no_undefineds_DEF, rec_exprl_EVERY])
    e_cases
in
  val has_no_undefineds = save_thm(
    "has_no_undefineds",
    LIST_CONJ e_thms)
end;
(* \#line cholera-model.nw 2092 *)
val side_affecting = TotalDefn.Define
  `(side_affecting (Assign f e1 e2 b) = T) /\
   (side_affecting (FnApp fdes args) = T) /\
   (side_affecting (FnApp_sqpt fdes args) = T) /\
   (side_affecting (PostInc e)    = T) /\
   (side_affecting allelse = F)`;
val syn_pure_expr = new_definition (
  "syn_pure_expr",
  (--`syn_pure_expr e = rec_expr_P e ($~ o side_affecting)`--));
(* \#line cholera-model.nw 2114 *)
val has_sqpt = TotalDefn.Define
  `(has_sqpt (FnApp f args) = T) /\
   (has_sqpt (FnApp_sqpt f args) = T) /\
   (has_sqpt (CommaSep e1 e2) = T) /\
   (has_sqpt (CAnd e1 e2) = T) /\
   (has_sqpt (COr e1 e2) = T) /\
   (has_sqpt (CCond e1 e2 e3) = T) /\
   (has_sqpt allelse = F)`;
val seqpt_free = new_definition (
  "seqpt_free",
  (--`seqpt_free e = rec_expr_P e ($~ o has_sqpt)`--));
(* \#line cholera-model.nw 1876 *)
val _ = export_theory();

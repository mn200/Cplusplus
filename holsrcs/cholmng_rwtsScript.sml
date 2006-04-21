(* \#line cholera-model.nw 26 *)
open HolKernel boolLib Parse mnUtils Psyntax
open simpLib bossLib boolSimps arithmeticTheory pred_setTheory
infix >-

val hol_ss = bossLib.list_ss

(* \#line cholera-model.nw 6294 *)
val _ = new_theory "cholmng_rwts";

local open cholmeaningTheory in end;

(* \#line cholera-model.nw 4719 *)
open chol_proof0
open cholmeaningTheory
local
  fun EVERY_DISJ_CONV c t =
    (if (is_disj t) then
       disj1_CONV (EVERY_DISJ_CONV c) THENC
       disj2_CONV (EVERY_DISJ_CONV c)
     else c) t
  val disjconv =
    EX_OUT_CONV THENC
    REWRITE_CONV [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, PAIR_EQ,
                  pred_setTheory.IN_INSERT,
                  pred_setTheory.NOT_IN_EMPTY] THENC
    TOP_DEPTH_CONV EXISTS_OR_CONV THENC
    SIMP_CONV Chol_ss []
  val sv_term = (--`(s, v):CState # meaning_val`--)
  val cases = cholmeaningTheory.meaning_cases
  fun transform t =
    SPECL [t, ``s0:CState``, sv_term] >-
    SIMP_RULE Chol_ss [] >-
    REWRITE_RULE [valid_econtext, valid_lvcontext] >-
    CONV_RULE (rhs_CONV (EVERY_DISJ_CONV disjconv)) >-
    REWRITE_RULE [] >- GEN_ALL
in
  fun spec_meaning name t = save_thm(name, transform t cases)
end;
(* \#line cholera-model.nw 4781 *)
val num = spec_meaning "num" (--`mExpr (Cnum n) se0`--)
(* \#line cholera-model.nw 4809 *)
val char = spec_meaning "char" (--`mExpr (Cchar c) se0`--)
val nullptr = spec_meaning "nullptr" (--`mExpr (Cnullptr t) se0`--)
val funref = spec_meaning "funref" (--`mExpr (CFunRef n) se0`--)
(* \#line cholera-model.nw 4837 *)
val var = spec_meaning "var" (--`mExpr (Var vname) se0`--)
val lval = spec_meaning "lval" (--`mExpr (LVal n t) se0`--)
(* \#line cholera-model.nw 4869 *)
val typecast = spec_meaning "typecast" (--`mExpr (Cast t e) se0`--)
(* \#line cholera-model.nw 4953 *)
val undefinedexpr = spec_meaning "undefinedexpr" ``mExpr UndefinedExpr se0``
val ecompval = spec_meaning "ecompval" ``mExpr (ECompVal v t) se0``
(* \#line cholera-model.nw 5162 *)
val comma_sep = spec_meaning "comma_sep" (--`mExpr (CommaSep e1 e2) se0`--)
val rvalreq = spec_meaning "rvalreq" (--`mExpr (RValreq e) se0`--)
(* \#line cholera-model.nw 5197 *)
val ap_unary = spec_meaning "ap_unary" (--`mExpr (CApUnary f e) se0`--)
(* \#line cholera-model.nw 5226 *)
val ap_binary = spec_meaning "ap_binary" (--`mExpr (CApBinary f e1 e2) se0`--)
(* \#line cholera-model.nw 5284 *)
val c_and = spec_meaning "c_and" (--`mExpr (CAnd e1 e2) se0`--)
val c_and_sqpt = spec_meaning "c_and_sqpt" (--`mExpr (CAndOr_sqpt e) se0`--)
(* \#line cholera-model.nw 5311 *)
val c_or = spec_meaning "c_or" (--`mExpr (COr e1 e2) se0`--)
(* \#line cholera-model.nw 5358 *)
val c_cond = spec_meaning "c_cond" (--`mExpr (CCond e1 e2 e3) se0`--)
(* \#line cholera-model.nw 5389 *)
val deref = spec_meaning "deref" (--`mExpr (Deref e) se0`--)
(* \#line cholera-model.nw 5406 *)
val addr = spec_meaning "addr" (--`mExpr (Addr e) se0`--)
(* \#line cholera-model.nw 5530 *)
val assign = spec_meaning "assign" (--`mExpr (Assign f e1 e2 b) se0`--)
(* \#line cholera-model.nw 5576 *)
val postinc = spec_meaning "postinc" (--`mExpr (PostInc e) se0`--)
(* \#line cholera-model.nw 5610 *)
val field_sel = spec_meaning "field_sel" (--`mExpr (SVar e fld) se0`--)
(* \#line cholera-model.nw 5680 *)
val fn_app = spec_meaning "fn_app" (--`mExpr (FnApp f args) se0`--)
val fn_app_sqpt = spec_meaning "fn_app_sqpt" (--`mExpr (FnApp_sqpt f args) se0`--)
(* \#line cholera-model.nw 5827 *)
val tc_exprs = spec_meaning "tc_exprs" (--`mTCExpr e se0`--)
(* \#line cholera-model.nw 5840 *)
val ev_lemma = prove(
  ``!e s0 sv.
      meaning e s0 sv ==>
      !e0 se0 s v.
        (e = mExpr e0 se0) \/ (e = mTCExpr e0 se0) ==>
        (sv = (s, v)) ==>
        ?e se. v = ExprVal e se``,
  HO_MATCH_MP_TAC meaning_induction THEN REPEAT CONJ_TAC THEN
  SIMP_TAC Chol_ss []);
val exprs_exprvals = save_thm(
  "exprs_exprvals",
  SIMP_RULE (hol_ss ++ impnorm_set) [
    RIGHT_IMP_FORALL_THM, FORALL_AND_THM] ev_lemma);
(* \#line cholera-model.nw 5864 *)
val tc_expr_single = prove(
  (--`!e0 se0 s0 sv. meaning (mExpr e0 se0) s0 sv ==>
                     meaning (mTCExpr e0 se0) s0 sv`--),
  SIMP_TAC Chol_ss [pairTheory.FORALL_PROD] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC [tc_exprs] THEN
  IMP_RES_TAC exprs_exprvals THEN ELIM_TAC THEN SIMP_TAC Chol_ss [] THEN
  ONCE_REWRITE_TAC [tc_exprs] THEN ASM_SIMP_TAC Chol_ss [] THEN
  ASM_MESON_TAC []);
(* \#line cholera-model.nw 5907 *)
val emptystmt = spec_meaning "emptystmt" (--`mStmt EmptyStmt`--)
val standalone = spec_meaning "standalone" (--`mStmt (Standalone e)`--)
val _ =
  say "Done rewrite proof for emptystmt and standalone expressions\n";
(* \#line cholera-model.nw 5946 *)
val stmtl_nil = spec_meaning "stmtl_nil" (--`mStmtl []`--)
val stmtl_cons = spec_meaning "stmtl_cons" (--`mStmtl (CONS stmt stmts)`--)
val ret = spec_meaning "ret" (--`mStmt (Ret e)`--)
val empty_ret = spec_meaning "empty_ret" (--`mStmt EmptyRet`--)
val break = spec_meaning "break" (--`mStmt Break`--)
val cont = spec_meaning "cont" (--`mStmt Cont`--)
(* \#line cholera-model.nw 5971 *)
val trap' = spec_meaning "trap'" (--`mStmt (Trap tt s)`--)
val trap = store_thm(
  "trap",
  --`!tt stmt s0 s v.
       meaning (mStmt (Trap tt stmt))  s0 (s,v) =
       ?v'. meaning (mStmt stmt) s0 (s, v') /\
         (traplink tt v' /\ (v = StmtVal) \/
          ~traplink tt v' /\ (v = v'))`--,
  REPEAT GEN_TAC THEN SIMP_TAC Chol_ss [trap'] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ELIM_TAC THEN
  ASM_SIMP_TAC Chol_ss [] THEN ASM_MESON_TAC []);
(* \#line cholera-model.nw 6021 *)
val ifstmt = spec_meaning "ifstmt" (--`mStmt (CIf g ts es)`--)
(* \#line cholera-model.nw 6091 *)
val whilestmt = spec_meaning "whilestmt" (--`mStmt (CLoop g bdy)`--)
(* \#line cholera-model.nw 6130 *)
val block_stmt = spec_meaning "block_stmt" (--`mStmt (Block vds stmts)`--)
(* \#line cholera-model.nw 6174 *)
val plain_vardecl = spec_meaning "plain_vardecl" (--`mVarD (VDec type name)`--)
(* \#line cholera-model.nw 6216 *)
val init_vardecl = spec_meaning "init_vardecl" (--`mVarD (VDecInit t n e)`--)
val _ =
  say "Done rewrite proof for initialising variable declarations\n"
(* \#line cholera-model.nw 6234 *)
val struct_vardecl =
  spec_meaning "struct_vardecl" (--`mVarD (VStrDec name flds)`--)
val _ =
  say "Done rewrite proof for structure variable declarations\n";
(* \#line cholera-model.nw 6262 *)
val vardecll_nil = spec_meaning "vardecll_nil" (--`mVarDl []`--)
val vardecll_cons =
  spec_meaning "vardecll_cons" (--`mVarDl (CONS vd vds)`--)

(* \#line cholera-model.nw 6301 *)
val _ = export_theory();

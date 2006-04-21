(* \#line cholera-model.nw 26 *)
open HolKernel boolLib Parse mnUtils Psyntax
open simpLib bossLib boolSimps arithmeticTheory pred_setTheory
infix >-

val hol_ss = bossLib.list_ss

(* \#line cholera-model.nw 2137 *)
val _ = new_theory "cholstmt";
(* parent *)
local open cholstaticsTheory in end
open Datatype

(* \#line cholera-model.nw 2160 *)
val _ = Hol_datatype
   `var_decl = VDec of CType => string |
               VDecInit of CType => string => CExpr |
               VStrDec of string => (string#CType) list`;
val decl_exprs_def = TotalDefn.Define
  `(decl_exprs (VDec t s) = []) /\
   (decl_exprs (VDecInit t s e) = [e]) /\
   (decl_exprs (VStrDec s fl) = [])`;
val _ = new_definition(
  "decllist_exprs",
  (--`decllist_exprs decllist = FLAT (MAP decl_exprs decllist)`--));
(* \#line cholera-model.nw 2183 *)
val _ = Hol_datatype `traptype = BreakTrap | ContTrap`;
(* \#line cholera-model.nw 2189 *)
val _ = Hol_datatype
  `CStmt = CLoop of CExpr => CStmt |
           CIf of CExpr => CStmt => CStmt |
           Standalone of CExpr |
           EmptyStmt |
           Block of var_decl list => CStmt list |
           Ret of CExpr |
           EmptyRet | Break | Cont | Trap of traptype => CStmt`;
(* \#line cholera-model.nw 2215 *)
val forloop = new_definition(
  "forloop",
  --`forloop e1 e2 e3 bdy =
       Block [] [Standalone e1;
                 Trap BreakTrap
                   (CLoop e2 (Block [] [Trap ContTrap bdy;
                                        Standalone e3]))]`--);
val whileloop = new_definition(
  "whileloop",
  --`whileloop g s = Trap BreakTrap (CLoop g (Trap ContTrap s))`--);
val doloop = new_definition(
  "doloop",
  --`doloop bdy g =
       Trap BreakTrap (Block [] [Trap ContTrap bdy;
                                 CLoop g (Trap ContTrap bdy)])`--);
(* \#line cholera-model.nw 2240 *)
val rec_stmt_P = TotalDefn.xDefine "rec_stmt_P"
   `(rec_stmt_P (CLoop g bdy) =
      \P. P (CLoop g bdy) /\ rec_stmt_P bdy P) /\
    (rec_stmt_P (CIf g t f) =
      \P. P (CIf g t f) /\ rec_stmt_P t P /\ rec_stmt_P f P) /\
    (rec_stmt_P (Standalone e) = \P. P (Standalone e)) /\
    (rec_stmt_P EmptyStmt = \P. P EmptyStmt) /\
    (rec_stmt_P (Block vds sts) =
      \P. P (Block vds sts) /\ rec_stmtl_P sts P) /\
    (rec_stmt_P (Ret e) = \P. P (Ret e)) /\
    (rec_stmt_P EmptyRet = \P. P EmptyRet) /\
    (rec_stmt_P Break = \P. P Break) /\
    (rec_stmt_P Cont = \P. P Cont) /\
    (rec_stmt_P (Trap tt s) = \P. P (Trap tt s) /\ rec_stmt_P s P) /\
    (rec_stmtl_P [] = \P. T) /\
    (rec_stmtl_P (CONS x xs) =
      \P. rec_stmt_P x P /\ rec_stmtl_P xs P)`;
(* \#line cholera-model.nw 2264 *)
val is_retstmt = new_definition (
  "is_retstmt",
  (--`is_retstmt s = (?e. s = Ret e) \/ (s = EmptyRet)`--));
val is_intstmt = new_definition (
  "is_intstmt",
  (--`is_intstmt s = is_retstmt s \/ (s = Cont) \/ (s = Break)`--));
val retfree = new_definition (
  "retfree",
  (--`retfree stmt = rec_stmt_P stmt ($~ o is_retstmt)`--));
val breakfree = new_definition (
  "breakfree",
  (--`breakfree stmt = rec_stmt_P stmt (\s. ~(s = Break))`--));
val contfree = new_definition (
  "contfree",
  (--`contfree stmt = rec_stmt_P stmt (\s. ~(s = Cont))`--));
val intstmt_free = new_definition (
  "intstmt_free",
  (--`intstmt_free stmt = rec_stmt_P stmt ($~ o is_intstmt)`--));
(* \#line cholera-model.nw 2287 *)
val rec_stmtl_EVERY = store_thm(
  "rec_stmtl_EVERY",
  (--`!stl P.
        rec_stmtl_P stl P = EVERY (\st. rec_stmt_P st P) stl`--),
  INDUCT_THEN (listTheory.list_INDUCT) ASSUME_TAC THEN
  ASM_SIMP_TAC hol_ss [rec_stmt_P]);

(* \#line cholera-model.nw 2146 *)
val _ = export_theory();

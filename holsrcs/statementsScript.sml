(* C statements - to be expanded into C++ statements *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open typesTheory memoryTheory expressionsTheory

val _ = new_theory "statements";
(* actually also the theory of declaration forms *)




(* A declaration can be used to declare (but not define a function).
   A VStrDec with an empty field list is the equivalent of
     struct foo;
   i.e., an incomplete declaration of a struct type
*)
val _ = Hol_datatype`
   var_decl = VDec of CType => string
            | VDecInit of CType => string => CExpr
            | VStrDec of string => (string#CType) list
`;

(* extract the initialisation expression from a declaration *)
val decl_exprs_def = Define`
  (decl_exprs (VDec t s) = []) /\
  (decl_exprs (VDecInit t s e) = [e]) /\
  (decl_exprs (VStrDec s fl) = [])
`;
val decllist_exprs_def = Define`
  decllist_exprs decllist = FLAT (MAP decl_exprs decllist)
`



(* sorts of things that might be trapped - will probably be extended to allow
   expressions to be caught as well *)
val _ = Hol_datatype `traptype = BreakTrap | ContTrap`;

val _ = Hol_datatype`
  CStmt = CLoop of CExpr => CStmt
        | CIf of CExpr => CStmt => CStmt
        | Standalone of CExpr
        | EmptyStmt
        | Block of var_decl list => CStmt list
        | Ret of CExpr
        | EmptyRet
        | Break
        | Cont
        | Trap of traptype => CStmt
`;

(* derived loop forms *)
val forloop_def = Define`
  forloop e1 e2 e3 bdy =
       Block [] [Standalone e1;
                 Trap BreakTrap
                   (CLoop e2 (Block [] [Trap ContTrap bdy;
                                        Standalone e3]))]
`
val whileloop_def = Define`
  whileloop g s = Trap BreakTrap (CLoop g (Trap ContTrap s))
`;
val doloop_def = Define`
  doloop bdy g =
       Trap BreakTrap (Block [] [Trap ContTrap bdy;
                                 CLoop g (Trap ContTrap bdy)])
`

(* recursively check a predicate over a statement *)
val rec_stmt_P_def = Define `
  (rec_stmt_P (CLoop g bdy) =
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
  (rec_stmtl_P (CONS x xs) = \P. rec_stmt_P x P /\ rec_stmtl_P xs P)
`;
val rec_stmtl_EVERY = store_thm(
  "rec_stmtl_EVERY",
  (--`!stl P.
        rec_stmtl_P stl P = EVERY (\st. rec_stmt_P st P) stl`--),
  Induct THEN ASM_SIMP_TAC (srw_ss()) [rec_stmt_P_def]);
val _ = export_rewrites ["rec_stmtl_EVERY"]

(* categorising some forms of statement *)
val is_retstmt_def = Define`
  is_retstmt s = (?e. s = Ret e) \/ (s = EmptyRet)
`;
val is_intstmt_def = Define`
  is_intstmt s = is_retstmt s \/ (s = Cont) \/ (s = Break)
`;
val retfree_def = Define`
  retfree stmt = rec_stmt_P stmt ($~ o is_retstmt)
`;
val breakfree_def = Define`
  breakfree stmt = rec_stmt_P stmt (\s. ~(s = Break))
`;
val contfree = Define`
  contfree stmt = rec_stmt_P stmt (\s. ~(s = Cont))
`
val intstmt_free_def = Define`
  intstmt_free stmt = rec_stmt_P stmt ($~ o is_intstmt)
`

(* external declarations can appear at the top level of a translation unit *)
val _ = Hol_datatype`
  ext_decl = FnDefn of CPP_Type => string => (string # CPP_Type) list => CStmt
           | Decl of var_decl
`;

val _ = export_theory();

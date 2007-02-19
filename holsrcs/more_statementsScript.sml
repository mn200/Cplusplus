open HolKernel Parse boolLib bossLib

open statementsTheory

val _ = new_theory "more_statements"

(* derived loop forms *)
val forloop_def = Define`
  forloop e1 e2 e3 bdy =
       Block F []
             [Standalone (NormE e1 base_se);
              Trap BreakTrap
                   (CLoop e2 (Block F [] [Trap ContTrap bdy;
                                          Standalone (NormE e3 base_se)]))]
`
val whileloop_def = Define`
  whileloop g s = Trap BreakTrap (CLoop (NormE g base_se) (Trap ContTrap s))
`;
val doloop_def = Define`
  doloop bdy g =
       Trap BreakTrap
            (Block F [] [Trap ContTrap bdy;
                         CLoop (NormE g base_se) (Trap ContTrap bdy)])
`

(* recursively check a predicate over a statement *)
val rec_stmt_P_def = Define `
  (rec_stmt_P (CLoop g bdy) =
    \P. P (CLoop g bdy) /\ rec_stmt_P bdy P) /\
  (rec_stmt_P (CIf g t f) =
    \P. P (CIf g t f) /\ rec_stmt_P t P /\ rec_stmt_P f P) /\
  (rec_stmt_P (Standalone e) = \P. P (Standalone e)) /\
  (rec_stmt_P EmptyStmt = \P. P EmptyStmt) /\
  (rec_stmt_P (Block b vds sts) =
    \P. P (Block b vds sts) /\ rec_stmtl_P sts P) /\
  (rec_stmt_P (Ret e) = \P. P (Ret e)) /\
  (rec_stmt_P EmptyRet = \P. P EmptyRet) /\
  (rec_stmt_P Break = \P. P Break) /\
  (rec_stmt_P Cont = \P. P Cont) /\
  (rec_stmt_P (Throw eopt) = \P. P (Throw eopt)) /\
  (rec_stmt_P (Trap tt s) = \P. P (Trap tt s) /\ rec_stmt_P s P) /\
  (rec_stmtl_P [] = \P. T) /\
  (rec_stmtl_P (CONS x xs) = \P. rec_stmt_P x P /\ rec_stmtl_P xs P)
`;
val rec_stmtl_EVERY = store_thm(
  "rec_stmtl_EVERY",
  ``!stl P.
        rec_stmtl_P stl P = EVERY (\st. rec_stmt_P st P) stl``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [rec_stmt_P_def]);
val _ = export_rewrites ["rec_stmtl_EVERY"]

val erec_stmt_def = Define`
  (erec_stmt P (CLoop g bdy) = erec_exte P g /\ erec_stmt P bdy) /\
  (erec_stmt P (CIf g t f) =
      erec_exte P g /\ erec_stmt P t /\ erec_stmt P f) /\
  (erec_stmt P (Standalone ee) = erec_exte P ee) /\
  (erec_stmt P EmptyStmt = T) /\
  (erec_stmt P (Block b vds sts) = erec_vdecs P vds /\ erec_stmtl P sts) /\
  (erec_stmt P (Ret ee) = erec_exte P ee) /\
  (erec_stmt P EmptyRet = T) /\
  (erec_stmt P Break = T) /\
  (erec_stmt P Cont = T) /\
  (erec_stmt P (Trap tt s) = erec_stmt P s) /\

  (erec_stmtl P [] = T) /\
  (erec_stmtl P (s::ss) = erec_stmt P s /\ erec_stmtl P ss) /\

  (erec_exte P (NormE e se) = P e) /\
  (erec_exte P (EStmt s c) = erec_stmt P s) /\

  (erec_vdecs P [] = T) /\
  (erec_vdecs P (vd::vds) = erec_vdec P vd /\ erec_vdecs P vds) /\

  (erec_vdec P (VDec ty nm) = T) /\
  (erec_vdec P (VDecInit ty nm i) = erec_idec P i) /\
  (erec_vdec P (VDecInitA ty vloc i) = erec_idec P i) /\
  (erec_vdec P (VStrDec cnm copt) = T) /\

  (erec_idec P (DirectInit ee) = erec_exte P ee) /\
  (erec_idec P (CopyInit ee) = erec_exte P ee)
`

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

val exception_stmt_def = Define`
  (exception_stmt (Throw exn) = ?e. exn = SOME e) /\
  (exception_stmt s = F)
`;

(* external declarations can appear at the top level of a translation unit *)
val _ = Hol_datatype`
  ext_decl = FnDefn of CPP_Type => CPPname => (string # CPP_Type) list => CStmt
           | Decl of var_decl
           | ClassConDef of CPPname => (string # CPP_Type) list =>
                            mem_initializer list =>
                            CStmt
           | ClassDestDef of CPPname => CStmt
           | TemplateDef of (CPP_Type # string) list => ext_decl
`;

val _ = export_theory()
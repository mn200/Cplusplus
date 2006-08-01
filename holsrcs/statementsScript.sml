(* C statements - to be expanded into C++ statements *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* also need theory of bags *)
local open bagTheory in end

(* C++ ancestor theories  *)
open typesTheory memoryTheory expressionsTheory

val _ = new_theory "statements";
(* actually also the theory of declaration forms *)



val _ = type_abbrev("se", ``:num # byte list``)
val _ = Hol_datatype `se_info = <| pending_ses : se->num ;
                                   update_map  : num->bool ;
                                   ref_map     : num->bool |>`;
val base_se_def = Define`
  base_se = <| pending_ses := {| |}; update_map := {}; ref_map := {} |>
`;


(* sorts of things that might be trapped - will probably be extended to allow
   expressions to be caught as well *)
val _ = Hol_datatype `traptype = BreakTrap | ContTrap`;


(* sorts of continuations, depending on whether a function is to return a
   reference or not. *)
val _ = Hol_datatype `
  conttype = RVC of (byte list -> CPP_Type -> CExpr)
           | LVC of (num -> CPP_Type -> string list -> CExpr)
`;


val _ = Hol_datatype`
  CStmt    = CLoop of ExtE => CStmt
           | CIf of ExtE => CStmt => CStmt
           | Standalone of ExtE
           | EmptyStmt
           | Block of bool => var_decl list => CStmt list
               (* boolean records whether or not block has been entered, so
                  all blocks will initially have this false *)
           | Ret of ExtE
           | EmptyRet
           | Break
           | Cont
           | Trap of traptype => CStmt ;

  ExtE     = NormE of CExpr => se_info
           | EStmt of CStmt => conttype ;

  var_decl = VDec of CType => string
           | VDecInit of CType => string => ExtE
           | VStrDec of string => class_info option ;

  class_entry (* TODO: classes can contain nested classes *)
           = CFnDefn of CPP_Type => string => (string # CPP_Type) list =>
                        CStmt
           | FldDecl of string => CPP_Type ;

  class_info   (* bool in fields is true for static members *)
           = <| fields : (class_entry # bool # protection) list ;
                ancestors : string option |>
`;
(* A declaration can be used to declare (but not define a function).
   A VStrDec with a NONE class_info is the equivalent of
     struct foo;
   i.e., an incomplete declaration of a struct type
*)



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
  (erec_vdec P (VDecInit ty nm ee) = erec_exte P ee) /\
  (erec_vdec P (VStrDec nm copt) = T)
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

(* external declarations can appear at the top level of a translation unit *)
val _ = Hol_datatype`
  ext_decl = FnDefn of CPP_Type => string => (string # CPP_Type) list => CStmt
           | CMFnDefn of CPP_Type => string => string =>
                         (string # CPP_Type) list => CStmt
           | Decl of var_decl
`;

val _ = export_theory();

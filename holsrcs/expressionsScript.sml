(* C++ expressions *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open typesTheory memoryTheory

val _ = new_theory "expressions";

(* the standard binary operators *)
val c_binops = Hol_datatype
    `c_binops = CPlus | CMinus  | CLess  | CGreat | CLessE | CGreatE |
                CEq   | CTimes | CDiv   | CMod   | CNotEq`;

(* the standard unary operators *)
val c_unops = Hol_datatype`
  c_unops = CUnPlus | CUnMinus | CComp | CNot
`;

val fnid_def = type_abbrev("fnid", ``:CPP_ID``)
val _ = disable_tyabbrev_printing "fnid"

(* expressions *)
val _ = Hol_datatype
  `CExpr = Cnum of int
         | Cchar of int
         | Cnullptr of CPP_Type
                     (* BAD_ASSUMPTION: want to get rid of this *)
         | This
         | Var of CPP_ID
         | COr of CExpr => CExpr
         | CAnd of CExpr => CExpr
         | CCond of CExpr => CExpr => CExpr
         | CApBinary of c_binops => CExpr => CExpr
         | CApUnary of c_unops => CExpr
         | Deref of CExpr
         | Addr of CExpr
         | MemAddr of CPP_ID => StaticField
         | Assign of c_binops option => CExpr => CExpr
         | SVar of CExpr => CPP_ID
         | FnApp of CExpr => CExpr list
         | CommaSep of CExpr => CExpr
         | Cast of CPP_Type => CExpr
         | PostInc of CExpr
         | New of CPP_Type => CExpr list option

           (* two different forms of the typeid operator *)
         | ExpTypeID of CExpr
         | TyTypeID of CPP_Type

         (* these are "fake expression constructors" *)


            (* this represents the point where all arguments and function
               have been evaluated *)
         | FnApp_sqpt of CExpr => CExpr list

            (* this is an object lvalue, the string list is the sub-object
               path a la Wasserab et al for values of class type.  Elsewhere
               the list will be empty *)
         | LVal of num => CPP_Type => CPP_ID list

            (* this is a function l-value.  The expression argument represents
               the class object if the function is a member function, the
               type is the function type, i.e. of form Function rettype args *)
         | FVal of fnid => CPP_Type => CExpr option

            (* this is a "constructor function" l-value.  These can only arise
               when an object is created and are used in the function
               designator position.  They don't need to encode any information
               about types and object identities because this is all
               elsewhere.  The arguments are mdp (T iff constructing a
               most-derived object), subobjp (T iff constructing a sub-object
               within another object, NOT the inverse of mdp as members will
               be mdp and subobjp), the address where the object is
               being constructed, and the name of the class. *)
         | ConstructorFVal of bool => bool => addr => CPP_ID

            (* this is the value "returned" from a constructor call.  The
               boolean is true iff the class is a sub-object.
            *)
         | ConstructedVal of bool => addr => CPP_ID

             (* bool is mdp flag *)
         | DestructorCall of addr => CPP_ID
         | RValreq of CExpr
         | ECompVal of byte list => CPP_Type
         | EThrow of CExpr option
         | UndefinedExpr

`;

val _ = export_rewrites ["CExpr_size_def"]

val value_type_def = Define`
  (value_type (ECompVal v t) = t) /\
  (value_type (LVal a t p) = t)
`;


val rec_expr_P_def = Define`
    (rec_expr_P (Cnum i) P = P (Cnum i)) /\
    (rec_expr_P (Cchar c) P = P (Cchar c)) /\
    (rec_expr_P (Cnullptr t) P = P (Cnullptr t)) /\
    (rec_expr_P (Var n) P = P (Var n)) /\
    (rec_expr_P This P = P This) /\
    (rec_expr_P (COr e1 e2) P =
      P (COr e1 e2) /\ rec_expr_P e1 P /\ rec_expr_P e2 P) /\
    (rec_expr_P (CAnd e1 e2) P =
      P (CAnd e1 e2) /\ rec_expr_P e1 P /\ rec_expr_P e2 P) /\
    (rec_expr_P (CCond e1 e2 e3) P =
      P (CCond e1 e2 e3) /\ rec_expr_P e1 P /\ rec_expr_P e2 P /\
      rec_expr_P e3 P) /\
    (rec_expr_P (CApBinary f e1 e2) P =
      P (CApBinary f e1 e2) /\ rec_expr_P e1 P /\ rec_expr_P e2 P) /\
    (rec_expr_P (CApUnary f' e) P =
      P (CApUnary f' e) /\ rec_expr_P e P) /\
    (rec_expr_P (Deref e) P = P (Deref e) /\ rec_expr_P e P) /\
    (rec_expr_P (Addr e) P = P (Addr e) /\ rec_expr_P e P) /\
    (rec_expr_P (MemAddr cname fld) P = P (MemAddr cname fld)) /\
    (rec_expr_P (Assign fo e1 e2) P =
      P (Assign fo e1 e2) /\ rec_expr_P e1 P /\ rec_expr_P e2 P) /\
    (rec_expr_P (SVar e n) P =
      P (SVar e n) /\ rec_expr_P e P) /\
    (rec_expr_P (FnApp e args) P =
      P (FnApp e args) /\ rec_expr_P e P /\ rec_exprl_P args P) /\
    (rec_expr_P (CommaSep e1 e2) P =
      P (CommaSep e1 e2) /\ rec_expr_P e1 P /\ rec_expr_P e2 P) /\
    (rec_expr_P (Cast t e) P = P (Cast t e) /\ rec_expr_P e P) /\
    (rec_expr_P (PostInc e) P = P (PostInc e) /\ rec_expr_P e P) /\
    (rec_expr_P (FnApp_sqpt e args) P =
      P (FnApp_sqpt e args) /\ rec_expr_P e P /\ rec_exprl_P args P) /\
    (rec_expr_P (LVal a t p) P = P (LVal a t p)) /\
    (rec_expr_P (ExpTypeID e) P = P (ExpTypeID e) /\ rec_expr_P e P) /\
    (rec_expr_P (TyTypeID t) P = P (TyTypeID t)) /\
    (rec_expr_P (FVal fnid ty eopt) P =
       P (FVal fnid ty eopt) /\ rec_expr_opt eopt P) /\
    (rec_expr_P (RValreq e) P = P (RValreq e) /\ rec_expr_P e P) /\
    (rec_expr_P (ECompVal v t) P = P (ECompVal v t)) /\
    (rec_expr_P UndefinedExpr P = P UndefinedExpr) /\
    (rec_expr_P (ConstructorFVal mdp subobjp a nm) P =
       P (ConstructorFVal mdp subobjp a nm)) /\
    (rec_expr_P (ConstructedVal subp a cnm) P =
       P (ConstructedVal subp a cnm)) /\
    (rec_expr_P (DestructorCall a nm) P = P (DestructorCall a nm)) /\
    (rec_expr_P (New ty argsopt) P = P (New ty argsopt)) /\
    (rec_expr_P (EThrow eopt) P = P (EThrow eopt) /\ rec_expr_opt eopt P) /\
    (rec_exprl_P [] P = T) /\
    (rec_exprl_P (CONS e es) P = rec_expr_P e P /\ rec_exprl_P es P) /\
    (rec_expr_opt NONE P = T) /\
    (rec_expr_opt (SOME e) P = rec_expr_P e P)`;

open SingleStep
val rec_expr_simple = store_thm(
  "rec_expr_simple",
  (--`!P e. rec_expr_P e P ==> P e`--),
  REPEAT GEN_TAC THEN Cases_on `e` THEN
  SIMP_TAC (srw_ss()) [rec_expr_P_def]);

val rec_exprl_EVERY = store_thm(
  "rec_exprl_EVERY",
  (--`!el P. rec_exprl_P el P = EVERY (\e. rec_expr_P e P) el`--),
  INDUCT_THEN (listTheory.list_INDUCT) ASSUME_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [rec_expr_P_def]);
val _ = export_rewrites ["rec_exprl_EVERY"]

val e_cases =
  (map (rhs o snd o strip_exists) o
   strip_disj o snd o strip_forall o concl)
  (theorem "CExpr_nchotomy")

val has_no_undefineds_def = Define`
  has_no_undefineds e = rec_expr_P e (\e. ~(e = UndefinedExpr))
`;

val e_thms =
    map
      (SIMP_RULE (srw_ss()) [GSYM has_no_undefineds_def] o
       GEN_ALL o
       SIMP_RULE (srw_ss()) [rec_expr_P_def] o
       GEN_ALL o
       C SPEC has_no_undefineds_def)
      e_cases
val has_no_undefineds = save_thm("has_no_undefineds", LIST_CONJ e_thms)
val _ = export_rewrites ["has_no_undefineds"]

val side_affecting_def = Define`
  (side_affecting (Assign f e1 e2) = T) /\
  (side_affecting (FnApp fdes args) = T) /\
  (side_affecting (FnApp_sqpt fdes args) = T) /\
  (side_affecting (PostInc e)    = T) /\
  (side_affecting allelse = F)
`;
val syn_pure_expr_def = Define`
  syn_pure_expr e = rec_expr_P e ($~ o side_affecting)
`;

val has_sqpt = Define`
  (has_sqpt (FnApp f args) = T) /\
  (has_sqpt (FnApp_sqpt f args) = T) /\
  (has_sqpt (CommaSep e1 e2) = T) /\
  (has_sqpt (CAnd e1 e2) = T) /\
  (has_sqpt (COr e1 e2) = T) /\
  (has_sqpt (CCond e1 e2 e3) = T) /\
  (has_sqpt allelse = F)
`;
val seqpt_free_def = Define`
  seqpt_free e = rec_expr_P e ($~ o has_sqpt)
`;

val _ = export_theory();

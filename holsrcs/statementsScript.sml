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
  conttype = RVC of (CExpr -> CExpr) => se_info
           | LVC of (CExpr -> CExpr) => se_info
`;

(* term taken from grammar, as in 12.6.2 *)
val _ = type_abbrev("mem_initializer", ``:CPPname # CExpr list option``)

val _ = Hol_datatype `varlocn = RefPlace of num option => CPPname
                              | ObjPlace of num
`

val _ = Hol_datatype `TempArg = Template of CPPname
                              | TypeName of CPPname
                              | ExprArg of CExpr`;

val _ = Hol_datatype `decl_type = CTy of CType
                                | TempCall of CPPname => TempArg list`

(* a catch block can omit the parameter entirely (...), or can provide
   a lone type, or can provide a name and a type *)
val _ = type_abbrev("exn_pdecl", ``:(string option # CPP_Type) option``)


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
           | Trap of traptype => CStmt
           | Throw of ExtE option
           | Catch of CStmt => (exn_pdecl # CStmt) list
           | ClearExn (* machine generated *)

  ;

  ExtE     = NormE of CExpr => se_info
           | EStmt of CStmt => conttype

  ;

  var_decl = VDec of decl_type => CPPname
           | VDecInit of decl_type => CPPname => initializer
               (* init is the initial form of the initialising declarator *)
           | VDecInitA of decl_type => varlocn => initializer
               (* when space has been allocated, the form becomes the
                  VDecInitA, where the name is replaced by the location
                  of the start of the object in memory.  If the object is
                  actually a reference, then the location is just the
                  reference's name with an optional address for any
                  enclosing class.   *)

           | VStrDec of string => class_info option

           | VException of CExpr

  ;

  (* TODO: classes can contain nested classes
             - resolution(?): imagine a translated language where nested
                  classes can be declared in a class scope in advance of the
                  enclosing class's definition. *)
  (* TODO: allow declaration of friends *)
  class_entry =

             CFnDefn of CPP_Type => string => (string # CPP_Type) list =>
                        CStmt
               (* function definitions within a class must be of member
                  function for that class, it is not legit to write
                     class A {
                        class B { int f(void); };
                        int B::f(void) { ... }
                     }
                  so the first string below has to be string and not
                  CPPname.   See 9.3 p2 : "a member function definition that
                  occurs outside of the class definition shall appear in a
                  namespace scope enclosing the class definition".  *)

           | FldDecl of string => CPP_Type
           | Constructor of (string # CPP_Type) list =>
                            mem_initializer list =>
                            CStmt option
           | Destructor of CStmt option;
                            (* bool = user-defined or not *)

  class_info =
             <| fields : (class_entry # bool # protection) list ;
                   (* bool in fields is true for static members *)

                ancestors : (CPPname # bool # protection) list
                   (* bool indicates virtuality *)
             |> ;

  initializer =
             (* see 8.5 p12 for discussion of difference *)
             DirectInit0 of CExpr list
                (* The parameters given to a direct initialisation - this is
                   the form that appears in user-provided abstract syntax. *)
           | DirectInit of ExtE
                (* This form is only used for the initialisation of objects of
                   class type.  The expression will be a FnApp where the
                   arguments are the arguments that appear in the source,
                   and where the function will be the place-holder
                   ConstructorFVal. *)
           | CopyInit of ExtE
                (* copy initialisation of classes also results in a constructor
                   being called, once the expression has been evaluated and
                   found to be of the right type through a conversion
                   sequence *)
`;
(* A declaration can be used to declare (but not define a function).
   A VStrDec with a NONE class_info is the equivalent of
     struct foo;
   i.e., an incomplete declaration of a struct type
*)




val _ = export_theory();

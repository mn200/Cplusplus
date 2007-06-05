(* C states - to be expanded into C++ states *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open utilsTheory typesTheory memoryTheory expressionsTheory statementsTheory
     environmentsTheory

val _ = new_theory "states";
(* actually also the theory of declaration forms *)

(* information about a function, once declared.  If a function has only
   been given a prototype, there will be an entry for it in the state's
   typemap, but nothing else.  *)
val _ = Hol_datatype `fn_info = <| return_type : CPP_Type ;
                                   parameters  : (string # CPP_Type) list ;
                                   body        : CStmt |>`;




(* BAD_ASSUMPTION: locmap maps from natural numbers;
                   should maybe map from pointer values *)

(* In the classmap and gclassmap fields, use the NONE value to
   indicate a class has an incomplete declaration.  Can't use the
   empty list of fields for C++, as C++ allows declaration of empty
   structs/classes (unlike C) (9 p1).

   NOTE, moreover that an empty C++ struct has non-zero size. (9 p3) *)


val _ = type_abbrev("construction_locn",
                    ``:addr # CPP_ID # CPP_ID list``)

val _ = Hol_datatype`
  constructed = NormalConstruct of construction_locn
              | SubObjConstruct of construction_locn
`;

val _ = Hol_datatype `
   state = <| 
     allocmap : addr -> bool ;  (* the set of stack-allocated addresses *)
     hallocmap: addr -> bool ;  (* the set of heap-allocated addresses *)
     constmap : addr -> bool ;  (* the set of read-only addresses *)
     initmap  : addr -> bool ;  (* the set of initialised addresses *)

     fnmap    : fnid |-> fn_info ;
                (* map from function 'names' to type information about
                   the given functions *)
     fnencode : fnid |-> byte list ;
                (* map encoding function 'name' as a byte sequence
                   so that its address can be stored in memory *)
     fndecode : byte list |-> fnid ;
                (* map inverting fnencode *)

     genv: environment ; (* non-local environment *)
     env : environment ; (* local version of the above *)

     locmap   : addr -> byte ;
                (* memory.  Domain might also be ( void * ) words *)

     stack    : (environment #CExpr option) list ;
                (* stack of environment and this info.  Updated
                   as blocks are entered and left *)

     thisvalue: CExpr option ;
                (* the value (i.e., this will always be an ECompVal
                   with a pointer value) of the this expression *)

     blockclasses : constructed list list ;
     exprclasses  : construction_locn list list
       (* the stack of objects that need to have destructors
          called.  First field is for automatic objects that have
          block-delimited lifetimes.  Second is for temporary
          objects that need to be destroyed at the end of the
          full enclosing expression *)
     ;

     current_exns : CExpr list  
                    (* stack of exceptions that might be subjected 
                       to a bare throw *)
   |>`;
val _ = type_abbrev("CState", ``:state``)

val initial_state_def = Define`
  initial_state = <| allocmap := {};
                     hallocmap := {};
                     env := empty_env ;
                     genv := empty_env ;
                     fnmap := FEMPTY;
                     fnencode := FEMPTY;
                     fndecode := FEMPTY;
                     initmap := {};

                     (* note that there is no value provided for locmap *)

                     stack := [];
                     thisvalue := NONE ;

                     blockclasses := [[]];
                     exprclasses := [[]] |>
`

(* function that updates memory with a value *)
val val2mem_def = Define`
  val2mem s (loc:num) v =
       s with locmap updated_by
                (\lmp x. if loc <= x /\ x < loc + LENGTH v then
                           EL (x - loc) v
                         else lmp x)
`;

(* function that extracts values from memory *)
val mem2val_def = Define`
  (mem2val s loc 0 = []) /\
  (mem2val s loc (SUC n) = s.locmap loc :: mem2val s (loc+1) n)
`;
val _ = export_rewrites ["mem2val_def"]

(* SANITY (trivial) *)
val mem2val_LENGTH = store_thm(
  "mem2val_LENGTH",
  --`!sz s n. LENGTH (mem2val s n sz) = sz`--,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []);

(* pointer encoding and decoding *)
(* if the list of strings is not empty, it is the path
   to the sub-object, which will be of the type specified.

   E.g., if the class is just appearing "as itself", then
   the list will be two elements long, consisting of the class name twice *)

(* argument to ptr_encode are same as those to LVal *)
val _ = new_constant(
  "ptr_encode",
  ``:state -> num -> CPP_Type -> CPP_ID list -> byte list option``)

val default_path_def = Define`
  (default_path (Class cn) = (cn, [cn]))
`;



val _ = export_theory();

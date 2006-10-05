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
     staticsTheory

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



val _ = Hol_datatype
  `state = <| allocmap : num -> bool ;
                         (* the set of allocated addresses *)

              fnmap    : fnid |-> fn_info ;
                         (* map from function 'names' to type information about
                            the given functions *)

              fnencode : fnid |-> byte list ;
                         (* map encoding function 'name' as a byte sequence
                            so that its address can be stored in memory *)

              fndecode : byte list |-> fnid ;
                         (* map inverting fnencode *)

              gclassmap: string |-> class_info option ;
                         (* the global map from class names to class info;
                            can be dynamically overridden by local class
                            declarations *)

              gtypemap : string |-> CPP_Type ;
                         (* global map giving types to global variables.
                            Can be dynamically overridden by local variables *)

              gvarmap  : string |-> (num # string list) ;
                         (* global map giving adddresses and paths for
                            global vars; can be dynamically overridden.  See
                            varmap for explanation of why paths are necessary
                         *)

              initmap  : num -> bool ;
                         (* the set of initialised addresses *)

              locmap   : num -> byte ;
                         (* memory.  Domain should be ( void * ) words *)

              stack    : ((string |-> class_info option) #
                          (string |-> CPP_Type) #
                          (string |-> (num # string list)) #
                          CExpr option) list ;
                         (* stack of class, type and var info.  Updated
                            as blocks are entered and left *)

              statics  : string # string |-> (num # string list) ;
                         (* map giving addresses and paths for static data
                            members. Domain is classname x fieldname *)

              classmap : string |-> class_info option;
                         (* local, dynamically changing class map *)

              typemap  : string |-> CPP_Type ;
                         (* local information about types of variables *)

              varmap   : string |-> (num # string list) ;
                         (* address and path information for local variables.
                            The path information has to be present because
                            variables can be references, and these can be
                            (initialised to be) references to sub-classes. *)

              thisvalue: CExpr option
                         (* the value (i.e., this will always be an ECompVal
                            with a pointer value) of the this expression *)
             |>`;
val _ = type_abbrev("CState", ``:state``)

val initial_state_def = Define`
  initial_state = <| allocmap := {};
                     fnmap := FEMPTY;
                     fnencode := FEMPTY;
                     fndecode := FEMPTY;
                     gclassmap := FEMPTY;
                     gtypemap := FEMPTY;
                     gvarmap := FEMPTY;
                     initmap := {};  (* note that there is no value provided for locmap *)
                     stack := [];
                     classmap := FEMPTY;
                     typemap := FEMPTY;
                     varmap := FEMPTY ;
                     thisvalue := NONE |>
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

val install_global_maps_def = Define`
  install_global_maps s =
         s with <| gvarmap := s.varmap ;
                   gclassmap := s.classmap;
                   gtypemap := s.typemap |>
`;



(* pointer encoding and decoding *)
(* if the list of strings is not empty, it is the path
   to the sub-object, which will be of the type specified.

   E.g., if the class is just appearing "as itself", then
   the list will be two elements long, consisting of the class name twice *)
val _ = new_constant(
  "ptr_encode",
  ``:state # CPP_Type -> num # string list -> byte list option``)

val _ = new_constant(
  "ptr_decode",
  ``:state # CPP_Type -> byte list -> (num # string list) option``)

(* BAD_ASSUMPTION *)
(* would be nice to have this as an Isabelle style locale assumption.  *)
val ptr_inverse = new_axiom(
  "ptr_inverse",
  ``(ptr_encode (s,ty) info = SOME result) ==>
    (ptr_decode (s,ty) result = SOME info)``)

val default_path_def = Define`
  (default_path (Class cn) = [cn]) /\
  (default_path otherwise = [])
`;



val _ = export_theory();

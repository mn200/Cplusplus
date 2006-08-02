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
              fnmap    : fnid |-> fn_info ;
              fnencode : fnid |-> byte list ;
              fndecode : byte list |-> fnid ;
              gclassmap: string |-> class_info option ;
              gtypemap : string |-> CPP_Type ;
              gvarmap  : string |-> (num # string list) ;
              initmap  : num -> bool ;
              locmap   : num -> byte ;
              stack    : ((string |-> class_info option) #
                          (string |-> CPP_Type) #
                          (string |-> (num # string list)) #
                          CExpr option) list ;
              classmap : string |-> class_info option;
              typemap  : string |-> CPP_Type ;
              varmap   : string |-> (num # string list) ;
              thisvalue: CExpr option
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

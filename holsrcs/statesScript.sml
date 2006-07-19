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
  `CState = <| allocmap : num -> bool ;
               fnmap    : string |-> fn_info ;
               fnvals   : string |-> byte list ;
               fndecode : byte list |-> string ;
               gclassmap: string |-> class_info option ;
               gtypemap : string |-> CPP_Type ;
               gvarmap  : string |-> num ;
               initmap  : num -> bool ;
               locmap   : num -> byte ;
               stack    : ((string |-> class_info option) #
                           (string |-> CPP_Type) #
                           (string |-> num)) list ;
               classmap : string |-> class_info option;
               typemap  : string |-> CPP_Type ;
               varmap   : string |-> num |>`;

val initial_state_def = Define`
  initial_state = <| allocmap := {};
                     fnmap := FEMPTY;
                     fnvals := FEMPTY;
                     fndecode := FEMPTY;
                     gclassmap := FEMPTY;
                     gtypemap := FEMPTY;
                     gvarmap := FEMPTY;
                     initmap := {};  (* note that there is no value provided for locmap *)
                     stack := [];
                     classmap := FEMPTY;
                     typemap := FEMPTY;
                     varmap := FEMPTY |>
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

val objfield_def = Define`
  (objfield (CFnDefn retty nm args body, static, prot) = NONE) /\
  (objfield (FldDecl nm ty, static, prot) =
    if object_type ty /\ ~static then SOME(nm,ty) else NONE)
`

val mapPartial_def = Define`
  (mapPartial f [] = []) /\
  (mapPartial f (h::t) = case f h of SOME x -> x :: mapPartial f t
                                  || NONE -> mapPartial f t)
`


(* looking up a field's information (type and index) requires a map from
   class name to (name#type) list.   This is the lookup function that only
   returns fields and not functions *)
val lfimap_def = Define`
  lfimap s = (\ci. mapPartial objfield ci.fields) o_f deNONE s.classmap
`;



(* BAD ASSUMPTION: no classes are abstract *)
(* type-checking requires a variety of pieces of information, which we derive
   from a state with this function *)
val expr_type_comps_def = Define`
  expr_type_comps s =
    <| class_fields := lfimap s;
       var_types := s.typemap ;
       abs_classes := {} |>
`;

(* sizeof calculations expect to find a map from class name to a list
   of types (the class's (non-static) fields.  This function calculates
   that map from a classmap *)
val sizeofmap_def = Define`
  sizeofmap s = MAP SND o_f lfimap s
`;






val _ = export_theory();

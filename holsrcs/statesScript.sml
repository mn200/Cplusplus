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

val _ = Hol_datatype`
  fnid = GlobalFn of string | MFn of string => string
`;


val _ = Hol_datatype
  `CState = <| allocmap : num -> bool ;
               fnmap    : fnid |-> fn_info ;
               fnvals   : fnid |-> byte list ;
               fndecode : byte list |-> fnid ;
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






val _ = export_theory();

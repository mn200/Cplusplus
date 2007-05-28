(* C++ environments, handling namespaces and nested classes *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local
  open wordsTheory integer_wordTheory finite_mapTheory fmaptreeTheory
in end

(* C++ ancestor theories  *)
open utilsTheory typesTheory memoryTheory expressionsTheory statementsTheory

val _ = new_theory "environments";


(* In the classmap and gclassmap fields, use the NONE value to
   indicate a class has an incomplete declaration.  Can't use the
   empty list of fields for C++, as C++ allows declaration of empty
   structs/classes (unlike C) (9 p1).

   NOTE, moreover that an empty C++ struct has non-zero size. (9 p3) *)


(* those sorts of things that can get implicitly declared and defined by
   the implementation if the user does not provide them *)
val _ = Hol_datatype`
  implicitly_definable = DefaultConstructor
                       | Destructor
                       | CopyConstructor
                       | CopyAssignment
`;

(* when a class name is looked up, it may get
     - that the name is not in the domain of the map, which means that the
       name is not the name of a class at all
     - the name maps to NONE, which means it has been declared only,
       as in
          class foo;
     - the name maps to SOME(cinfo, user_provided) where cinfo is the
       information about the class, and user_provided is the set of things
       that were given by the user (and didn't need filling in by the
       implementation)
*)

val _ = type_abbrev("state_class_info",
                    ``:(class_info # implicitly_definable set) option``)


val _ = type_abbrev("construction_locn",
                    ``:addr # CPP_ID # CPP_ID list``)

val _ = Hol_datatype`
  class_envinfo = <|
    (* ironically, the location of the static variables is only available
       dynamically, as classes are initialised *)
    statvars : string |-> addr # CPP_ID list ;
    info     : state_class_info ;
    refs     : string # addr |-> addr # CPP_ID list
|>`
val empty_class_envinfo_def = Define`
  empty_class_envinfo = <| statvars := FEMPTY; info := NONE; refs := FEMPTY |>
`;

val _ = type_abbrev ("class_env", ``:(StaticField,class_envinfo)fmaptree``)

val _ = Hol_datatype`
  envinfo = <| varmap   : string |-> addr # CPP_ID list ;
               typemap  : StaticField |-> CPP_Type ;
               classenv : StaticField |-> class_env
|>`;

(* strings are the keys here, because these are ever-deepening
   namespace identifiers *)
val _ = type_abbrev ("environment", ``:(string,envinfo)fmaptree``)

val empty_env_def = Define`
  empty_env = FTNode <| varmap := FEMPTY ;
                        typemap := FEMPTY ;
                        classenv := FEMPTY |>
                     FEMPTY
`;

val lookup_nspace_def = Define`
  (lookup_nspace env [] = env) /\
  (lookup_nspace env (h::t) = lookup_nspace (map env ' h) t)
`;

val celookup_class_def = Define`
  (celookup_class cenv (IDConstant b [] sf) = FLOOKUP cenv sf) /\
  (celookup_class cenv (IDConstant b (h :: t) sf) =
     case FLOOKUP cenv h of
        NONE -> NONE
     || SOME cei -> celookup_class (map cei) (IDConstant b t sf))
`;

val elookup_class_def = Define`
  (elookup_class env (IDConstant b [] sf) =
     FLOOKUP ((item env).classenv) sf) /\
  (* if top name might be a namespace name or a class name, class names take
     priority *)
  (elookup_class env (IDConstant b (SFName h :: t) sf) =
      if SFName h IN FDOM (item env).classenv then
        celookup_class (item env).classenv (IDConstant b (SFName h :: t) sf)
      else
        case FLOOKUP (map env) h of
           NONE -> NONE
        || SOME e' -> elookup_class e' (IDConstant b t sf)) /\
  (* otherwise, the head name is a template application, which must be a
     class name rather than a namespace name *)
  (elookup_class env (IDConstant b sfs sf2) =
      celookup_class (item env).classenv (IDConstant b sfs sf2))
`;

val is_class_name_env_def = Define`
  (is_class_name_env env id = ?c. elookup_class env id = SOME c)
`;

val update_classenv_def = Define`
  (update_classenv [] i (cenv : StaticField |-> class_env) = NONE) /\
  (update_classenv [h] i cenv =
     SOME (cenv |+ (h, FTNode <| info := SOME i ;
                                 statvars := FEMPTY ;
                                 refs := FEMPTY |>
                              FEMPTY))) /\
  (update_classenv (h::t) i cenv =
     if h IN FDOM cenv then
       case update_classenv t i (map (cenv ' h)) of
          NONE -> NONE
       || SOME ce' -> SOME (cenv |+ (h, FTNode (item (cenv ' h)) ce'))
     else NONE)
`;

(* class id has no namespace constituents - i.e., this is OK for a local
   class, but not OK for a top-level declaration... *)
val update_class_def = Define`
  update_class (IDConstant b sfs sf) i env =
     case update_classenv (sfs ++ [sf]) i (item env).classenv of
        NONE -> NONE
     || SOME ce' -> SOME (FTNode (item env with classenv := ce')
                                 (map env))
`;


val _ = export_theory()


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
                    ``:addr # class_spec # class_spec list``)

val _ = Hol_datatype`
  class_envinfo = <|
    (* ironically, the location of the static variables is only available
       dynamically, as classes are initialised *)
    statvars : string |-> addr # CPP_ID list ;
    info     : state_class_info ;
    refs     : string # addr |-> addr # CPP_ID list
|>`


val _ = type_abbrev ("class_env", ``:(StaticField,class_envinfo)fmaptree``)

val _ = Hol_datatype`
  envinfo = <| varmap   : string |-> addr # CPP_ID list ;
               typemap  : StaticField |-> CPP_Type ;
               classenv : StaticField |-> class_env ;
               funs     : StaticField |-> CPP_ID (* function's fullname *)
|>`;

(* strings are the keys here, because these are ever-deepening
   namespace identifiers *)
val _ = type_abbrev ("environment", ``:(string,envinfo)fmaptree``)

val empty_env_def = Define`
  empty_env = FTNode <| varmap := FEMPTY ;
                        typemap := FEMPTY ;
                        classenv := FEMPTY ;
                        funs := FEMPTY |>
                     FEMPTY
`;

val lookup_nspace_def = Define`
  (lookup_nspace env [] = env) /\
  (lookup_nspace env (h::t) = lookup_nspace (map env ' h) t)
`;

val elookup_class_def = Define`
  (elookup_class env (IDFld id fld) =
     case elookup_class env id of
        NONE -> NONE
     || SOME cenv -> FLOOKUP (map cenv) fld) /\
  (elookup_class env (IDConstant (b, [], n)) =
      FLOOKUP ((item env).classenv) (SFName n)) /\
  (elookup_class env (IDConstant (b, h :: t, n)) =
      case FLOOKUP (map env) h of
         NONE -> NONE
      || SOME m -> elookup_class m (IDConstant(b, t, n))) /\
  (elookup_class env (IDTempCall (TemplateConstant (b, [], n)) targs) =
      FLOOKUP ((item env).classenv) (SFTempCall n targs)) /\
  (elookup_class env (IDTempCall (TemplateConstant (b, h::t, n)) targs) =
      case FLOOKUP (map env) h of
         NONE -> NONE
      || SOME m -> elookup_class m
                         (IDTempCall (TemplateConstant (b, t, n)) targs)) /\
  (elookup_class env _ = NONE)
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

val update_class_def = Define`
  update_class id i env =
     let (bid, sfs) = strip_field id
     in
       case strip_nspaces bid of
          NONE -> NONE
       || SOME ((b, ns), sf) ->
            fupd_at_path ns
              (\ft. case update_classenv (sf::sfs) i (item ft).classenv of
                       NONE -> NONE
                    || SOME ce' -> SOME (FTNode (item ft with classenv := ce')
                                                (map ft)))
              env
`


val id_GSPEC_cases = store_thm(
  "id_GSPEC_cases",
  ``{ id | P id } =
      { IDVar s | P (IDVar s) } UNION
      { IDFld id sf | P (IDFld id sf) } UNION
      { IDTempCall tid targs | P (IDTempCall tid targs) } UNION
      { IDConstant tn | P (IDConstant tn) }``,
  SRW_TAC [][EXTENSION] THEN Cases_on `x` THEN SRW_TAC [][]);

val option_case_lemma = prove(
  ``(option_case NONE f x = SOME y) = ?z. (x = SOME z) /\ (f z = SOME y)``,
  Cases_on `x` THEN SRW_TAC [][]);

(* SANITY *)
(* empty list is an error case *)
val class_part_def = Define`
  (class_part (IDFld id fld) =
     case class_part id of
        [] -> []
     || list -> list ++ [fld]) /\
  (class_part (IDConstant(b,l,n)) = [SFName n]) /\
  (class_part (IDTempCall (TemplateConstant(b,l,n)) targs) =
              [SFTempCall n targs]) /\
  (class_part _ = [])
`;

val option_case_lemma2 = prove(
  ``option_case NONE (\x. SOME x) y = y``,
  Cases_on `y` THEN SRW_TAC [][]);

val list_case_lemma = prove(
  ``(list_case NONE f x = SOME y) =
    ?h t. (x = h :: t) /\ (f h t = SOME y)``,
  Cases_on `x` THEN SRW_TAC [][]);

val elookup_class_apply_path = store_thm(
  "elookup_class_apply_path",
  ``!env id.
       elookup_class env id =
          case class_part id of
             [] -> NONE
          || h::t -> (case apply_path (SND (id_namespaces id)) env of
                         NONE -> NONE
                      || SOME e -> (case FLOOKUP (item e).classenv h of
                                       NONE -> NONE
                                    || SOME ce -> apply_path t ce))``,
  HO_MATCH_MP_TAC (theorem "elookup_class_ind") THEN
  SRW_TAC [][elookup_class_def, fmaptreeTheory.apply_path_def, class_part_def,
             typesTheory.id_namespaces_def, typesTheory.tid_namespaces_def,
             option_case_lemma2] THEN
  TRY (SRW_TAC [][finite_mapTheory.FLOOKUP_DEF] THEN NO_TAC) THEN
  Cases_on `class_part id` THEN SRW_TAC [][] THEN
  Cases_on `apply_path (SND (id_namespaces id)) env` THEN SRW_TAC [][] THEN
  Cases_on `FLOOKUP (item x).classenv h` THEN SRW_TAC [][] THEN
  SRW_TAC [][fmaptreeTheory.apply_path_SNOC]);

(* tricksy
val env_classes_FINITE = store_thm(
  "env_classes_FINITE",
  ``!env. FINITE { id | is_class_name_env env id }``,
  SIMP_TAC (srw_ss()) [is_class_name_env_def] THEN
  SRW_TAC [DNF_ss][elookup_class_apply_path, option_case_lemma,
                   list_case_lemma] THENL [
    Q_TAC SUFF_TAC `{IDVar s | F} = {}` THEN1 SRW_TAC [][] THEN
    SRW_TAC [][EXTENSION],
    SRW_TAC [][option_case_lemma]
*)




val _ = export_theory()


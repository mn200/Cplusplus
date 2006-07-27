(* The C++ class hierarchy, and functions on it, derived from information
   stored in a state *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local
  open wordsTheory integer_wordTheory finite_mapTheory containerTheory
in end

(* C++ ancestor theories  *)
open statesTheory

val _ = new_theory "class_info";

(* BAD_ASSUMPTION: for the moment, our hierarchies only allow one
   ancestor class at most
*)

(* c2 is an ancestor of c1 *)
val ancestor_def = Define`
  ancestor s c1 c2 = c1 IN FDOM (deNONE s.classmap) /\
                     ((THE(s.classmap ' c1)).ancestors = SOME c2)
`;


(* Appending paths.  (Wasserab et al., section 3.4) *)
val path_app_def = Define`
 path_app p1 p2 = if LAST p1 = HD p2 then p1 ++ TL p2 else p2
`;
val _ = set_fixity "^" (Infixl 500)
val _ = overload_on("^", ``path_app``)

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,2),
                                  BeginFinalBlock(PP.CONSISTENT,0), TM,
                                  BreakSpace(1,0), TOK "<", BreakSpace(1,0)],
                   term_name = "ancestor",
                   fixity = Infix(NONASSOC, 460) }


(* See the Subjobjs_R relation of Wasserab et al. *)
val (rsubobjs_rules, rsubobjs_ind, rsubobjs_cases) = Hol_reln`
  (!C s. C IN FDOM (deNONE s.classmap) ==> rsubobjs s (C, [C]))

    /\

  (!C Cs D s.
      s |- C < D /\ rsubobjs s (D, Cs)
   ==>
      rsubobjs s (C, C::Cs))
`;

val calc_rsubobjs = store_thm(
  "calc_rsubobjs",
  ``(C,Cs) IN rsubobjs s =
       (Cs = [C]) /\ C IN FDOM (deNONE s.classmap) \/
       ?D Cs'. s |- C < D /\ (D,Cs') IN rsubobjs s /\
                 (Cs = C::Cs')``,
  SRW_TAC [][SPECIFICATION] THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [rsubobjs_cases])) THEN
  SRW_TAC [][SPECIFICATION] THEN
  METIS_TAC [])

(* The Subobjs relation of Wasserab et al.  Because of the absence of
   multiple inheritance, let alone virtual (shared) ancestors, this is
   currently the same as rsubobjs *)
val (subobjs_rules, subobjs_ind, subobjs_cases) = Hol_reln`
  (!C Cs s. rsubobjs s (C,Cs) ==> subobjs s (C,Cs))
`;

val calc_subobjs = store_thm(
  "calc_subobjs",
  ``(C,Cs) IN subobjs s = (C,Cs) IN rsubobjs s``,
  SRW_TAC [][SPECIFICATION] THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [subobjs_cases])) THEN
  SRW_TAC [][]);


val pord1_def = Define`
  pord1 (s, C) Cs Ds = (Cs = FRONT Ds) /\ (C,Cs) IN rsubobjs s /\
                       (C,Ds) IN rsubobjs s
`;


(* s |- path C to D unique *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Suffix 465,
                  pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,0),
                                 TOK "path", BreakSpace(1,0), TM,
                                 BreakSpace(1,0), TOK "to", BreakSpace(1,0),
                                 TM, BreakSpace(1,0), TOK "unique"],
                  term_name = "unique_path"}

val unique_path_def = Define`
  s |- path C to D unique = ?!Cs. subobjs s (C,Cs) /\ (LAST Cs = D)
`

(* s |- path C to D via Cs *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix (NONASSOC, 460),
                  pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,0),
                                 TOK "path", BreakSpace(1,0), TM,
                                 BreakSpace(1,0), TOK "to", BreakSpace(1,0),
                                 TM, BreakSpace(1,0), TOK "via",
                                 BreakSpace(1,0)],
                  term_name = "path_via"}
val path_via_def = Define`
  s |- path C to D via Cs = (C,Cs) IN subobjs s /\ (LAST Cs = D)
`;

(* finding fields W et al. 5.1.3 *)
val fieldname_def = Define`
  (fieldname (FldDecl n ty) = n) /\
  (fieldname (CFnDefn retty n args body) = n)
`

val fieldtype_def = Define`
  (fieldtype (FldDecl n ty) = ty) /\
  (fieldtype (CFnDefn retty n args body) = Function retty (MAP SND args))
`;

val FieldDecls_def = Define`
  FieldDecls s C fnm =
     { (Cs, ty) | (C,Cs) IN subobjs s /\
                  LAST Cs IN FDOM (deNONE s.classmap) /\
                  ?cinfo fld. (deNONE s.classmap ' (LAST Cs) = cinfo) /\
                              MEM fld cinfo.fields /\
                              (fieldname (FST fld) = fnm) /\
                              (fieldtype (FST fld) = ty) }
`;


(* s |- C has least fld -: ty via Cs *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix (NONASSOC, 460),
                  pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,0),
                                 TM, BreakSpace(1,0),
                                 TOK "has", BreakSpace(1,0),
                                 TOK "least", BreakSpace(1,0),
                                 PPBlock([TM, BreakSpace(1,0),
                                          TOK "-:", BreakSpace(1,0), TM],
                                         (PP.CONSISTENT, 0)),
                                 BreakSpace(1,0), TOK "via", BreakSpace(1,0)],
                  term_name = "fieldty_via"}
val fieldty_via_def = Define`
  s |- C has least fld -: ty via Cs =
         (Cs,ty) IN FieldDecls s C fld /\
         !Cs' ty'. (Cs',ty') IN FieldDecls s C fld ==>
                   RTC (pord1 (s,C)) Cs Cs'
`


(* nsdmembers (non-static data-members) *)
val nsdmembers_def = Define`
  nsdmembers s c =
    case FLOOKUP (deNONE s.classmap) c of
       NONE -> NONE
    || SOME cinfo ->
         SOME
           (mapPartial
              (\ci. case ci of
                       (CFnDefn ret nm args bod, stat, prot) -> NONE
                    || (FldDecl nm ty, stat, prot) -> if stat then NONE
                                                      else SOME (nm,ty))
              cinfo.fields)
`

(* p is the set of all the subobjs for a given class *)
val class_layout_def = Define`
  class_layout (p : string list set) = SET_TO_LIST p
`

val class_layout_SING = store_thm(
  "class_layout_SING",
  ``class_layout {p} = [p]``,
  SRW_TAC [][class_layout_def, containerTheory.SET_TO_LIST_THM, CHOICE_SING])
val _ = export_rewrites ["class_layout_SING"]

(* This can be passed to the sizeof relation in order to calculate the size
   and offset information for classes.  *)
(* BAD_ASSUMPTION:
     this doesn't allow for the inclusion of vptr entries in classes
*)
val class_elems_def = Define`
  class_elems s =
    FUN_FMAP (\c. FLAT (MAP (\cpath. THE (nsdmembers s (LAST cpath)))
                            (class_layout { so | (c,so) IN subobjs s })))
             (FDOM s.classmap)
`

(* SANITY *)
val class_elems_example1 = store_thm(
  "class_elems_example1",
  ``class_elems
       <| classmap :=
             FEMPTY |+
               ("c",
                SOME <| fields := [(FldDecl "foo" (Unsigned Int), F, Public);
                                   (FldDecl "bar" Bool, T, Public);
                                   (FldDecl "d" (Class "d"), F, Private);
                                   (FldDecl "baz" BChar, F, Public)];
                        ancestors := NONE |>) |+
               ("d",
                SOME <| fields := [(FldDecl "q" (Signed Int), F, Public)];
                        ancestors := NONE |>) |> ' "c" =
       [("foo", Unsigned Int); ("d", Class "d"); ("baz", BChar)]``,
  SRW_TAC [][finite_mapTheory.FLOOKUP_UPDATE, nsdmembers_def,
             ancestor_def, class_elems_def, calc_subobjs,
             Once calc_rsubobjs, finite_mapTheory.FUN_FMAP_DEF,
             finite_mapTheory.FAPPLY_FUPDATE_THM]);

(* SANITY *)
val class_elems_example2 = store_thm(
  "class_elems_example2",
  ``class_elems
       <| classmap :=
             FEMPTY |+
               ("c",
                SOME <| fields := [(CFnDefn Bool "f" [] (Block F [][]), F,
                                    Public);
                                   (FldDecl "bar" Bool, T, Public)];
                        ancestors := SOME "d" |>) |+
               ("d",
                SOME <| fields := [(FldDecl "q" (Signed Int), F, Public)];
                        ancestors := NONE |>) |> ' "c" =
       [("q", Signed Int)]``,
  SRW_TAC [][finite_mapTheory.FLOOKUP_UPDATE,
             ancestor_def, class_elems_def, calc_subobjs,
             Once calc_rsubobjs, finite_mapTheory.FUN_FMAP_DEF,
             finite_mapTheory.FAPPLY_FUPDATE_THM] THEN
  ONCE_REWRITE_TAC [calc_rsubobjs] THEN
  SRW_TAC [][ancestor_def, GSPEC_OR, INSERT_UNION_EQ] THEN
  Q.SUBGOAL_THEN `!x y. ~(x = y) ==> ((class_layout {x;y} = [x;y]) \/
                                      (class_layout {x;y} = [y;x]))`
    (Q.SPECL_THEN [`["c"]`, `["c"; "d"]`] MP_TAC)
  THENL [
    SRW_TAC [][class_layout_def] THEN
    SRW_TAC [][containerTheory.SET_TO_LIST_THM] THEN
    SRW_TAC [CONJ_ss][REST_DEF, DELETE_INSERT] THEN
    SRW_TAC [][containerTheory.SET_TO_LIST_THM, CHOICE_SING] THEN
    Q.ISPEC_THEN `{x:string list;y}` MP_TAC CHOICE_DEF THEN SRW_TAC [][],
    ALL_TAC
  ] THEN
  SRW_TAC [][] THEN
  SRW_TAC [][nsdmembers_def, finite_mapTheory.FLOOKUP_UPDATE]);


(* ---------------------------------------------------------------------- *)

(* looking up a field's information (type and index) requires a map from
   class name to (name#type) list.   This is the lookup function that only
   returns fields and not functions *)
(* BAD_ASSUMPTION: this doesn't handle masking of names properly *)
val lfimap_def = Define`
  lfimap s = class_elems s
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

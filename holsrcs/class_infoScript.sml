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

(* similarly, direct base classes, in order of declaration *)
val get_direct_bases_def = Define`
  get_direct_bases s cnm : CPPname list =
    [THE (THE (s.classmap ' cnm)).ancestors]
`

val get_virtual_bases_def = Define`
  get_virtual_bases s cnm : CPPname list = []
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

(* finding fields W et al. 5.1.3
   - omitting constructors and destructors as these can't be called normally *)
val fieldname_def = Define`
  (fieldname (FldDecl n ty) = n) /\
  (fieldname (CFnDefn retty n args body) = n)
`

(* again, omitting constructors and destructors as these can't be called *)
val fieldtype_def = Define`
  (fieldtype (FldDecl n ty) = ty) /\
  (fieldtype (CFnDefn retty n args body) = Function retty (MAP SND args))
`;

(* those fields for which the above two predicates are well-defined *)
val okfield_def = Define`
  (okfield (FldDecl n ty) = T) /\
  (okfield (CFnDefn retty n args body) = T) /\
  (okfield _ = F)
`;

val FieldDecls_def = Define`
  FieldDecls s C fnm =
     { (Cs, ty) | (C,Cs) IN subobjs s /\
                  LAST Cs IN FDOM (deNONE s.classmap) /\
                  ?cinfo centry staticp prot.
                      (deNONE s.classmap ' (LAST Cs) = cinfo) /\
                      MEM (centry,staticp,prot) cinfo.fields /\
                      ~staticp /\
                      okfield centry /\
                      (fieldname centry = fnm) /\
                      (fieldtype centry = ty) }
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
                                                      else SOME (nm,ty)
                    || _ -> NONE)
              cinfo.fields)
`

(* p is the set of all the subobjs for a given class *)
(* use of SET_TO_LIST means that one particular ordering of the set is taken
   and used to determine the order in which the sub-objects appear *)
val class_layout_def = Define`
  class_layout (p : CPPname list set) = SET_TO_LIST p
`

val class_layout_SING = store_thm(
  "class_layout_SING",
  ``class_layout {p} = [p]``,
  SRW_TAC [][class_layout_def, containerTheory.SET_TO_LIST_THM, CHOICE_SING])
val _ = export_rewrites ["class_layout_SING"]

(* This function is a little complicated because of inheritance.

   Imagine a class hierarchy where B sits at the bottom, C is derived from
   B, and D is derived from C.  Each of these classes has its own fields as
   well: those things that appear between the braces when you write

     class B { ... }

   The sizeof function where this map is used expects to lookup a class name
   and get back a list of things to look at further.  These things may be
   normal fields, or more classes, which it will look up in turn.

   The problem is that you don't want to look up D, learn that it
   contains a B and C class, and then recursively look into the C,
   learn that it contains a B etc.  You would then get multiple
   unwarranted copies of ancestor classes.  Instead, when looking up a
   genuine class, its hierarchy's classes are presented back as the
   result of an intermediate calculation and the concatenation of the
   non-static data members for those classes can be returned

*)

val class_szmap_def = Define`
   class_szmap s =
      FUN_FMAP
         (\c. let subs = class_layout { so | (c,so) IN subobjs s }
                          (* get "subobjects", which includes the most
                             derived class name *)
              in
                      (* the end of the path in the subobj is the name of the
                         class, get its nsdmembers, map SND to strip out
                         the field names, and flatten the result *)
                 FLAT (MAP (\p. MAP SND (THE (nsdmembers s (LAST p)))) subs))
         (FDOM (deNONE s.classmap))
`

(* SANITY *)
val FDOM_class_szmap = store_thm(
  "FDOM_class_szmap",
  ``FDOM (class_szmap s) = FDOM (deNONE s.classmap)``,
  SRW_TAC [][class_szmap_def, finite_mapTheory.FUN_FMAP_DEF])
val _ = export_rewrites ["FDOM_class_szmap"]


val genoffset_def = Define`
  (genoffset [] acc szf alnf e = NONE) /\
  (genoffset (h::t) (acc:num) szf alnf e =
    let acc' = roundup (alnf h) acc
    in
      if h = e then SOME acc'
      else genoffset t (acc' + szf h) szf alnf e)
`
val _ = export_rewrites ["genoffset_def"]

(* given derived class name C, state s, and path to base sub-object p, return
   the offset of the latter within an object of type C *)
val subobj_offset_def = Define`
  subobj_offset s C p =
    let tyfm = class_szmap s
    in
      genoffset
        (class_layout { so | (C,so) IN subobjs s})
        0
        (\pth. if nsdmembers s (LAST pth) = SOME [] then 0
               else
                 @sz. sizeof tyfm (Class (LAST pth)) sz)
        (\pth. if nsdmembers s (LAST pth) = SOME [] then 0
               else @a. align tyfm (Class (LAST pth)) a)
        p
`


val nsds_bases_def = Define`
  nsds_bases s cnm =
    let layout = class_layout { so | (cnm, so) IN subobjs s } in
    let info p =
      let off = THE (subobj_offset s cnm p)
      in
          if p = [cnm] then
            let nsds = THE (nsdmembers s cnm)
            in
              MAP (\ (fld,ty).
                   (SOME fld, ty,
                    THE (genoffset nsds off
                              (\ (nm,ty). @sz. sizeof (class_szmap s) ty sz)
                              (\ (nm,ty). @a. align (class_szmap s) ty a)
                              (fld,ty))))
                  nsds
          else [(NONE, Class (LAST p), off)]
    in
      FLAT (MAP info layout)
`



(* BAD ASSUMPTION: no classes are abstract *)
(* type-checking requires a variety of pieces of information, which we derive
   from a state with this function *)
val expr_type_comps_def = Define`
  expr_type_comps s =
    <| class_fields :=
          FUN_FMAP (\c. THE (nsdmembers s c))
                   { c | ?v. c IN FDOM s.classmap /\
                             (s.classmap ' c = SOME v) };
       var_types := s.typemap ;
       abs_classes := {} |>
`;

(* sizeof calculations expect to find a map from class name to a list
   of types (the class's (non-static) fields.  This function calculates
   that map from a classmap *)
val sizeofmap_def = Define`
  sizeofmap s = class_szmap s
`;

val MEM_splits = prove(
  ``!l. MEM e l ==> ?pfx sfx. (l = pfx ++ (e :: sfx))``,
  Induct THEN SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`[]`, `l`] THEN SRW_TAC [][],
    RES_TAC THEN MAP_EVERY Q.EXISTS_TAC [`h::pfx`, `sfx`] THEN
    SRW_TAC [][]
  ]);

(* SANITY *)
val hasfld_imp_lfi = store_thm(
  "hasfld_imp_lfi",
  ``s |- C has least fld -: ftype via p' /\ object_type ftype ==>
    ?i. lookup_field_info (THE (nsdmembers s (LAST p'))) fld (i,ftype)``,
  SRW_TAC [][fieldty_via_def, FieldDecls_def, nsdmembers_def,
             finite_mapTheory.FLOOKUP_DEF] THEN
  Q.SPEC_THEN `deNONE s.classmap ' (LAST p')`
              STRIP_ASSUME_TAC
              statementsTheory.class_info_literal_nchotomy THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `centry` THEN
  FULL_SIMP_TAC (srw_ss()) [fieldtype_def, typesTheory.object_type_def,
                            okfield_def] THEN
  IMP_RES_TAC MEM_splits THEN
  SRW_TAC [][fieldname_def] THEN
  Q.HO_MATCH_ABBREV_TAC
    `?i. lookup_field_info (L1 ++ (X,Y) :: L2) X (i,Y)` THEN
  SRW_TAC [][staticsTheory.lookup_field_info_def] THEN
  Q.EXISTS_TAC `LENGTH L1` THEN
  SRW_TAC [ARITH_ss][rich_listTheory.EL_APPEND2])

val _ = export_theory();

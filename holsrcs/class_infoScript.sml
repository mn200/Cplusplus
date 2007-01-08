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
       sortingTheory rich_listTheory
in end

(* C++ ancestor theories  *)
open statesTheory aggregatesTheory

val _ = new_theory "class_info";

val cinfo_def = Define`
  cinfo s cnm : class_info = FST (THE (s.classmap ' cnm))
`;

(* set of a state's fully defined class *)
val defined_classes_def = Define`
  defined_classes s = FDOM (deNONE s.classmap)
`;

(* c2 is an ancestor of c1 *)
val ancestor_def = Define`
  ancestor s c1 c2 =
    c1 IN defined_classes s /\ ((cinfo s c1).ancestors = SOME c2)
`;


(* similarly, direct base classes, in order of declaration *)
val get_direct_bases_def = Define`
  get_direct_bases s cnm : CPPname list =
    case (cinfo s cnm).ancestors of
       NONE -> []
    || SOME n -> [n]
`

val get_virtual_bases_def = Define`
  get_virtual_bases s cnm : CPPname list = []
`;

(* given a type, class-path pair, if the path is non-empty, then the
   static type is Class of the last element in the path. *)
val static_type_def = Define`
  static_type (ty, pth) = if NULL pth then ty else Class (LAST pth)
`;

(* has any constructor, which seems to be the sense of what 8.5.1 p1 is
   saying *)
val has_user_constructor_def = Define`
  has_user_constructor s cnm =
    cnm IN defined_classes s /\
    ?ci userdefined.
       (s.classmap ' cnm = SOME (ci,userdefined)) /\
       (DefaultConstructor IN userdefined \/ CopyConstructor IN userdefined)
`;

(* 8.5.1 p1 : aggregate types *)
val is_aggregate_def = Define`
  (is_aggregate s (Class cnm) =
      ~has_user_constructor s cnm /\
      (get_direct_bases s cnm = []) /\
      (get_virtual_bases s cnm = []) /\
      !fldname fldty prot.
          MEM (FldDecl fldname fldty, F, prot) ((cinfo s cnm).fields) ==>
          (prot = Public)) /\
  (is_aggregate s _ = F)
`;

val strip_array_def = Define`
  (strip_array (Array bt n) = strip_array bt) /\
  (strip_array t = t)
`;

(* 9 p4  : POD types *)
val (PODstruct_rules, PODstruct_ind, PODstruct_cases) = Hol_reln`
  (!s cnm.
     cnm IN defined_classes s /\
     is_aggregate s (Class cnm) /\
     DISJOINT {Destructor; CopyAssignment}
              (SND (THE (s.classmap ' cnm))) /\
     (!fldname fldty prot.
         MEM (FldDecl fldname fldty, F, prot)
             ((cinfo s cnm).fields) ==>
         ~ref_type fldty /\
         (!cnm'. (strip_array fldty = Class cnm') ==>
                 PODstruct s cnm'))
  ==>
     PODstruct s cnm)
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
  (!C s. C IN defined_classes s ==> rsubobjs s (C, [C]))

    /\

  (!C Cs D s.
      s |- C < D /\ rsubobjs s (D, Cs)
   ==>
      rsubobjs s (C, C::Cs))
`;

val calc_rsubobjs = store_thm(
  "calc_rsubobjs",
  ``(C,Cs) IN rsubobjs s =
       (Cs = [C]) /\ C IN defined_classes s \/
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
                  LAST Cs IN defined_classes s /\
                  ?centry staticp prot.
                      MEM (centry,staticp,prot) (cinfo s (LAST Cs)).fields /\
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
    if c IN defined_classes s then
      SOME
        (mapPartial
           (\ce. case ce of
                    (CFnDefn ret nm args bod, stat, prot) -> NONE
                 || (FldDecl nm ty, stat, prot) -> if stat then NONE
                                                   else SOME (nm,ty)
                 || _ -> NONE)
           (cinfo s c).fields)
    else NONE
`

val o_ABS_L = store_thm(
  "o_ABS_L",
  ``(\x. f x) o g = (\x. f (g x))``,
  SRW_TAC [][combinTheory.o_DEF]);

open utilsTheory

(* ASSUMPTION:
     assume that virtual base classes must always appear last in the layout
     of a class
*)
val get_class_constituents0_def = new_specification(
  "get_class_constituents0_def",
  ["get_class_constituents0"],
  SIMP_RULE bool_ss [SKOLEM_THM]
    (prove(``!s cnm. ?l.
               PERM l (MAP (UNCURRY NSD) (THE (nsdmembers s cnm)) ++
                       MAP DBase (get_direct_bases s cnm) ++
                       MAP VirtualBase (get_virtual_bases s cnm)) /\
               (mapPartial (\cc. case cc of NSD n ty -> SOME (n,ty)
                                         || _ -> NONE) l =
                THE (nsdmembers s cnm)) /\
               (!i j vbnm. i < LENGTH l /\ j < LENGTH l /\ i < j /\
                           (EL i l = VirtualBase vbnm) ==>
                           ?vbnm'. EL j l = VirtualBase vbnm')``,
            REPEAT GEN_TAC THEN
            Q.HO_MATCH_ABBREV_TAC `?l. PERM l X /\ P l` THEN
            Q.EXISTS_TAC `X` THEN SRW_TAC [][] THEN
            Q.UNABBREV_ALL_TAC THEN
            SRW_TAC [][mapPartial_MAP, o_ABS_L, mapPartial_K_NONE] THENL [
              SRW_TAC [boolSimps.ETA_ss][pairTheory.UNCURRY,
                                         mapPartial_SOME],
              Q.HO_MATCH_ABBREV_TAC
                `?vbnm'. EL j (l1 ++ l2 ++ l3) = VirtualBase vbnm'` THEN
              Cases_on `i < LENGTH l1` THENL [
                Q.PAT_ASSUM `EL i X = Y` MP_TAC THEN
                FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                              [rich_listTheory.EL_APPEND1] THEN
                Q.UNABBREV_TAC `l1` THEN
                FULL_SIMP_TAC (srw_ss()) [rich_listTheory.EL_MAP] THEN
                Cases_on `EL i (THE (nsdmembers s cnm))` THEN
                SRW_TAC [][],
                ALL_TAC
              ] THEN
              `l1 ++ l2 ++ l3 = l1 ++ (l2 ++ l3)` by SRW_TAC [][] THEN
              FULL_SIMP_TAC (bool_ss ++ ARITH_ss)
                            [rich_listTheory.EL_APPEND2] THEN
              Q.ABBREV_TAC `i' = i - LENGTH l1` THEN
              Cases_on `i' < LENGTH l2` THENL [
                Q.PAT_ASSUM `EL i' X = Y` MP_TAC THEN
                FULL_SIMP_TAC (srw_ss()) [rich_listTheory.EL_APPEND1,
                                          Abbr`l2`, rich_listTheory.EL_MAP],
                ALL_TAC
              ] THEN
              `i' < j - LENGTH l1` by SRW_TAC [ARITH_ss][Abbr`i'`] THEN
              FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                            [rich_listTheory.EL_APPEND2, Abbr`l3`] THEN
              Q_TAC SUFF_TAC `j - (LENGTH l1 + LENGTH l2) <
                              LENGTH
                                (MAP VirtualBase (get_virtual_bases s cnm))`
                    THEN1 SRW_TAC [][rich_listTheory.EL_MAP] THEN
              Q.UNABBREV_ALL_TAC THEN
              FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)[]
            ])))

val get_class_constituents_def = Define`
  get_class_constituents s mdp cnm =
     FILTER (\cc. case cc of VirtualBase _ -> mdp || x -> T)
            (get_class_constituents0 s cnm)
`;

val sizeofmap_def = Define`
  sizeofmap s mdp =
     FUN_FMAP (get_class_constituents s mdp) (FDOM s.classmap)
`


(* calculates the offset of a virtual base within particular class, assuming
   it is most-derived *)
val virtual_offset_def = Define`
  virtual_offset s C1 C2 =
      let ccs = get_class_constituents s T C1 in
      let i = THE (LFINDi ((=) (VirtualBase C2)) ccs)
      in
        @off. offset (sizeofmap s) ccs i off
`

val base_offset_def = Define`
  base_offset s C1 C2 =
      let ccs = get_class_constituents0 s C1 in
      let i = THE (LFINDi ((=) (DBase C2)) ccs)
      in
        @off. offset (sizeofmap s) ccs i off
`;

val constituent_offsets_def = Define`
  constituent_offsets s mdp cnm =
    let ccs = get_class_constituents s mdp cnm in
    let nccs = NUMBER 0 ccs
    in
        MAP (\(n,c). (c, @off. offset (sizeofmap s) ccs n off)) nccs
`;

val init_order_offsets_def = Define`
  init_order_offsets s mdp cnm =
    let virts : CPPname list = if mdp then get_virtual_bases s cnm else [] in
    let dbases : CPPname list  = get_direct_bases s cnm in
    let nsds = THE (nsdmembers s cnm) in
    let all = MAP VirtualBase virts ++ MAP DBase dbases ++
              MAP (UNCURRY NSD) nsds in
    let all_layout_order = get_class_constituents s mdp cnm in
    let alli = MAP (\cc. (cc, THE (LFINDi ((=) cc) all_layout_order))) all
    in
        MAP (\(cc,i). (cc, @off. offset (sizeofmap s) all_layout_order i off))
            alli
`

(* given derived class name C, state s, and path to (not necessarily
   immediate) base sub-class p, return the offset of the latter
   within an object of type C *)
val subobj_offset_def = Define`
  (subobj_offset s (C1, [C2]) = if C1 = C2 then 0
                                else virtual_offset s C1 C2) /\
  (subobj_offset s (C1, (C2::C3::t)) =
               (* C1 must equal C2 *)
               base_offset s C1 C3 + subobj_offset s (C3, (C3::t)))
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
  SRW_TAC [][fieldty_via_def, FieldDecls_def, nsdmembers_def] THEN
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

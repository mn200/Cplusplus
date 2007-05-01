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

val is_class_name_def = Define`
  is_class_name st cppid = if is_abs_id cppid then
                             is_class_name_env st.genv cppid
                           else is_class_name_env st.env cppid
`;

val cinfo0_def = Define`
  cinfo0 s cnm = (item (THE (elookup_class (if is_abs_id cnm then s.genv
                                            else s.env)
                                           cnm))).info
`


val cinfo_def = Define`
  cinfo s cnm : class_info = FST (THE (cinfo0 s cnm))
`;

(* set of a state's fully defined class *)
val defined_classes_def = Define`
  defined_classes s = { id | is_class_name s id /\ ~(cinfo0 s id = NONE) }
`;

(* similarly, direct base classes, in order of declaration *)
val get_direct_bases_def = Define`
  get_direct_bases s cnm : class_spec list =
    mapPartial (\ (cnm, b, prot). if b then NONE else SOME cnm)
               (cinfo s cnm).ancestors
`

(* c2 is a direct base of c1 *)
val is_direct_base_def = Define`
  is_direct_base s c1 c2 =
    c1 IN defined_classes s /\ MEM c1 (get_direct_bases s c2)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,2),
                                  BeginFinalBlock(PP.CONSISTENT,0), TM,
                                  BreakSpace(1,0), TOK "<", BreakSpace(1,0)],
                   term_name = "is_direct_base",
                   fixity = Infix(NONASSOC, 460) }

val get_virtual_bases_def = Define`
  get_virtual_bases s cnm : class_spec list =
    mapPartial (\ (cnm, b, prot). if b then SOME cnm else NONE)
               (cinfo s cnm).ancestors
`;

(* c2 is a virtual base of c1 *)
val is_virtual_base_def = Define`
  is_virtual_base s c1 c2 =
    c1 IN defined_classes s /\ MEM c1 (get_virtual_bases s c2)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,2),
                                  BeginFinalBlock(PP.CONSISTENT,0), TM,
                                  BreakSpace(1,0), TOK "<.", BreakSpace(1,0)],
                   term_name = "is_virtual_base",
                   fixity = Infix(NONASSOC, 460) }

val RTC_class_lt_def = Define`
  RTC_class_lt s c1 c2 = RTC (is_direct_base s RUNION is_virtual_base s) c1 c2
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,2),
                                  BeginFinalBlock(PP.CONSISTENT,0), TM,
                                  BreakSpace(1,0), TOK "<=", BreakSpace(1,0)],
                   term_name = "RTC_class_lt",
                   fixity = Infix(NONASSOC, 460) }

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
       (cinfo0 s cnm = SOME (ci,userdefined)) /\
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

(* 9 p4  : POD types *)
val (PODstruct_rules, PODstruct_ind, PODstruct_cases) = Hol_reln`
  (!s cnm.
     cnm IN defined_classes s /\
     is_aggregate s (Class cnm) /\
     DISJOINT {Destructor; CopyAssignment}
              (SND (THE (cinfo0 s cnm))) /\
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

(* The Subobjs relation of Wasserab et al. *)
val (subobjs_rules, subobjs_ind, subobjs_cases) = Hol_reln`
   (!C Cs s.
     rsubobjs s (C,Cs)
   ==>
     subobjs s (C,Cs))

   /\

  (!s C C' D Cs.
     s |- C <= C' /\ s |- C' <. D /\ (D,Cs) IN rsubobjs s
   ==>
     subobjs s (C, Cs))
`;

(* from s3.4 of Wasserab et al *)
val (pord1_rules, pord1_ind, pord1_cases) = Hol_reln`
   (!C Cs Ds s.
     (C,Cs) IN subobjs s /\ (C,Ds) IN subobjs s /\ (Cs = FRONT Ds)
   ==>
     pord1 (s,C) Cs Ds)

   /\

   (!C Cs D s.
     (C,Cs) IN subobjs s /\ s |- LAST Cs <. D
   ==>
     pord1 (s, C) Cs [D])
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
val SFld_to_ID_def = Define`
  (SFld_to_ID (SFTempCall s args) = IDTempCall (TemplateConstant (F,[],s))
                                               args) /\
  (SFld_to_ID (SFName s) = Base s)
`;

val fieldname_def = Define`
  (fieldname (FldDecl fldnm ty) = SFName fldnm) /\
  (fieldname (CFnDefn retty n args body) = n)
`

(* again, omitting constructors and destructors as these can't be called *)
val fieldtype_def = Define`
  (fieldtype (FldDecl fld ty) = ty) /\
  (fieldtype (CFnDefn retty n args body) = Function retty (MAP SND args))
`;

(* those fields for which the above two predicates are well-defined *)
val okfield_def = Define`
  (okfield (FldDecl fld ty) = T) /\
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

val MethodDefs_def = Define`
  MethodDefs s cnm mthnm =
    { (Cs,(rettype,ps,body)) |
         (cnm,Cs) IN subobjs s /\
         ?prot statp.  MEM (CFnDefn rettype mthnm ps body, statp, prot)
                           (cinfo s (LAST Cs)).fields }
`

(* s |- C has least method -: ty via Cs *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix (NONASSOC, 460),
                  pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,0),
                                 TM, BreakSpace(1,0),
                                 TOK "has", BreakSpace(1,0),
                                 TOK "least", BreakSpace(1,0),
                                 TOK "method", BreakSpace(1,0),
                                 PPBlock([TM, BreakSpace(1,0),
                                          TOK "-:", BreakSpace(1,0), TM],
                                         (PP.CONSISTENT, 0)),
                                 BreakSpace(1,0), TOK "via", BreakSpace(1,0)],
                  term_name = "methodty_via"}
val methodty_via_def = Define`
  s |- C has least method mname -: minfo via Cs =
         (Cs,minfo) IN MethodDefs s C mname /\
         !Cs' ty'. (Cs',ty') IN MethodDefs s C mname ==>
                   RTC (pord1 (s,C)) Cs Cs'
`

(* see 6.3.6 Wasserab et al. *)
val MinimalMethodDefs_def = Define`
  MinimalMethodDefs s cnm mthdnm =
    {(Cs,minfo) | (Cs,minfo) IN MethodDefs s cnm mthdnm /\
                  !Cs' minfo'. (Cs',minfo') IN MethodDefs s cnm mthdnm ==>
                               RTC (pord1 (s,cnm)) Cs' Cs ==> (Cs = Cs') }
`

(* mdc = "most derived class"; ldc = "least derived class"  *)
val mdc_def = Define`mdc (C,Cs) = C`;
val ldc_def = Define`ldc (C,Cs) = LAST Cs`;

val OverriderMethodDefs_def = Define`
  OverriderMethodDefs s R mthdname =
    {(Cs, minfo) | ?Cs' minfo'.
                      s |- ldc R has least method mthdname -: minfo' via Cs' /\
                      (Cs,minfo) IN MinimalMethodDefs s (mdc R) mthdname /\
                      RTC (pord1 (s,mdc R)) Cs (SND R ^ Cs') }
`;

(* s |- (C,Cs) has overrider mname -: minfo via Cs *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix (NONASSOC, 460),
                  pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,0),
                                 TM, BreakSpace(1,0),
                                 TOK "has", BreakSpace(1,0),
                                 TOK "overrider", BreakSpace(1,0),
                                 PPBlock([TM, BreakSpace(1,0),
                                          TOK "-:", BreakSpace(1,0), TM],
                                         (PP.CONSISTENT, 0)),
                                 BreakSpace(1,0), TOK "via", BreakSpace(1,0)],
                  term_name = "has_overrider_via"}
val has_overrider_via_def = Define`
  s |- R has overrider mname -: minfo via Cs =
         (OverriderMethodDefs s R mname = {(Cs,minfo)})
`

(* select unique method: s |- (C,Cs) selects M -: minfo via Cs' *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix (NONASSOC, 460),
                  pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,0),
                                 TM, BreakSpace(1,0),
                                 TOK "selects", BreakSpace(1,0),
                                 PPBlock([TM, BreakSpace(1,0),
                                          TOK "-:", BreakSpace(1,0), TM],
                                         (PP.CONSISTENT, 0)),
                                 BreakSpace(1,0), TOK "via", BreakSpace(1,0)],
                  term_name = "selects_via"}
val (selects_via_rules,selects_via_ind,selects_via_cases) = Hol_reln`
   (!s C mname minfo Cs Cs'.
     s |- C has least method mname -: minfo via Cs'
   ==>
     s |- (C,Cs) selects mname -: minfo via Cs')

   /\

   (!s mname minfo C Cs Cs'.
     (!minfo Cs'. ~ (s |- C has least method mname -: minfo via Cs')) /\
     s |- (C,Cs) has overrider mname -: minfo via Cs'
   ==>
     s |- (C,Cs) selects mname -: minfo via Cs')
`

(* s |- static_ty casts dynamic_value0 to dynamic_value1 *)
(*    the static_ty is the desired static type *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix (NONASSOC, 460),
                  pp_elements = [BreakSpace(1,0),
                                 TOK "|-", BreakSpace(1,0),
                                 TM, BreakSpace(1,0),
                                 TOK "casts", BreakSpace(1,0),
                                 TM, BreakSpace(1,0),
                                 TOK "into", BreakSpace(1,0)],
                  term_name = "casts_to"}
(* this is a merge of Wasserab et al's casts to (6.3.3) and the <= subtyping
   relation.  The former does not check for unique paths. *)
val casts_to_def = Define`
  s |- C casts Cs into Ds =
       ?!Cs'. (LAST Cs,Cs') IN subobjs s /\ (LAST Cs' = C) /\
              (Ds = Cs ^ Cs')
`;


(* nsdmembers (non-static data-members) *)
val nsdmembers_def = Define`
  nsdmembers s c =
    if c IN defined_classes s then
      SOME
        (mapPartial
           (\ce. case ce of
                    (CFnDefn ret nm args bod, stat, prot) -> NONE
                 || (FldDecl fld ty, stat, prot) -> if stat then NONE
                                                    else SOME (fld,ty)
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
     FUN_FMAP (get_class_constituents s mdp) (is_class_name s)
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

(* given a class name, and a mdp status, returns the list of direct components
   along with their offsets, presented in the order in which they have to be
   initialised - virtual bases (if any), direct bases, followed by
   non-static data-members *)
val init_order_offsets_def = Define`
  init_order_offsets s mdp cnm =
    let virts = if mdp then get_virtual_bases s cnm else [] in
    let dbases  = get_direct_bases s cnm in
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

(* the fields belonging to this class specifically *)
val get_fields_def = Define`
  get_fields ci =
          mapPartial
            (\ (ce, b, p).
               case ce of
                  CFnDefn retty nm params body ->
                     SOME (nm, Function retty (MAP SND params))
               || FldDecl fld ty -> SOME (SFName fld, ty)
               || _ -> NONE)
            (FST ci).fields
`;

val field_type_def = Define`
  field_type ci sfld =
    OPTION_MAP SND (FINDL (\ (nm, ty). nm = sfld) (get_fields ci))
`;


(* looks up an identifier corresponding to an object, and returns its type *)
val elookup_type_def = Define`
  (elookup_type env (IDFld id fld) =
     case elookup_class env id of
        NONE -> NONE
     || SOME cenv -> (case (item cenv).info of
                         NONE -> NONE
                      || SOME ci -> field_type ci fld)) /\
  (elookup_type env (IDConstant (b, [], n)) =
     FLOOKUP ((item env).typemap) (SFName n)) /\
  (elookup_type env (IDConstant (b, h :: t, n)) =
     case FLOOKUP (map env) h of
        NONE -> NONE
     || SOME e' -> elookup_type e' (IDConstant (b, t, n))) /\
  (elookup_type env (IDTempCall (TemplateConstant (b, [], n)) targs) =
     FLOOKUP ((item env).typemap) (SFTempCall n targs)) /\
  (elookup_type env (IDTempCall (TemplateConstant (b, h :: t, n)) targs) =
     case FLOOKUP (map env) h of
        NONE -> NONE
     || SOME e' -> elookup_type e' (IDTempCall
                                    (TemplateConstant(b, t, n))
                                    targs))
`;

(* looks up an object identifier and returns its address *)
val elookup_addr_def = Define`
  (* must be a SFName, a template id could only be to a function, which is
     not an object *)
  (elookup_addr env (IDFld id (SFName fld)) =
     case elookup_class env id of
        NONE -> NONE
     || SOME cenv -> FLOOKUP (item cenv).statvars fld) /\
  (elookup_addr env (IDConstant (b, [], n)) = FLOOKUP (item env).varmap n) /\
  (elookup_addr env (IDConstant (b, h::t, n)) =
     case FLOOKUP (map env) h of
        NONE -> NONE
     || SOME e' -> elookup_addr e' (IDConstant(b, t, n))) /\
  (elookup_addr env _ = NONE)
`;

(* state-based, as opposed to environment-based, lookup functions *)
val lift_lookup_def = Define`
  lift_lookup f s id = if is_abs_id id then f s.genv id
                       else f s.env id
`;

val lookup_addr_def = Define` lookup_addr =  lift_lookup elookup_addr `;
val lookup_type_def = Define` lookup_type =  lift_lookup elookup_type `;
val lookup_class_def = Define`lookup_class = lift_lookup elookup_class `;

(* looks up a fully-qualified non-static data member field (e.g., C::fld) and
   finds its offset within that class.

*)
val lookup_offset_def = Define`
  (lookup_offset s mdp (IDFld id (SFName fld)) =
     let coffs = constituent_offsets s mdp id
     in
       case FINDL (\ (cc, off). ?ty. cc = NSD fld ty) coffs of
          NONE -> NONE
       || SOME (cc, off) -> SOME off) /\
  (lookup_offset s mdp _ = NONE)
`;


(* looks up a fully-qualified field (e.g., C::fld) and finds its type *)
val lookup_field_type_def = Define`
  (lookup_field_type s (IDFld id sfld) =
    case lookup_class s id of
       NONE -> NONE
    || SOME cenv -> (case (item cenv).info of
                        NONE -> NONE
                     || SOME ce -> field_type ce sfld)) /\
  (lookup_field_type s _ = NONE)
`;

val _ = export_theory();

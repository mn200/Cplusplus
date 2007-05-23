(* Resolution of names within a sequence of external declarations *)

(* (Can be viewed as a phase of compilation) *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps


(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open typesTheory memoryTheory expressionsTheory staticsTheory class_infoTheory
open aggregatesTheory declaration_dynamicsTheory
local
  open side_effectsTheory statesTheory operatorsTheory overloadingTheory
       instantiationTheory
in end

val _ = new_theory "name_resolution";

val _ = Hol_datatype`
  P1_action = P1Decl of ext_decl
            | EnterNS of string
            | ExitNS of string
`;

(* the "others" field stores 'objects' (functions and variables), as well
   as namespace names *)
val _ = Hol_datatype`
  P1state = <| current_nspath : string list ;
               dynclasses : string |-> (TemplateArg list # CPP_ID) ;
               dynothers : string |-> (TemplateArg list # CPP_ID) ;
               global : state ;
               accdecls : ext_decl list |>
`;

val breakup_fmap_def = Define`
  breakup_fmap f fm =
    FUN_FMAP (\x. SND (f x))


val break_sfld_def = Define`
  (break_sfld abs sfs (SFName s) = ([], IDConstant abs sfs (SFName s))) /\
  (break_sfld abs sfs (SFTempCall s targs) =
     (targs, IDConstant abs sfs (SFName s)))
`;

val sfldmap_strings_def = Define`
  sfldmap_strings sfm = IMAGE (\sf. case sf of SFName s -> s
                                            || SFTempCall s _ -> s)
                              (FDOM sfm)
`;

(* ----------------------------------------------------------------------
    empty_p1 : state -> P1state

    the "empty" p1-state that has empty dynamic maps for classes and
    others, but which embodies a particular state.
   ---------------------------------------------------------------------- *)

val empty_p1_def = Define`
  empty_p1 s = <| current_nspath := [] ;
                dynclasses := FEMPTY ;
                dynothers := FEMPTY ;
                global := s ;
                accdecls := [] |>
`;


(* ----------------------------------------------------------------------
    open_ftnode : string list -> P1state -> P1state

    given a P1state (containing dynamic maps for "others" and classes,
    and global environment values (stored in a state, and the gtemps
    field) override the dynamics maps with entries from the global
    environment, according to the provided path, which is of
    namespaces

   ---------------------------------------------------------------------- *)
val open_ftnode_def = Define`
  open_ftnode pth s =
    let env_at_pth = THE (apply_path pth s.global.genv) in
    let sfpth = MAP SFName pth
    in
      s with <| dynclasses :=
                  FUNION (FUN_FMAP (break_sfld abs sfpth)
                                   (sfldmap_strings
                                      (item env_at_pth).classenv))
                         s.dynclasses;
                dynothers := FUNION (FUN_FMAP
                                       (break_sfld abs sfpth)
                                       (FDOM (item env_at_pth).typemap UNION
                                        IMAGE SFName (FDOM (map env_at_pth))))
                                    s.dynothers |>
`;

(* ----------------------------------------------------------------------
    open_classnode : CPP_ID -> P1state -> P1state

    given a class name (i.e., of type :CPP_ID), and a P1state
    (including maps for "others" and "classes"), update the maps to
    reflect the information in the class.  This is moderately
    complicated because ancestor classes have to have their names
    added too.  If multiple ancestors at the same level try to add the
    same name this is a statically detectable ambiguity.

    We also need a state about so that we can look up information for
    the ancestor classes.  (Imagine you have class C : public ::D {
    ... }, names in C's environment might actually be references to
    stuff in ::D.)
   ---------------------------------------------------------------------- *)

val open_classnode_def = Define`
  open_classnode cnm p1s =
    let s = p1s.global in
    let objflds =
           { (sf,fpth) | ?tyst. s |- cnm has least sf -: tyst via fpth } in
    let objmap = FUN_FMAP (\sf. mk_member (LAST (objflds ' sf)) sf)
                          (IMAGE FST objflds) in
    let funflds =
           { (sf,fpthopt) |
                (?ret stat ps bod fpth. (* non-virtual case *)
                     s |- cnm has least method sf -: (ret,stat,ps,bod)
                            via fpth /\
                     ~is_virtual s cnm sf ret (MAP SND ps) /\
                     (fpthopt = SOME fpth)) \/
                (?ret stat ps bod pth.
                     s |- cnm has least method sf -: (ret,stat,ps,bod)
                            via pth /\
                     is_virtual s cnm sf ret (MAP SND ps) /\
                     (fpthopt = NONE)) } in
    let funmap = FUN_FMAP (\sf. case funflds ' sf of
                                    NONE -> IDConstant F [] sf
                                 || SOME pths -> mk_member (LAST pths) sf)
                           (IMAGE FST funflds)
    in
       p1s with <| dynothers := FUNION objmap (FUNION funmap p1s.dynothers) |>
`;

val open_classpath_def = Define`
  open_classpath p1s sofar sfs =
    case sfs of
       [] -> p1s
    || sf :: rest -> open_classpath (open_classnode (mk_member sofar sf) p1s)
                                    (mk_member sofar sf)
                                    rest
`;


(* ----------------------------------------------------------------------
    open_path : bool -> StaticField list -> P1state -> P1state

    The boolean records whether we're opening from the global root (::).
    If it's false, then we'll be looking at a local variables and classes

    The input P1state is assumed to be "dynamically open" at the level
    of its current_nspath.

   ---------------------------------------------------------------------- *)

val open_path_def = Define`
  open_path absp todo ps =
    let s = ps.global in
    let env0 = if absp then s.genv else s.env in
    let env = THE (apply_path ps.current_nspath env0)
    in
      case todo of
         [] -> ps
      || h::t -> if h IN FDOM (item env).classenv then
                   let root = IDConstant absp (MAP SFName ps.current_nspath) h
                   in
                     open_classpath (open_classnode root ps) root t
                 else
                   let pth = ps.current_nspath ++ [dest_sfname h] in
                   let ps' = open_ftnode pth ps in
                   let ps'' = ps' with current_nspath := pth
                   in
                     open_path absp t ps''
`;

val EnterNSpace_def = Define`
  EnterNSpace n s = open_path T [SFName n] s
`

val ExitNSpace_def = Define`
  ExitNSpace s =
    open_path T (FRONT (MAP SFName s.current_nspath)) (empty_p1 s.global)
`;

val rewrite_types_def = Define`
  rewrites_types ps ty =
    let inst =
         <| typemap := (\s. if SFName s IN FDOM ps.dynclasses then
                              TypeID (ps.dynclasses ' SFName s)
                            else TypeID (SFName s)) ;
            valmap := TVAVar ;
            tempmap := (\s. if ?targs. SFTempCall s targs IN
                                       FDOM ps.dynclasses
                            then
                              @(b,sfs,sf).
                              IDConstant b sfs sf = ps.dynclasses '




val (phase1_rules, phase1_ind, phase1_cases) = Hol_reln`
  (* RULE-ID: [phase1-namepace] *)
  (!n ds pas s.
     T
   ==>
     phase1 (P1Decl (NameSpace n ds) :: pas, s)
            (EnterNS n :: (MAP P1Decl ds ++ (ExitNS n :: pas)), s))

      /\

  (* RULE-ID: [phase1-enter-namespace] *)
  (!n ds s.
     T
   ==>
     phase1 (EnterNS n :: ds, s) (ds, EnterNSpace n s))

     /\

  (* RULE-ID: [phase1-exit-namespace] *)
  (!n ds s t.
     (s.current_nspath = n :: t)
   ==>
     phase1 (ExitNS n :: ds, s) (ds, ExitNSpace s))

   /\

  (* RULE-ID: [phase1-decl-vdec] *)
  (* note there is effectively no circumstance in which a simple variable
     declaration can be of a structured name.   One can redeclare functions
     with structured names, but this achieves absolutely nothing. *)
  (
     T
   ==>
     phase1 (Decl (VDec ty (SFName s)), s)

`;



val lift_vdec_def = Define`
  lift_vdec n (VDec

val flatten_nspaces_def = Define`
  (flatten_nspaces [] = []) /\
  (flatten_nspaces (NameSpace n ds :: t) =
     MAP (


val _ = Hol_datatype`
  nameres_ctxt = <|
    objs : string -> CPP_ID # CPP_Type ;
    classes : string -> CPP_ID ;
    nspaces : string -> string list ;
  |>
`;


val _ = Hol_datatype`
  nametypes = NSname | Classname | Unknown
`

val tn_outermost_def = Define`
  (tn_outermost (b, [], s) = (b, s, Unknown)) /\
  (tn_outermost (b, h::t, s) = (b, h, NSname))
`;

val tid_outermost_def = Define`
  (tid_outermost (TemplateConstant tn) = tn_outermost tn)
`

val get_outerid_def = Define`
  (get_outerid (IDFld id sf) =
     case get_outerid id of
        (b, s, Unknown) -> (b,s,Classname)
     || x -> x) /\
  (get_outerid (IDTempCall tid targs) = tid_outermost tid) /\
  (get_outerid (IDConstant tn) = tn_outermost tn)
`;

val tid_prepend_def = Define`
  tid_prepend nslist clist (TemplateConstant (b, ns, s)) =
    if ns = [] then
      if clist = [] then
        IDConstant(T, nslist, s)
      else

val id_prepend_def = Define`
  (id_prepend nslist clist (IDFld id sf) =
     IDFld (id_prepend nslist clist id) sf) /\
  (id_prepend nslist clist (IDConstant (b, ns, s)) =
     if ns = [] then
       if clist = [] then
         IDConstant(T, nslist, s)
       else
         FOLDL IDFld (IDConstant(T,nslist, HD clist)) (TL clist ++ [s])
     else
       IDConstant (T, nslist ++ ns, s)) /\
  (id_prepend nslist clist (IDVar s) = IDVar s) /\
  (id_prepend nslist clist (IDTempCall tid targs) =
     IDTempCall (tid_prepend nslist clist tid) targs)
`;

val translate_tid_def = Define`
  (translate_tid ctxt (TemplateConstant tn) =
     case tn_outermost tn of
        (T, h, ty) -> TemplateConstant tn
     || (F, h, NSname) -> TemplateConstant (T, ctxt.nspaces h

val translate_id_def = Define`
  (translate_id ctxt classp (IDVar s) = IDVar s) /\
  (translate_id ctxt classp (IDFld id sfld) =
     IDFld (translate_id ctxt T id) sfld) /\
  (translate_id ctxt (IDTempCall tid targs) =
     IDTempCall (translate_tid ctxt tid)





val _ = set_trace "inddef strict" 1


(* non-function field resolution rule
(* Note how the path p is used:
     - to figure out the static type of the l-value (LAST p)
     - to derive the path from the most-derived class to the sub-object
       enclosing the field.  The offset is calculated with respect to
       this because the sub-object could be anywhere, and might be virtual.


       subobject of the original LVal is ignored.  This is because
   only functions can get a "virtual" treatment.
   This doesn't mean that a field reference can't be to an ancestor's field.

*)
(!s cnm fld ftype Cflds se offn i a p p'.
     s |- LAST p has least fld -: ftype via p' /\
     (Cflds = THE (nsdmembers s (LAST p'))) /\
     object_type ftype /\
     lookup_field_info (MAP (\ (n,ty). (SFName n, ty)) Cflds) fld (i,ftype) /\
     offset (sizeofmap s) (MAP (UNCURRY NSD) Cflds) i offn
   ==>
     ^mng (mExpr (SVar (LVal a (Class cnm) p) fld) se) s
          (s, ev (LVal (a + subobj_offset s (cnm, p ^ p') + offn) ftype
                       (default_path ftype)) se))
*)


(* ----------------------------------------------------------------------
    how to evaluate a sequence of external declarations
   ---------------------------------------------------------------------- *)

(* split a name into a class::fld part *)
val class_fld_split_def = Define`
  class_fld_split (IDFld id fld) = (id, fld)
`;


(* if the evaluation can't get the list of external declarations to the
   empty list, this is (implicitly) an occurrence of undefined behaviour *)
val (emeaning_rules, emeaning_ind, emeaning_cases) = Hol_reln`

(* RULE-ID: global-fndefn *)
(!s0 s fval name rettype params body ftype edecls.
     installfn s0 Ptr rettype name params body fval s /\
     ~(name IN FDOM s.typemap) /\ ~is_class_name s0 name /\
     (ftype = Function rettype (MAP SND params))
   ==>
     emeaning
       (FnDefn rettype name params body :: edecls) s
       (s with <| typemap updated_by (\tm. tm |+ (name, ftype)) |>,
        edecls))

   /\

(* RULE-ID: member-fndefn *)
(* The first MEM clause looks up the assumed declaration, and gets
   static-ness and protection information there.
   The second MEM clauses checks that this is not a duplicate definition
     (this is a static check, one that would be performed by the compiler
      if the duplication occurred within a single translation unit, or by
      the linker if it occurred across multiple units)
*)
(!rettype userdefs name params body edecls s0 s cinfo staticp prot cpart base.
     is_class_name s0 name /\
     ((cpart, base) = class_fld_split name) /\
     (SOME (cinfo, userdefs) = s0.classmap ' cpart) /\
     (?pms'.
         MEM (CFnDefn rettype base pms' NONE, staticp, prot)
             cinfo.fields /\
         (MAP SND pms' = MAP SND params)) /\
     (!bdy' rettype' statp prot pms'.
         MEM (CFnDefn rettype' base pms' bdy', statp, prot) cinfo.fields
           ==>
         ~(MAP SND pms' = MAP SND params)) /\
     install_member_functions cpart s0
                              [(CFnDefn rettype base params (SOME body),
                                staticp, prot)]
                              s
   ==>
     emeaning (FnDefn rettype name params body :: edecls) s0
              (s, edecls))

   /\

(* RULE-ID: global-declmng *)
(!s0 s d0 ds edecls.
     declmng meaning copy2globals (d0, s0) (ds, s)
   ==>
     emeaning (Decl d0 :: edecls) s0 (s, MAP Decl ds ++ edecls))

   /\

(* RULE-ID: global-class-declaration *)
(*   one might argue that this is a useless rule to have dynamically, as
     class declarations are only made for the benefit of static type-checking
*)
(!name edecls s0.
     T
   ==>
     emeaning
        (Decl (VStrDec name NONE) :: edecls) s0
        (copy2globals
           (s0 with classmap updated_by (\sm. sm |+ (name, NONE))),
         edecls))

   /\

(* RULE-ID: global-class-definition *)
(!s0 s name info0 userdefs info edecls.
     ((info,userdefs) = define_default_specials info0) /\
     install_member_functions name s0 info.fields s
   ==>
     emeaning (Decl (VStrDec name (SOME info0)) :: edecls) s0
              (copy2globals
                  (s with <| classmap updated_by
                                      (\sm. sm |+ (name,
                                                   SOME (info, userdefs))) |>),
               edecls))
`;




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

val _ = Hol_datatype`
  dynobj_type = dStatMember | dMember | dVirtualMember | dNormalObj
`;

(* given an environment, and an id, determine if the id is a reference to
   a member object *)
val eid_is_member_def = Define`
  eid_is_member (env : environment) id =
    case id of
       IDConstant b [] sf -> F
    || IDConstant b (SFTempCall s targs :: sfs) sf -> T
    || IDConstant b (SFName s :: sfs) sf ->
         if SFName s IN FDOM (item env).classenv then T
         else eid_is_member (map env ' s) (IDConstant b sfs sf)
`
val _ = export_rewrites ["eid_is_member_def"]

(* when looking up a member, ignores ancestors - also ignores possibility
   that a member might be virtual *)
val id_objtype_def = Define`
  id_objtype (s : state) id =
    case id of
       IDConstant b [] sf -> dNormalObj
    || IDConstant b (h::t) sf ->
         let classid = IDConstant b (FRONT (h::t)) (LAST (h::t))
         in
           if is_class_name s classid then
             let ci = cinfo s classid in
             let (ce,b,p) = THE (FINDL (\ (ce,b,p). fieldname ce = sf)
                                       ci.fields)
             in
               if b then dStatMember else dMember
           else dNormalObj
`;



(* the "others" field stores 'objects' (functions and variables), as well
   as namespace names *)
val _ = Hol_datatype`
  P1state = <|
    current_nspath : string list ;
    dynclasses : string |-> bool # StaticField list # TemplateArg list ;
    dynobjs : string |-> bool # StaticField list # TemplateArg list #
                         dynobj_type ;
    dynns : string |-> bool # string list ;
    global : state ;
    accdecls : ext_decl list |>
`;

val resolve_classid_def = Define`
  (resolve_classid avds ps (IDConstant T sfs sf) = IDConstant T sfs sf) /\
  (resolve_classid avds ps (IDConstant F [] (SFName s)) =
     let (b,sfs,targs) = ps.dynclasses ' s
     in
       IDConstant b sfs (SFName s)) /\
  (resolve_classid avds ps (IDConstant F [] (SFTempCall s targs)) =
     let (b,sfs,targs') = ps.dynclasses ' s
     in
       IDConstant b sfs (SFTempCall s targs)) /\
  (resolve_classid avds ps (IDConstant F (SFName s :: sfs) sf) =
     if s IN FDOM ps.dynclasses then
       let (b,pre_sfs,targs) = ps.dynclasses ' s
       in
         IDConstant b (pre_sfs ++ SFName s :: sfs) sf
     else
       let (b,sfnms) = ps.dynns ' s
       in
         IDConstant b (MAP SFName sfnms ++ SFName s :: sfs) sf) /\
  (resolve_classid avds ps (IDConstant F (SFTempCall s targs :: sfs) sf) =
     let (b,pre_sfs,targs') = ps.dynclasses ' s
     in
       IDConstant b (pre_sfs ++ SFTempCall s targs :: sfs) sf)
`;

val break_sfld_def = Define`
  (break_sfld (SFName s) = ([], s)) /\
  (break_sfld (SFTempCall s targs) = (targs, s))
`;
val _ = export_rewrites ["break_sfld_def"]

val dest_id_def = Define`
  dest_id (IDConstant b sfs sf) = (b,sfs,sf)
`

(* ----------------------------------------------------------------------
    empty_p1 : ext_decl list -> state -> P1state

    the "empty" p1-state that has empty dynamic maps for classes and
    others, but which embodies a particular state and accumulated
    declarations
   ---------------------------------------------------------------------- *)

val empty_p1_def = Define`
  empty_p1 ds s = <| current_nspath := [] ;
                     dynclasses := FEMPTY ;
                     dynobjs := FEMPTY ;
                     dynns := FEMPTY ;
                     global := s ;
                     accdecls := ds |>
`;


(* ----------------------------------------------------------------------
    open_ftnode : string list -> P1state -> P1state

    given a P1state (containing dynamic maps for objects, classes and
    namespaces, and global environment values (stored in a state, and
    the gtemps field)) override the dynamics maps with entries from the
    global environment, according to the provided path, which is of
    namespaces.

    If the globals doesn't have a namespace entry for that path, then
    make it.

   ---------------------------------------------------------------------- *)
val open_ftnode_def = Define`
  open_ftnode pth s =
    let (env_at_pth,genv') =
        case apply_path pth s.global.genv of
           NONE -> (empty_env,
                    THE (fupd_at_path
                           (FRONT pth)
                           (\ft.
                             SOME (FTNode
                                     (item ft)
                                     (map ft |+ (LAST pth, empty_env))))
                           s.global.genv))
        || SOME ft -> (ft, s.global.genv)
    in
    let sfpth = MAP SFName pth in
    let cenv = (item env_at_pth).classenv in
    let tyenv = (item env_at_pth).typemap
    in
      s with <| dynclasses :=
                  FUNION
                    (FUN_FMAP (\s. @p.
                                     ?sfld targs.
                                        sfld IN FDOM cenv /\
                                        (break_sfld sfld = (targs, s)) /\
                                        (p = (T,sfpth,targs)))
                              (IMAGE sfld_string (FDOM cenv)))
                    s.dynclasses;
                dynobjs :=
                  FUNION
                    (FUN_FMAP (\s. @p.
                                     ?sfld targs.
                                       sfld IN FDOM tyenv /\
                                       (break_sfld sfld = (targs, s)) /\
                                       (p = (T, sfpth, targs, dNormalObj)))
                              (IMAGE sfld_string (FDOM tyenv)))
                    s.dynobjs;
                dynns :=
                  FUNION (FUN_FMAP (\s. (T, pth)) (FDOM (map env_at_pth)))
                         s.dynns ;
                global := s.global with genv := genv'
             |>
`;

(* ----------------------------------------------------------------------
    open_classnode : CPP_ID -> P1state -> P1state

    given a class name (i.e., of type :CPP_ID), and a P1state
    (including maps for "others" and "classes"), update the maps to
    reflect the information in the class.  This is moderately
    complicated because ancestor classes have to have their names
    added too.  If multiple ancestors at the same level try to add the
    same name this is a statically detectable ambiguity.

    We also need the state about (p1s.global) so that we can look up
    information for the ancestor classes.  (Imagine you have class C :
    public ::D { ... }, names in C's environment might actually be
    references to stuff in ::D.)

    This function is called when we're looking at some expression or
    function body which is supposed to be in the scope of the given
    class name.

   ---------------------------------------------------------------------- *)

val open_classnode_def = Define`
  open_classnode avoids cnm p1s =
    let s = p1s.global in
    let objflds =
         { (str,res) |
              ?sf tyst targs fpth absp sfs fpthsf.
                  (s,avoids) |- cnm has least sf -: tyst via fpth /\
                  (break_sfld sf = (targs, str)) /\
                  (dest_id (LAST fpth) = (absp,sfs,fpthsf)) /\
                  (res = (absp, sfs ++ [fpthsf], targs,
                          if SND tyst then dStatMember else dMember)) }
    in
    let objmap = FUN_FMAP (\s. objflds ' s) (IMAGE FST objflds) in
    let funflds =
           { (str,res) |
                (?ret stat ps bod fpth targs sf sfs absp fpthsf.
                     (* non-virtual case *)
                     (s,avoids) |- cnm has least method sf -: (ret,stat,ps,bod)
                            via fpth /\
                     (break_sfld sf = (targs, str)) /\
                     ~is_virtual s cnm sf ret (MAP SND ps) /\
                     (dest_id (LAST fpth) = (absp,sfs,fpthsf)) /\
                     (res = (absp,sfs ++ [fpthsf],targs,
                             if stat then dStatMember else dMember))) \/
                (?ret ps bod pth sf.
                     (s,avoids) |- cnm has least method sf -: (ret,F,ps,bod)
                            via pth /\
                     is_virtual s cnm sf ret (MAP SND ps) /\
                     (break_sfld sf = ([], str)) /\
                     (res = (F, [], [], dVirtualMember))) } in
    let funmap = FUN_FMAP (\s. funflds ' s) (IMAGE FST funflds) in
    let nclasses = { (str,res) |
                       ?sf fpth absp sfs fpthsf targs.
                          (s,avoids) |- cnm has least injected sf via fpth /\
                          (break_sfld sf = (targs, str)) /\
                          (dest_id (LAST fpth) = (absp, sfs, fpthsf)) /\
                          (res = if SND (break_sfld fpthsf) = str then
                                   (absp, sfs, targs)
                                 else
                                   (absp, sfs ++ [fpthsf], targs)) } in
    let nclassmap = FUN_FMAP (\s. nclasses ' s) (IMAGE FST nclasses)
    in
       p1s with <| dynobjs := FUNION objmap (FUNION funmap p1s.dynobjs) ;
                   dynclasses := FUNION nclassmap p1s.dynclasses |>
`;

val open_classpath_def = Define`
  open_classpath avoids p1s sofar sfs =
    case sfs of
       [] -> p1s
    || sf :: rest -> open_classpath avoids
                                    (open_classnode avoids
                                                    (mk_member sofar sf)
                                                    p1s)
                                    (mk_member sofar sf)
                                    rest
`;


(* ----------------------------------------------------------------------
    open_path : (string -> bool) -> bool -> StaticField list ->
                P1state -> P1state

    The set of strings records template argument names, which need to
    be avoided when doing calculations of visible names inside classes.

    The boolean records whether we're opening from the global root (::).
    If it's false, then we'll be looking at local variables and classes.
    This might be required when looking at the functions contained inside
    local classes.

    The input P1state is assumed to be "dynamically open" at the level
    of its current_nspath.

   ---------------------------------------------------------------------- *)

val open_path_def = Define`
  open_path avoids absp todo ps =
    let s = ps.global in
    let env0 = if absp then s.genv else s.env in
    let env = THE (apply_path ps.current_nspath env0)
    in
      case todo of
         [] -> ps
      || h::t -> if h IN FDOM (item env).classenv then
                   let root = IDConstant absp (MAP SFName ps.current_nspath) h
                   in
                     open_classpath avoids
                                    (open_classnode avoids root ps)
                                    root
                                    t
                 else
                   let pth = ps.current_nspath ++ [dest_sfname h] in
                   let ps' = open_ftnode pth ps in
                   let ps'' = ps' with current_nspath := pth
                   in
                     open_path avoids absp t ps''
`;

val EnterNSpace_def = Define`
  EnterNSpace n s =
    open_path {} T [SFName n]
              (s with dynns := s.dynns |+ (n,(T,s.current_nspath)))
`;
(* the with clause is necessary in the circumstance where this is the
   first declaration of the namespace *)

val ExitNSpace_def = Define`
  ExitNSpace s =
    open_path {}
              T
              (FRONT (MAP SFName s.current_nspath))
              (open_ftnode [] (empty_p1 s.accdecls s.global))
`;

val rewrite_type_def = Define`
  rewrite_type templvars ps ty =
    let inst =
         <| typemap := (\s. if s IN templvars.tyfvs then TypeID (Base s)
                            else if s IN FDOM ps.dynclasses then
                              let (b,sfs,targs) = ps.dynclasses ' s
                              in
                                TypeID (IDConstant b sfs (SFName s))
                            else if s IN FDOM ps.dynns then
                              let (b,sfnms) = ps.dynns ' s
                              in
                                TypeID (IDConstant b (MAP SFName sfnms)
                                                   (SFName s))
                            else
                              TypeID (Base s)) ;
            valmap := TVAVar ;
            tempmap := (\s. if s IN templvars.tempfvs then (F, [], s)
                            else if s IN FDOM ps.dynclasses then
                              let (b,sfs,targs) = ps.dynclasses ' s
                              in
                                (b,sfs,s)
                            else
                              (F, [], s)) |>
    in
      THE (type_inst inst ty)
`;

val state_NewGVar_def = Define`
  state_NewGVar ty sfs sfnm s =
    s with
       genv := THE (fupd_at_path sfs
                     (\ft. SOME
                           (FTNode
                             (item ft with typemap updated_by
                                                   (\fm. fm |+ (sfnm,ty)))
                             (map ft)))
                     s.genv)
`;


(* ----------------------------------------------------------------------
    NewGVar : CPP_Type -> string -> P1state -> P1state

    "New Global Variable"

    Updates the dynobjs map so that future variable lookups at this level
    will get this variable.  Also updates the global environment in the
    state so that the variable will be "permanently" recorded.

   ---------------------------------------------------------------------- *)

val NewGVar_def = Define`
  NewGVar ty sfnm s =
    let sfnm' = IDConstant T (MAP SFName s.current_nspath) sfnm in
    let (targs,sfstr) = break_sfld sfnm in
    let ty' = rewrite_type (FOLDL (\a ta. a UNION tafrees ta) {} targs) s ty
    in
      s with <| dynobjs :=
                  s.dynobjs |+ (sfstr, (T,MAP SFName s.current_nspath,targs,
                                        dNormalObj)) ;
                global updated_by state_NewGVar ty s.current_nspath sfnm ;
                accdecls := (s.accdecls ++ [Decl (VDec ty' sfnm')]) |>
`;

(* ----------------------------------------------------------------------
    mk_last_init : initializer -> P1state -> P1state

    takes the last declaration off the list of accumulating declarations,
    and replaces it with a version that initialises it with the provided
    initializer

   ---------------------------------------------------------------------- *)

val mk_last_init_def = Define`
  mk_last_init init s =
    let old = LAST s.accdecls in
    let new = case old of
                 Decl (VDec ty nm) -> Decl (VDecInit ty nm init)
              || x -> x
    in
      s with accdecls := (FRONT s.accdecls ++ [new])
`;

(* ----------------------------------------------------------------------
    phase1_expr : frees_record -> P1state -> CExpr -> CExpr
   ---------------------------------------------------------------------- *)

val mk_dynobj_id_def = Define`
  mk_dynobj_id ps sf =
    let (b,sfs,targs) = ps.dynobjs ' (sfld_string sf)
    in
      IDConstant b sfs sf
`;

val idattach_locn_def = Define`
  (idattach_locn (b,sfs1,targs) (IDConstant _ sfs2 sf) =
      IDConstant b (sfs1 ++ sfs2) sf)
`;
val _ = export_rewrites ["idattach_locn_def"]

(* the ps and avoids parameters are schematic *)
val phase1_expr_defn = Defn.Hol_defn "phase1_expr" `
  (phase1_expr (Cnum n) = Cnum n) /\
  (phase1_expr (Cchar n) = Cchar n) /\
  (phase1_expr (Cnullptr ty) = Cnullptr (rewrite_type avoids ps ty)) /\
  (phase1_expr This = This) /\
  (phase1_expr (COr e1 e2) = COr (phase1_expr e1) (phase1_expr e2)) /\
  (phase1_expr (CAnd e1 e2) = CAnd (phase1_expr e1) (phase1_expr e2)) /\
  (phase1_expr (CCond e1 e2 e3) =
       CCond (phase1_expr e1) (phase1_expr e2) (phase1_expr e3)) /\
  (phase1_expr (CApBinary cbop e1 e2) =
       CApBinary cbop (phase1_expr e1) (phase1_expr e2)) /\
  (phase1_expr (CApUnary cuop e) = CApUnary cuop (phase1_expr e)) /\
  (phase1_expr (Addr e) = Addr (phase1_expr e)) /\
  (phase1_expr (Deref e) = Deref (phase1_expr e)) /\
  (phase1_expr (Assign bopopt e1 e2) =
       Assign bopopt (phase1_expr e1) (phase1_expr e2)) /\
  (phase1_expr (FnApp e elist) =
       (* TODO: special case FnApp (Var id) elist to reflect 3.4.2 *)
       FnApp (phase1_expr e) (MAP phase1_expr elist)) /\
  (phase1_expr (CommaSep e1 e2) =
       CommaSep (phase1_expr e1) (phase1_expr e2)) /\
  (phase1_expr (Cast ty e) =
       Cast (rewrite_type avoids ps ty) (phase1_expr e)) /\
  (phase1_expr (PostInc e) = PostInc (phase1_expr e)) /\
  (phase1_expr (New ty args_opt) =
       New (rewrite_type avoids ps ty)
           (case args_opt of
               NONE -> NONE
            || SOME elist -> SOME (MAP phase1_expr elist))) /\
  (phase1_expr (EThrow eopt) = EThrow (OPTION_MAP phase1_expr eopt)) /\

  (* tricky cases *)
  (* field selection *)
  (phase1_expr (SVar e id) =
      let e' = phase1_expr e in
      let ty = @ty. expr_type ps.global RValue e' ty in
      let cnm = @cnm. strip_const ty = Class cnm in
      let ps' =
          case id of
             IDConstant b [] sf -> open_classnode avoids.tyfvs cnm ps
          || IDConstant b (sf1::sfs) sf2 ->
               open_classnode avoids.tyfvs (class_part id) ps
      in
          SVar e' (mk_dynobj_id ps' (IDtl id))) /\

  (phase1_expr (Var id) =
      case id of
         IDConstant T sfs sf ->
           if id_objtype ps.global id = dMember then
             let cnm = class_part id in
             let ps' = open_classnode avoids.tyfvs cnm ps
             in
               SVar (Deref This) (mk_dynobj_id ps' (IDtl id))
           else Var id
      || IDConstant F [] sf ->
           (let qid = idattach_locn (ps.dynobjs ' (sfld_string sf)) id
            in
              (case SND (SND (SND (ps.dynobjs ' (sfld_string sf)))) of
                  dVirtualMember -> SVar (Deref This) id
               || dMember -> SVar (Deref This) qid
               || dStatMember -> Var qid
               || dNormalObj -> Var qid))
      || IDConstant F (h::t) sf ->
            (let s = sfld_string h in
             let qid =
                 if s IN FDOM ps.dynclasses then
                   idattach_locn (ps.dynclasses ' s) id
                 else
                   let (b',ns) = ps.dynns ' s
                   in
                     IDConstant b' (MAP SFName ns ++ (h::t)) sf
             in
               if id_objtype ps.global qid = dMember then
                 let cnm = class_part qid in
                 let ps' = open_classnode avoids.tyfvs cnm ps
                 in
                   SVar (Deref This) (mk_dynobj_id ps' (IDtl qid))
               else Var id)) /\

  (phase1_expr (MemAddr cid fld) =
     let cid' = if is_abs_id cid then cid
                else
                  let sf = IDhd cid in
                  let s = sfld_string sf
                  in
                    if s IN FDOM ps.dynclasses then
                      idattach_locn (ps.dynclasses ' s) cid
                    else
                      let (b,ns) = ps.dynns ' s
                      in
                        idattach_locn (b, MAP SFName ns, []:bool list) cid
     in
       (* there's nothing to do to the field.  Though it may actually be a
          field of some class ancestral to cid', the whole point of the
          calculation of the field address is to calculate it in the context
          of being inside a cid', not the ancestor.  And we can safely leave
          that to the dynamics *)
       MemAddr cid' fld)
`;

val (phase1_expr_def, phase1_expr_ind) = Defn.tprove(
  phase1_expr_defn,
  WF_REL_TAC `^(last (TotalDefn.guessR phase1_expr_defn))` THEN
  SRW_TAC [ARITH_ss][] THEN
  Induct_on `elist` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []);

val _ = save_thm("phase1_expr_def", phase1_expr_def)
val _ = save_thm("phase1_expr_ind", phase1_expr_ind)
val _ = export_rewrites ["phase1_expr_def"]


(* ----------------------------------------------------------------------
    phase1_init : frees_record -> P1state -> initializer -> initializer

    Relationally reworks an initializer to reflect names in scope in
    P1state, avoiding the given frees (which are template parameters).
   ---------------------------------------------------------------------- *)

val phase1_init_def = Define`
  (phase1_init avoids s (DirectInit0 elist)  =
     DirectInit0 (MAP (phase1_expr avoids s) elist)) /\

  (phase1_init avoids s (CopyInit (NormE e se))  =
     CopyInit (NormE (phase1_expr avoids s e) se))

`;
val _ = export_rewrites ["phase1_init_def"]

(* ----------------------------------------------------------------------
    newlocal : P1state -> StaticField -> P1state
   ---------------------------------------------------------------------- *)

(* can't declare a local variable that is a template, so only consider a
   SFName parameter  *)
val newlocal_def = Define`
  newlocal ps (SFName s) ty =
     ps with <| dynobjs := ps.dynobjs |+ (s, (F, [], [], dNormalObj)) ;
                global := ps.global with
                            env updated_by
                              (\ft. FTNode
                                    (item ft with
                                      typemap updated_by
                                              (\fm. fm |+ (SFName s,ty)))
                                    (map ft)) |>
`

(* ----------------------------------------------------------------------
    extract_class_names : frees_record -> P1state -> class_entry ->
                          P1state

    This is used in pass 1 of the analysis of a class declaration,
    where the top-level members have their names added to the current scope.
    This can be done in the order in which the names appear in the class
    definition because reordering isn't allowed to make a difference.
    (IOW, this doesn't detect the static error of having it make a
    difference.)

   ---------------------------------------------------------------------- *)

val extract_class_names_def = Define`
  (extract_class_names avds ps (b,sfs)
                       (CFnDefn v ty sf pms bodyoptopt,stat,p) =
     let (targs,s) = break_sfld sf
     in
       if v then
         (* virtual member functions can't be templates *)
         ps with dynobjs := ps.dynobjs |+ (s, (F, [], [], dVirtualMember))
       else
         let cnm = IDConstant b (FRONT sfs) (LAST sfs) in
         let rty' = rewrite_type avds ps ty in
         let ptys = MAP (rewrite_type avds ps o SND) pms
         in
           if is_virtual ps.global cnm sf rty' ptys then
             ps with
               dynobjs := ps.dynobjs |+ (s, (b, sfs, [], dVirtualMember))
           else
             ps with
               dynobjs := ps.dynobjs |+ (s, (b,sfs,targs,
                                             if stat then dStatMember
                                             else dMember))) /\
  (extract_class_names avds ps (b,sfs) (FldDecl sf ty,stat,p) =
     let (targs,s) = break_sfld sf
     in
       if function_type ty then
         let (rty,ptys) = dest_function_type (rewrite_type avds ps ty) in
         let cnm = IDConstant b (FRONT sfs) (LAST sfs)
         in
           if is_virtual ps.global cnm sf rty ptys then
             ps with
               dynobjs := ps.dynobjs |+ (s, (b, sfs, [], dVirtualMember))
           else
             ps with dynobjs := ps.dynobjs |+ (s, (b, sfs, targs,
                                                   if stat then dStatMember
                                                   else dMember))
       else
         ps with dynobjs := ps.dynobjs |+ (s, (b, sfs, [],
                                               if stat then dStatMember
                                               else dMember))) /\
  (extract_class_names avds ps (b,sfs) (Constructor _ _ _,_,_) = ps) /\
  (extract_class_names avds ps (b,sfs) (Destructor _ _,_,_) = ps) /\
  (extract_class_names avds ps (b,sfs) (NClass sf ciopt,_,_) =
     let (targs, s) = break_sfld sf
     in
       ps with dynclasses updated_by (\fm. fm |+ (s, (b,sfs,targs)))) /\
  (extract_class_names avds ps (b,sfs) (CETemplateDef targs ce, stat, p) =
     extract_class_names (FOLDL (\a ta. a UNION tafrees ta) avds targs)
                         ps
                         (b,sfs)
                         (ce,stat,p))
`

(* ----------------------------------------------------------------------
    phase1_stmt : frees_record -> P1state -> CStmt -> CStmt
   ---------------------------------------------------------------------- *)

val phase1_stmt_defn = Defn.Hol_defn "phase1_stmt" `
  (phase1_stmt avds ps (CLoop (NormE e se) bod) =
     CLoop (NormE (phase1_expr avds ps e) se) (phase1_stmt avds ps bod)) /\
  (phase1_stmt avds ps (CIf (NormE e se) st1 st2) =
     CIf (NormE (phase1_expr avds ps e) se)
         (phase1_stmt avds ps st1)
         (phase1_stmt avds ps st2)) /\
  (phase1_stmt avds ps (Standalone (NormE e se)) =
     Standalone (NormE (phase1_expr avds ps e) se)) /\
  (phase1_stmt avds ps EmptyStmt = EmptyStmt) /\
  (phase1_stmt avds ps (Block F vds sts) =
     let (vds',s') = FOLDL (\ (va,s0) vd. let (vd',s') = phase1_vdec avds s0 vd
                                          in
                                            (va ++ [vd'], s'))
                           ([],ps)
                           vds
     in
       Block F vds' (MAP (phase1_stmt avds s') sts)) /\
  (phase1_stmt avds ps (Ret (NormE e se)) =
     Ret (NormE (phase1_expr avds ps e) se)) /\
  (phase1_stmt avds ps EmptyRet = EmptyRet) /\
  (phase1_stmt avds ps Break = Break) /\
  (phase1_stmt avds ps Cont = Cont) /\
  (phase1_stmt avds ps (Trap tt st) = Trap tt (phase1_stmt avds ps st)) /\
  (phase1_stmt avds ps (Throw NONE) = Throw NONE) /\
  (phase1_stmt avds ps (Throw (SOME (NormE e se))) =
     Throw (SOME (NormE (phase1_expr avds ps e) se))) /\
  (phase1_stmt avds ps (Catch st handlers) =
     Catch (phase1_stmt avds ps st)
           (MAP (\ (epd, est).
                    case epd of
                       NONE -> (NONE, phase1_stmt avds ps est)
                    || SOME (NONE, ty) ->
                               (SOME (NONE, rewrite_type avds ps ty),
                                phase1_stmt avds ps est)
                    || SOME (SOME enm, ty) ->
                         let ty' = rewrite_type avds ps ty
                         in
                           (SOME (SOME enm, ty'),
                            phase1_stmt avds
                                        (newlocal ps (SFName enm) ty')
                                        est))
                handlers)) /\
  (phase1_stmt avds ps ClearExn = ClearExn)

     /\

  (* neither of these handle the definition of structured variables,
     which is impossible in a local scope, even for static data members *)
  (phase1_vdec avds ps (VDec ty nm) =
     let ty' = rewrite_type avds ps ty
     in
       (VDec ty' nm, newlocal ps (IDtl nm) ty')) /\
  (phase1_vdec avds ps (VDecInit ty nm init) =
     let ty' = rewrite_type avds ps ty
     in
       (VDecInit ty' nm (phase1_init avds ps init),
        newlocal ps (IDtl nm) ty')) /\
  (phase1_vdec avds ps (VStrDec cnm cinfo_opt) =
     let (cinfo_opt', ps') = phase1_cinfo_opt avds ps cnm cinfo_opt
     in
       (VStrDec cnm cinfo_opt', ps'))

     /\

  (phase1_cinfo_opt avds ps cnm NONE =
     (NONE,
      case cnm of
        IDConstant F [] (SFName s) ->
          ps with
           <| dynclasses updated_by (\fm. fm |+ (s, (F, [], [])));
              global := ps.global with
                          env updated_by
                            (\ft. FTNode
                                   (item ft with
                                      classenv updated_by
                                        (\fm. fm |+ (SFName s,
                                                     FTNode
                                                       empty_class_envinfo
                                                       FEMPTY)))
                                   (map ft))
           |>)) /\
  (phase1_cinfo_opt avds ps cnm (SOME ci) =
     let ancestors' = MAP (\ (id,b,p). (resolve_classid avds ps id, b, p))
                          ci.ancestors in
     let ps1 = FOLDL (\ps (id,b,p). open_classnode avds.tyfvs id ps)
                     ps ancestors' in
     let ps2 = FOLDL (\s cebp.
                        extract_class_names avds s (F, [IDtl cnm]) cebp)
                     (local_class cnm ps1)
                     ci.fields in
     let (ps3, flds') =
       FOLDL (\ (ps,celist) (ce,b,p).
                let (ps',ce') = phase1_centry avds ps cnm ce
                in
                  (ps', celist ++ [(ce',b,p)]))
             (ps2,[])
             ci.fields
     in
       (SOME <| ancestors := ancestors'; fields := flds' |>, ps''))

     /\

  (* in a local class, member functions can't be templates, and must be
     declared immediately *)
  (* they can be abstract though, which is this case *)
  (phase1_centry avds ps cnm
                 (CFnDefn v retty (SFName s) pms (SOME NONE)) =
     (ps, CFnDefn v
                  (rewrite_type avds ps retty)
                  (SFName s)
                  (MAP (\ (nm,ty). (nm, rewrite_type avds ps ty)) pms)
                  (SOME NONE))) /\
  (phase1_centry avds ps cnm
                 (CFnDefn v retty (SFName s) pms (SOME (SOME bod))) =
     let retty' = rewrite_type avds ps retty in
     let pms' = MAP (\ (nm,ty). (nm, rewrite_type avds ps ty)) pms in
     let ps' = FOLDL (\ ps (nm,ty). newlocal ps (SFName nm) ty) ps pms' in
     let bod' = phase1_stmt avds ps' bod
     in
       (ps, CFnDefn v retty' (SFName s) pms' (SOME (SOME bod'))))
`

val (phase1_stmt_def, phase1_stmt_ind) = Defn.tprove(
  phase1_stmt_defn,
  WF_REL_TAC `measure (\sum.
                        case sum of
                           INL (avds,s,st) -> CStmt_size st
                        || INR (INL (avds,s,vd)) -> var_decl_size vd
                        || INR (INR (INL (avds,ps,cnm,cinfo_opt))) ->
                             option_size class_info_size cinfo_opt
                        || INR (INR (INR (avds,ps,cnm,ce))) ->
                             class_entry_size ce)` THEN
  SRW_TAC [ARITH_ss][] THENL [
    Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Induct_on `l` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `handlers` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `handlers` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `handlers` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `vds` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `sts` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Cases_on `cinfo_opt` THEN
    SRW_TAC [ARITH_ss][basicSizeTheory.option_size_def]
  ])
val _ = save_thm("phase1_stmt_def", phase1_stmt_def)
val _ = save_thm("phase1_stmt_ind", phase1_stmt_ind)
val _ = export_rewrites ["phase1_stmt_def"]


(* ----------------------------------------------------------------------
    phase1 :
   ---------------------------------------------------------------------- *)

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
  (!n ds s.
     (LAST s.current_nspath = n)
   ==>
     phase1 (ExitNS n :: ds, s) (ds, ExitNSpace s))

   /\

  (* RULE-ID: [phase1-decl-vdec] *)
  (* note there is effectively no circumstance in which a simple variable
     declaration can be of a structured name.   One can redeclare functions
     with structured names, but this achieves absolutely nothing. *)
  (!ty snm ds s.
     T
   ==>
     phase1 (P1Decl (Decl (VDec ty (Base snm))) :: ds, s)
            (ds, NewGVar ty (SFName snm) s))

   /\

  (* RULE-ID: [phase1-decl-vdec-template-function] *)
  (* 14 p2 insists that in declaring/defining a function template, the
     identifier be a template-name, not a template-id.  The former is just
     a name, whereas an id has the angle-brackets *)
  (!ty targs sfnm s ds.
     function_type ty
   ==>
     phase1 (CONS
               (P1Decl
                  (TemplateDef
                     targs
                     (Decl (VDec ty (IDConstant F [] (SFName sfnm))))))
               ds, s)
            (ds, NewGVar ty (SFTempCall sfnm targs) s))

   /\

  (* RULE-ID: [phase1-decl-vdecinit] *)
  (!s s' ds ty sfnm init.
     (s' = NewGVar ty (SFName sfnm) s)
   ==>
     phase1 (P1Decl (Decl (VDecInit ty (Base sfnm) init)) :: ds, s)
            (ds, mk_last_init (phase1_init {} s' init) s'))
`;

(*

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
     ^mng (NormE (SVar (LVal a (Class cnm) p) fld) se) s
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


*)

val _ = export_theory ()


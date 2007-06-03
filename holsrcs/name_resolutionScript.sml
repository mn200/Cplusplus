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
    dynns : string |-> string list ;
    global : state ;
    accdecls : ext_decl list |>
`;

(* ----------------------------------------------------------------------
    cresolve_nspaces : P1state -> CPP_ID -> string list

    returns the path of namespaces that the resolved id belongs to
    (assuming it identifies a class)
   ---------------------------------------------------------------------- *)

val ecresolve_nspaces_def = Define`
  (ecresolve_nspaces env [] = []) /\
  (ecresolve_nspaces env (SFName s :: t) =
     if SFName s IN FDOM (item env).classenv then []
     else s :: ecresolve_nspaces (map env ' s) t) /\
  (ecresolve_nspaces env (SFTempCall _ _ :: _) = [])
`
val _ = export_rewrites ["ecresolve_nspaces_def"]

val cresolve_nspaces_def = Define`
  (cresolve_nspaces ps (IDConstant T sfs sf) =
     ecresolve_nspaces ps.global.genv (sfs ++ [sf])) /\
  (cresolve_nspaces ps (IDConstant F sfs sf) =
     let h = IDhd (IDConstant F sfs sf) in
     let s = sfld_string h
     in
        if s IN FDOM ps.dynclasses then
          let (b,pre_sfs,targs) = ps.dynclasses ' s
          in
            if b then ecresolve_nspaces ps.global.env (pre_sfs ++ [h])
            else []
        else
          let ns = ps.dynns ' s
          in
            ecresolve_nspaces ps.global.env (MAP SFName ns ++ sfs))
`;

(* ----------------------------------------------------------------------
    resolve_classid : P1state -> CPP_ID -> CPP_ID
   ---------------------------------------------------------------------- *)

val resolve_classid_def = Define`
  (resolve_classid ps (IDConstant T sfs sf) = IDConstant T sfs sf) /\
  (resolve_classid ps (IDConstant F [] sf) =
       let (b,sfs,targs) = ps.dynclasses ' (sfld_string sf)
       in
         IDConstant b sfs sf) /\
  (resolve_classid ps (IDConstant F (SFName s :: sfs) sf) =
     if s IN FDOM ps.dynclasses then
       let (b,pre_sfs,targs) = ps.dynclasses ' s
       in
         IDConstant b (pre_sfs ++ SFName s :: sfs) sf
     else
       let sfnms = ps.dynns ' s
       in
         IDConstant T (MAP SFName sfnms ++ SFName s :: sfs) sf) /\
  (resolve_classid ps (IDConstant F (SFTempCall s targs :: sfs) sf) =
     let (b,pre_sfs,targs') = ps.dynclasses ' s
     in
       IDConstant b (pre_sfs ++ SFTempCall s targs :: sfs) sf)
`;

val break_sfld_def = Define`
  (break_sfld (SFName s) = ([], s)) /\
  (break_sfld (SFTempCall s targs) = (targs, s))
`;
val _ = export_rewrites ["break_sfld_def"]

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
                  FUNION (FUN_FMAP (\s. pth) (FDOM (map env_at_pth)))
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
  (open_classpath avoids p1s sofar [] = p1s) /\
  (open_classpath avoids p1s sofar (sf::rest) =
      open_classpath avoids
                     (open_classnode avoids (mk_member sofar sf) p1s)
                     (mk_member sofar sf)
                     rest)
`;
val _ = export_rewrites ["open_classpath_def"]


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

val open_nspath_def = Define`
  (open_nspath avds ps (absp,root) [] = ps) /\
  (open_nspath avds ps (absp,root) (sf::sfs) =
     let env0 = if absp then ps.global.genv else ps.global.env in
     let env = THE (apply_path root env0)
     in
       if sf IN FDOM (item env).classenv then
         let root = IDConstant absp (MAP SFName root) sf in
         let rootcenv = open_classnode avds root ps
         in
           open_classpath avds rootcenv root sfs
       else
         open_nspath avds ps (absp,root ++ [sfld_string sf]) sfs)
`;
val _ = export_rewrites ["open_nspath_def"]

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
              (s with dynns := s.dynns |+ (n,s.current_nspath))
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
                              let sfnms = ps.dynns ' s
                              in
                                TypeID (IDConstant T
                                                   (MAP SFName sfnms)
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

val is_unqvar_def = Define`
  (is_unqvar (Var (IDConstant b sfs (SFName s))) = ~b /\ (sfs = [])) /\
  (is_unqvar e = F)
`;
val _ = export_rewrites ["is_unqvar_def"]
val dest_unqvar_def = Define`
  dest_unqvar (Var (IDConstant F [] (SFName s))) = s
`;
val _ = export_rewrites ["dest_unqvar_def"]

(* ----------------------------------------------------------------------
    ass_nspaces_classes : CPP_Type -> (CPP_ID set # CPP_ID set)

    "associated namespaces and classes", as per 3.4.2 p2
   ---------------------------------------------------------------------- *)
val enclosing_class_def = Define`
  (enclosing_class ps (IDConstant b [] sf) = NONE) /\
  (enclosing_class ps (IDConstant b (sf1::sfs) sf2) =
     let candidate = IDConstant b (FRONT (sf1::sfs)) (LAST (sf1::sfs))
     in
       if candidate IN defined_classes ps.global then SOME candidate
       else NONE)
`;
val _ = export_rewrites ["enclosing_class_def"]

(* avds and ps are schematic *)
val ass_nspaces_classes_defn = Hol_defn "ass_nspaces_classes" `
  (ass_nspaces_classes (Ptr ty) = ass_nspaces_classes ty) /\
  (ass_nspaces_classes (Array ty n) = ass_nspaces_classes ty) /\
  (ass_nspaces_classes (MPtr id ty) =
     let (idns, idcs) = ass_nspaces_classes (Class id) in
     let (tyns, tycs) = ass_nspaces_classes ty
     in
       (idns UNION tyns, idcs UNION tycs)) /\
  (ass_nspaces_classes (Function retty argtys) =
     FOLDL (\ (acns, accs) ty. let (tyns, tycs) = ass_nspaces_classes ty
                               in
                                 (acns UNION tyns, accs UNION tycs))
           (ass_nspaces_classes retty)
           argtys) /\
  (ass_nspaces_classes (Class id) =
     let enccs = case enclosing_class ps id of
                    NONE -> {}
                 || SOME id' -> {id} in
     let idcs0 = enccs UNION { b | (ps.global,avds.tyfvs) |- id <= b } in
     let idcs = idcs0 INTER { cnm | DISJOINT (cppidfrees cnm) avds }
     in
       (IMAGE (cresolve_nspaces ps) idcs, idcs)) /\
  (ass_nspaces_classes ty = ({}, {}))
`

val (ass_nspaces_classes_def, ass_nspaces_classes_ind) = Defn.tprove(
  ass_nspaces_classes_defn,
  WF_REL_TAC `measure (\ty. if ?id ty0. ty = MPtr id ty0 then
                              1 + 2 * CPP_Type_size ty
                            else 2 * CPP_Type_size ty)` THEN
  SRW_TAC [ARITH_ss][] THEN
  Induct_on `argtys` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []);
val _ = save_thm("ass_nspaces_classes_def", ass_nspaces_classes_def)
val _ = save_thm("ass_nspaces_classes_ind", ass_nspaces_classes_ind)
val _ = export_rewrites ["ass_nspaces_classes_def"]


(* ----------------------------------------------------------------------
    phase1_expr : frees_record -> P1state -> CExpr -> CExpr
   ---------------------------------------------------------------------- *)

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
     let elist' = MAP phase1_expr elist in
     let e' =
         if is_unqvar e then
           let fnm = dest_unqvar e
           in
             if fnm IN FDOM ps.dynobjs then phase1_expr e
             else
               let atys = @atys. listRel (expr_type ps.global RValue) elist'
                                 atys in
               let foldthis ps0 ty =
                   let nss = FST (ass_nspaces_classes avoids ps0 ty) in
                   let nsl = SET_TO_LIST nss
                   in
                     FOLDL (\ps00 ns. open_ftnode ns ps00) ps0 nsl
               in
               let ps' = FOLDL foldthis ps atys
               in
                 Var (idattach_locn (ps'.dynobjs ' fnm)
                                    (IDConstant F [] (SFName fnm)))
         else
           phase1_expr e
     in
       FnApp e' elist') /\
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
          (* open the class scope here, not the path to the scope;
             classes don't insert their enclosing scopes' names into their
             own scope - see notes/namespace-nested-class.cpp *)
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
                   IDConstant T (MAP SFName (ps.dynns ' s) ++ (h::t)) sf
             in
               if id_objtype ps.global qid = dMember then
                 let cnm = class_part qid in
                 let ps' = open_classnode avoids.tyfvs cnm ps
                 in
                   SVar (Deref This) (mk_dynobj_id ps' (IDtl qid))
               else Var qid)) /\

  (phase1_expr (MemAddr cid fld) =
     let cid' = if is_abs_id cid then cid
                else
                  let sf = IDhd cid in
                  let s = sfld_string sf
                  in
                    if s IN FDOM ps.dynclasses then
                      idattach_locn (ps.dynclasses ' s) cid
                    else
                      let ns = ps.dynns ' s
                      in
                        idattach_locn (T, MAP SFName ns, []:bool list) cid
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
    new_class : CPP_ID -> state_class_info -> state -> state

    adds a new class at the given location, with no fields, and the
    given identifiers as ancestors
   ---------------------------------------------------------------------- *)

val cenv_new_class_def = Define`
  (cenv_new_class [sf] info (cenv : StaticField |-> class_env) =
     cenv |+ (sf, FTNode <| statvars := FEMPTY;
                            info := info;
                            refs := FEMPTY |>
                         FEMPTY)) /\
  (cenv_new_class (sf::sfs) info cenv =
     cenv |+ (sf, FTNode
                    (item (cenv ' sf))
                    (cenv_new_class sfs info (map (cenv ' sf)))))
`
val _ = export_rewrites ["cenv_new_class_def"]

val enew_class_def = Define`
  (enew_class (IDConstant b [] sf) info (env : environment) =
     FTNode (item env with classenv updated_by cenv_new_class [sf] info)
            (map env)) /\
  (enew_class (IDConstant b (sf1::sfs) sf2) info env =
     if sf1 IN FDOM (item env).classenv then
       FTNode (item env with
                 classenv updated_by
                   (cenv_new_class (sf1::(sfs ++ [sf2])) info))
              (map env)
     else
       FTNode (item env)
              (map env |+ (sfld_string sf1,
                           enew_class (IDConstant b sfs sf2)
                                      info
                                      (map env ' (sfld_string sf1)))))
`;
val _ = export_rewrites ["enew_class_def"]

val new_class_def = Define`
  new_class cnm info s =
    if is_abs_id cnm then s with genv updated_by enew_class cnm info
    else s with env updated_by enew_class cnm info
`;
val _ = export_rewrites ["new_class_def"]

(* ----------------------------------------------------------------------
    new_class_field : (bool # StaticField list) ->
                      (class_entry # bool # protection) -> state -> state
   ---------------------------------------------------------------------- *)

val cenew_class_field_def = Define`
  (cenew_class_field [sf] cebp (cenv : StaticField |-> class_env) =
     cenv |+ (sf, FTNode
                   (item (cenv ' sf) with
                    info updated_by
                      (\ iuds_opt.
                         let (i,uds) = THE iuds_opt
                         in
                           SOME
                             (i with fields := (i.fields ++ [cebp]), uds)))
                   (map (cenv ' sf)))) /\
  (cenew_class_field (h::t) cebp cenv =
     cenv |+ (h, FTNode (item (cenv ' h))
                        (cenew_class_field t cebp (map (cenv ' h)))))
`;
val _ = export_rewrites ["cenew_class_field_def"]

val enew_class_field_def = Define`
  (enew_class_field [sf] cebp (env : environment) =
     FTNode (item env with
               classenv updated_by cenew_class_field [sf] cebp)
            (map env)) /\
  (enew_class_field (sf :: sfs) cebp env =
     if sf IN FDOM (item env).classenv then
       FTNode (item env with classenv
                  updated_by cenew_class_field (sf :: sfs) cebp)
              (map env)
     else
       FTNode (item env)
              (map env |+ (sfld_string sf,
                           enew_class_field sfs cebp
                                            (map env ' (sfld_string sf)))))
`;
val _ = export_rewrites ["enew_class_field_def"]

val new_class_field_def = Define`
  new_class_field (b,sfs) cebp s =
    if b then s with genv updated_by enew_class_field sfs cebp
    else s with env updated_by enew_class_field sfs cebp
`
val _ = export_rewrites ["new_class_field_def"]

(* ----------------------------------------------------------------------
    extract_class_names : frees_record -> P1state -> class_entry ->
                          P1state

    This is used in pass 1 of the analysis of a class declaration,
    where the top-level members have their names added to the current scope.
    This can be done in the order in which the names appear in the class
    definition because reordering isn't allowed to make a difference.
    (IOW, this doesn't detect the static error of having it make a
    difference.)

    Affect only ps.global; allowing for dynamic names to be created with
    an appropriate call to open_classnode later.

   ---------------------------------------------------------------------- *)

val extract_class_names_defn = Hol_defn "extract_class_names" `
  (extract_class_names avds ps (b,sfs)
                       (CFnDefn v ty sf pms bodyoptopt,stat,p) =
     let (targs,s) = break_sfld sf in
     let rty' = rewrite_type avds ps ty in
     let pms' = MAP (\ (n,ty). (n, rewrite_type avds ps ty)) pms in
     let ptys = MAP SND pms'
     in
       ps with global updated_by
       new_class_field (b,sfs) (CFnDefn v rty' sf pms' bodyoptopt,stat,p)) /\
  (extract_class_names avds ps (b,sfs) (FldDecl sf ty,stat,p) =
     let (targs,s) = break_sfld sf in
     let ty' = rewrite_type avds ps ty
     in
       ps with global updated_by
                new_class_field (b,sfs) (FldDecl sf ty',stat,p)) /\
  (extract_class_names avds ps (b,sfs) (Constructor _ _ _,_,_) = ps) /\
  (extract_class_names avds ps (b,sfs) (Destructor _ _,_,_) = ps) /\
  (extract_class_names avds ps (b,sfs) (NClass sf NONE,_,_) =
     let (targs, s) = break_sfld sf
     in
        ps with global updated_by
                   new_class (IDConstant b sfs sf) NONE) /\
  (extract_class_names avds ps (b,sfs) (NClass sf (SOME ci),_,_) =
     let (targs, s) = break_sfld sf in
     let ancs' = MAP (\ (id,b,p). (resolve_classid ps id, b, p))
                     ci.ancestors in
     let ps0 = ps with global updated_by
                   new_class (IDConstant b sfs sf)
                       (SOME (<| ancestors := ancs'; fields := [] |>, {}))
     in
       FOLDL (\ps cebp. extract_class_names avds ps (b,sfs ++ [sf]) cebp)
             ps0
             ci.fields) /\
  (extract_class_names avds ps (b,sfs) (CETemplateDef targs ce, stat, p) =
     extract_class_names (FOLDL (\a ta. a UNION tafrees ta) avds targs)
                         ps
                         (b,sfs)
                         (ce,stat,p))
`

val (extract_class_names_def, extract_class_names_ind) = Defn.tprove(
  extract_class_names_defn,
  WF_REL_TAC `measure (\ (avds,ps,sfs,cebp). class_entry_size (FST cebp))` THEN
  SRW_TAC [ARITH_ss][] THEN
  Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Induct_on `l` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []);
val _ = save_thm("extract_class_names_def", extract_class_names_def)
val _ = save_thm("extract_class_names_ind", extract_class_names_ind)
val _ = export_rewrites ["extract_class_names_def"]


(* ----------------------------------------------------------------------
    local_class : CPP_ID -> P1state -> P1state
   ---------------------------------------------------------------------- *)

val local_class_def = Define`
  local_class (IDConstant F [] (SFName s)) ps =
    ps with dynclasses := ps.dynclasses |+ (s, (F, [], []))
`;


(* ---------------------------------------------------------------------- *)

(* P1state -> CPP_ID -> CPP_ID *)
val resolve_meminit_id_def = Define`
  (resolve_meminit_id cnm ps (IDConstant F [] (SFName s)) =
     if s IN FDOM ps.dynobjs then
       mk_member cnm (SFName s)
     else idattach_locn (ps.dynclasses ' s) (IDConstant F [] (SFName s))) /\
  (resolve_meminit_id cnm ps memid = resolve_classid ps memid)
`;


val phase1_meminit_def = Define`
  phase1_meminit avds cnm param_scope class_scope (mid, args) =
    let mid' = resolve_meminit_id cnm class_scope mid in
    let args' =
      case args of
         NONE -> NONE
      || SOME elist -> SOME (MAP (phase1_expr avds param_scope) elist)
    in
      (mid', args')
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
     let ancestors' = MAP (\ (id,b,p). (resolve_classid ps id, b, p))
                          ci.ancestors in
     let ps0 = ps with global updated_by
                 new_class cnm (SOME (<| ancestors := ancestors' ;
                                         fields := [] |>, {})) in
     let ps1 = open_path avds.tyfvs F (id_sfs cnm) ps0 in
     let ps2 = FOLDL (\s cebp.
                        extract_class_names avds s (F, [IDtl cnm]) cebp)
                     ps1
                     ci.fields in
     let ps3 = open_path avds.tyfvs F (id_sfs cnm) ps2 in
     let flds' =
       FOLDL (\ celist (ce,b,p).
                let ce' = phase1_centry avds ps cnm ce
                in
                  celist ++ [(ce',b,p)])
             []
             ci.fields
     in
       (SOME <| ancestors := ancestors'; fields := flds' |>,
        ps3 with <| dynobjs := ps.dynobjs;
                    dynclasses := ps.dynclasses |>))

     /\

  (* in a local class, member functions can't be templates, and must be
     declared immediately *)
  (* they can be abstract though, which is this case *)
  (phase1_centry avds ps cnm
                 (CFnDefn v retty (SFName s) pms (SOME NONE)) =
     CFnDefn v (rewrite_type avds ps retty)
             (SFName s)
             (MAP (\ (nm,ty). (nm, rewrite_type avds ps ty)) pms)
             (SOME NONE)) /\
  (phase1_centry avds ps cnm
                 (CFnDefn v retty (SFName s) pms (SOME (SOME bod))) =
     let retty' = rewrite_type avds ps retty in
     let pms' = MAP (\ (nm,ty). (nm, rewrite_type avds ps ty)) pms in
     let ps' = FOLDL (\ ps (nm,ty). newlocal ps (SFName nm) ty) ps pms' in
     let bod' = phase1_stmt avds ps' bod
     in
       CFnDefn v retty' (SFName s) pms' (SOME (SOME bod'))) /\
  (phase1_centry avds ps cnm (FldDecl sf ty) =
     let ty' = rewrite_type avds ps ty in FldDecl sf ty') /\
  (phase1_centry avds ps cnm (Constructor pms meminits bodo) =
     let pms' = (MAP (\ (nm,ty). (nm, rewrite_type avds ps ty)) pms) in
     let param_scope =
       FOLDL (\ps (nm,ty). newlocal ps (SFName nm) ty) ps pms' in
     let meminits' = MAP (phase1_meminit avds cnm param_scope ps) meminits
     in
       Constructor pms' meminits'
                   (OPTION_MAP (phase1_stmt avds param_scope) bodo)) /\
  (phase1_centry avds ps cnm (Destructor (b:bool) (bodo: CStmt option)) =
     Destructor b (OPTION_MAP (phase1_stmt avds ps) bodo)) /\
  (phase1_centry avds ps cnm (NClass nsf NONE) = NClass nsf NONE) /\
  (phase1_centry avds ps cnm (NClass nsf (SOME ci)) =
     (* have already pre-processed body, so ps.global knows all about
        the nested class's fields *)
     let ancs' = MAP (\ (id,b,p). resolve_classid ps id, b, p) ci.ancestors in
     let flds' =
           FOLDL (\acc (ce,b,p).
                     acc ++ [(phase1_centry avds ps (mk_member cnm nsf) ce,
                              b, p)])
                 []
                 ci.fields
     in
       NClass nsf (SOME <| ancestors := ancs'; fields := flds' |>))

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
    Induct_on `handlers` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `handlers` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `handlers` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Induct_on `l` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Induct_on `l` THEN SRW_TAC [][] THEN
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
    phase1_fndefn : free_record -> CPP_Type -> CPP_ID ->
                    (string # CPP_Type) list -> CStmt ->
                    P1state -> P1state

   ---------------------------------------------------------------------- *)

val phase1_fndefn_def = Define`
  phase1_fndefn avds retty fnm pms body ps =
    let retty' = rewrite_type avds ps retty in
    let pms' = MAP (\ (nm,ty). (nm, rewrite_type avds ps ty)) pms in
    let funty = Function retty' (MAP SND pms') in
    let (fnm',declared_ps, body_ps) =
      case fnm of (* if the name is qualified, then there must be an
                     existing declaration, so we don't need to alter
                     anything in the state *)
         IDConstant T [] sf -> ARB (* must be an error, see 8.3 p1 *)
      || IDConstant T (sf1::sfs) sf2 ->
            (fnm, ps, open_path avds.tyfvs T (sf1::sfs) ps)
      || IDConstant F [] sf ->
            (IDConstant T (MAP SFName ps.current_nspath) sf,
             NewGVar funty sf ps,
             NewGVar funty sf ps)
      || IDConstant F (sf1::sfs) sf2 ->
            let fnm' = resolve_classid ps fnm in
            let (b,sfs,sf) = dest_id fnm'
            in
              (fnm', ps, open_path avds.tyfvs b sfs ps)
    in
    let ps' = FOLDL (\ps (n,ty). newlocal ps (SFName n) ty) body_ps pms' in
    let body' = phase1_stmt avds ps' body
    in
      declared_ps with
        accdecls := (declared_ps.accdecls ++ [FnDefn retty' fnm' pms' body'])
`;

(* ----------------------------------------------------------------------
    phase1_gcentry : free_record -> P1state -> CPP_ID -> class_entry ->
                     class_entry
   ---------------------------------------------------------------------- *)


(* see phase1_centry (part of phase1_stmt) for what happens to class entries
   in local class definitions *)
val phase1_gcentry_defn = Hol_defn "phase1_gcentry" `
  (phase1_gcentry avds ps cnm (CFnDefn v retty (SFName s) pms bod) =
     let retty' = rewrite_type avds ps retty in
     let pms' = MAP (\ (nm,ty). (nm, rewrite_type avds ps ty)) pms in
     let ps' = FOLDL (\ps (nm,ty). newlocal ps (SFName nm) ty) ps pms' in
     let bod' = case bod of
                   NONE -> NONE
                || SOME NONE -> SOME NONE
                || SOME (SOME st) -> SOME (SOME (phase1_stmt avds ps' st))
     in
        CFnDefn v retty' (SFName s) pms' bod') /\
  (phase1_gcentry avds ps cnm (FldDecl sf ty) =
     FldDecl sf (rewrite_type avds ps ty)) /\
  (phase1_gcentry avds ps cnm (CETemplateDef targs ce) =
     CETemplateDef targs
                    (phase1_gcentry
                       (FOLDL (\a ta. a UNION tafrees ta) avds targs)
                       ps cnm ce)) /\
  (phase1_gcentry avds ps cnm (Constructor pms meminits bodo) =
     let pms' = (MAP (\ (nm,ty). (nm, rewrite_type avds ps ty)) pms) in
     let param_scope =
       FOLDL (\ps (nm,ty). newlocal ps (SFName nm) ty) ps pms' in
     let meminits' = MAP (phase1_meminit avds cnm param_scope ps) meminits
     in
       Constructor pms' meminits'
                   (OPTION_MAP (phase1_stmt avds param_scope) bodo)) /\
  (phase1_gcentry avds ps cnm (Destructor (b:bool) (bodo: CStmt option)) =
     Destructor b (OPTION_MAP (phase1_stmt avds ps) bodo)) /\
  (phase1_gcentry avds ps cnm (NClass nsf NONE) = NClass nsf NONE) /\
  (phase1_gcentry avds ps cnm (NClass nsf (SOME ci)) =
     (* have already pre-processed body, so ps.global knows all about
        the nested class's fields *)
     let ancs' = MAP (\ (id,b,p). resolve_classid ps id, b, p) ci.ancestors in
     let flds' =
           FOLDL (\acc (ce,b,p).
                     acc ++ [(phase1_gcentry avds ps (mk_member cnm nsf) ce,
                              b, p)])
                 []
                 ci.fields
     in
       NClass nsf (SOME <| ancestors := ancs'; fields := flds' |>))
`;

val (phase1_gcentry_def, phase1_gcentry_ind) = Defn.tprove(
  phase1_gcentry_defn,
  WF_REL_TAC `measure (\ (avds,ps,cnm,ce). class_entry_size ce)` THEN
  SRW_TAC [ARITH_ss][] THEN
  Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Induct_on `l` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []);
val _ = save_thm("phase1_gcentry_def", phase1_gcentry_def)
val _ = save_thm("phase1_gcentry_ind", phase1_gcentry_ind)
val _ = export_rewrites ["phase1_gcentry_def"]



(* ----------------------------------------------------------------------
    phase1_gclassdefn : free_record -> CPP_ID -> class_info option ->
                        P1state -> P1state

   ---------------------------------------------------------------------- *)

val phase1_gclassdefn_def = Define`
  (phase1_gclassdefn avds cnm NONE ps =

     (* 7.1.5.3 p1 implies that cnm will be a simple identifier or a
        possibly qualified template identifier (if the avds set is
        empty, then this would be an explicit specialisation;
        otherwise this would be the declaration of a partial
        specialisation); explicit instantiation is handled elsewhere
     *)

     case cnm of
        IDConstant F [] (SFName s) ->
           (let csfs = MAP SFName ps.current_nspath in
            let fullnm = IDConstant T csfs (SFName s)
            in
              ps with <| dynclasses updated_by (\fm. fm |+ (s, (T, csfs, [])));
                         global updated_by new_class fullnm NONE;
                         accdecls := (ps.accdecls ++
                                        [Decl (VStrDec fullnm NONE)]) |>)
     || IDConstant b sfs (SFTempCall s targs) ->
          let ns = cresolve_nspaces ps cnm in
          let fullnm = resolve_classid ps cnm
          in
            ps with <| dynclasses updated_by
                         (\fm. if ns = ps.current_nspath then
                                 fm |+ (s, (T, MAP SFName ns, targs))
                               else fm);
                       global updated_by new_class fullnm NONE;
                       accdecls := (ps.accdecls ++
                                      [Decl (VStrDec fullnm NONE)]) |>) /\

  (phase1_gclassdefn avds cnm (SOME ci) ps =
     let ancs' = MAP (\ (id,b,p). (resolve_classid ps id, b, p))
                     ci.ancestors in
     let fullnm =
           case cnm of
              IDConstant b [] sf ->
                 IDConstant b (MAP SFName ps.current_nspath) sf
           || IDConstant b sfs sf -> resolve_classid ps cnm in
     let ps0 = ps with global updated_by
                 new_class fullnm
                           (SOME (<| ancestors := ancs' ;
                                     fields := [] |>, {})) in
     let ps1 = open_path avds.tyfvs T (id_sfs fullnm) ps0 in
     let ps2 = FOLDL (\s cebp.
                        extract_class_names avds s (T, id_sfs fullnm) cebp)
                     ps1
                     ci.fields in
     let ps3 = open_path avds.tyfvs T (id_sfs fullnm) ps2 in
     let flds' =
         FOLDL (\ celist (ce,b,p).
                  let ce' = phase1_gcentry avds ps cnm ce
                  in
                    (celist ++ [(ce',b,p)]))
               []
               ci.fields
     in
       ps3 with <| dynobjs := ps0.dynobjs ; dynclasses := ps0.dynclasses ;
                   accdecls := (ps.accdecls ++
                                [Decl (VStrDec fullnm
                                               (SOME <| ancestors := ancs' ;
                                                        fields := flds' |>))])
                |>)
`;


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

   /\

  (* RULE-ID: [phase1-decl-fndefn] *)
  (!s ds retty fnm pms body.
     T
   ==>
     phase1 (P1Decl (FnDefn retty fnm pms body) :: ds, s)
            (ds, phase1_fndefn {} retty fnm pms body s))

   /\

  (* RULE-ID: [phase1-decl-classdefn] *)
  (!id cinfoopt ds s.
     T
   ==>
     phase1 (P1Decl (Decl (VStrDec id cinfoopt)) :: ds, s)
            (ds, phase1_gclassdefn {} id cinfoopt s))

   /\

  (* RULE-ID: [phase1-decl-template-class] *)
  (!targs id cinfoopt ds s tafs.
     (tafs = FOLDL (\a ta. a UNION tafrees ta) {} targs)
   ==>
     phase1 (P1Decl (TemplateDef targs (Decl (VStrDec id cinfoopt))) :: ds, s)
            (ds, phase1_gclassdefn tafs id cinfoopt s))

   /\

  (* RULE-ID: [phase1-decl-template-function] *)
  (!s targs ds retty fnm pms body tafs.
     (tafs = FOLDL (\a ta. a UNION tafrees ta) {} targs)
   ==>
     phase1 (P1Decl (TemplateDef targs (FnDefn retty fnm pms body)) :: ds, s)
            (ds, phase1_fndefn tafs retty fnm pms body s))

`;

val _ = export_theory ()


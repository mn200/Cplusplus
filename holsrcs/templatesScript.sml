(* Compilation-time program instantiation *)

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
open statesTheory aggregatesTheory instantiationTheory
     name_resolutionTheory

val _ = new_theory "templates"


(* ----------------------------------------------------------------------
    process "stuff"
      = 'process member function' and 'process definitions' in Siek and
        Taha, but we have lots more than just member functions to deal
        with.

    The basic behaviour is
                             stuff
      templates * functions --------> templates * functions

    where the templates and functions are template classes and
    template functions in any state of instantiation.  When stuff is
    encountered, we look at the types inside it and make sure that the
    templates on the left can instantiate those types.  This gives rise
    to more template definitions, and these are added to the "output"
    templates of the relation.
   ---------------------------------------------------------------------- *)

(* the top-level template calls occurring within an id *)
val id_tcalls_def = Define`
  (id_tcalls b sfs [] last =
     case last of
        IDName _ -> {}
     || IDTempCall s targs -> {IDConstant b sfs last}) /\
  (id_tcalls b sfs (h :: t) last =
     case h of
        IDName _ -> id_tcalls b (sfs ++ [h]) t last
     || IDTempCall s targs -> (IDConstant b sfs h) INSERT
                              id_tcalls b (sfs ++ [h]) t last)
`;

(* the template calls occurring within a concrete type *)
val ttypes_def = Define`
  (ttypes Void = {}) /\
  (ttypes BChar = {}) /\
  (ttypes Bool = {}) /\
  (ttypes (Unsigned _) = {}) /\
  (ttypes (Signed _) = {}) /\
  (ttypes (Class cid) = cidttypes cid) /\
  (ttypes Float = {}) /\
  (ttypes Double = {}) /\
  (ttypes LDouble = {}) /\
  (ttypes (Ptr ty) = {}) /\ (* don't descend here - this could be an
                               incomplete type, so not needing instantiation *)
  (ttypes (MPtr cid ty) = cidttypes cid UNION ttypes ty) /\
  (ttypes (Ref ty) = ttypes ty) /\
  (ttypes (Array ty n) = ttypes ty) /\
  (ttypes (Function ty tylist) = ttypes ty UNION ttypesl tylist) /\
  (ttypes (Const ty) = ttypes ty) /\
  (ttypes (TypeID cid) = cidttypes cid)

    /\

  (ttypesl [] = {}) /\
  (ttypesl (ty::tyl) = ttypes ty UNION ttypesl tyl) /\

  (cidttypes (IDConstant b sfs sf) = id_tcalls b [] sfs sf UNION
                                     sfldl_ttypes sfs UNION sfld_ttypes sf) /\

  (sfld_ttypes (IDTempCall s tal) = talttypes tal) /\
  (sfld_ttypes (IDName s) = {}) /\

  (tattypes (TType ty) = ttypes ty) /\
  (tattypes (TTemp tid) = {}) /\
  (tattypes (TVal tva) = tvattypes tva) /\

  (talttypes [] = {}) /\
  (talttypes (ta::tal) = tattypes ta UNION talttypes tal) /\

  (tvattypes (TNum i) = {}) /\
  (tvattypes (TObj cid) = cidttypes cid) /\
  (tvattypes (TMPtr cid ty) = cidttypes cid UNION ttypes ty) /\
  (tvattypes (TVAVar s) = {}) /\

  (sfldl_ttypes [] = {}) /\
  (sfldl_ttypes (h::t) = sfld_ttypes h UNION sfldl_ttypes t)
`;

val expr_ttypes_def = Define`
  (expr_ttypes (Cnum i) = {}) /\
  (expr_ttypes (Cchar i) = {}) /\
  (expr_ttypes (Cnullptr ty) = ttypes ty) /\
  (expr_ttypes This = {}) /\
  (expr_ttypes (Var cid) = cidttypes cid) /\
  (expr_ttypes (COr e1 e2) = expr_ttypes e1 UNION expr_ttypes e2) /\
  (expr_ttypes (CAnd e1 e2) = expr_ttypes e1 UNION expr_ttypes e2) /\
  (expr_ttypes (CCond e1 e2 e3) = expr_ttypes e1 UNION expr_ttypes e2 UNION
                                  expr_ttypes e3) /\
  (expr_ttypes (CApBinary bop e1 e2) = expr_ttypes e1 UNION expr_ttypes e2) /\
  (expr_ttypes (CApUnary uop e) = expr_ttypes e) /\
  (expr_ttypes (Deref e) = expr_ttypes e) /\
  (expr_ttypes (Addr e) = expr_ttypes e) /\
  (expr_ttypes (MemAddr cid sfld) = cidttypes cid) /\
  (expr_ttypes (Assign bopt e1 e2) = expr_ttypes e1 UNION expr_ttypes e2) /\
  (expr_ttypes (SVar e cid) = expr_ttypes e UNION cidttypes cid) /\
  (expr_ttypes (FnApp e elist) = expr_ttypes e UNION exprl_ttypes elist) /\
  (expr_ttypes (CommaSep e1 e2) = expr_ttypes e1 UNION expr_ttypes e2) /\
  (expr_ttypes (Cast ty e) = ttypes ty UNION expr_ttypes e) /\
  (expr_ttypes (PostInc e) = expr_ttypes e) /\
  (expr_ttypes (New ty elopt) = ttypes ty UNION exprlopt_ttypes elopt) /\
  (expr_ttypes (FnApp_sqpt rvrt e elist) =
     expr_ttypes e UNION exprl_ttypes elist) /\
  (expr_ttypes (LVal _ _ _) = {}) /\
  (expr_ttypes (FVal _ _ _) = {}) /\
  (expr_ttypes (ConstructorFVal _ _ _ _) = {}) /\
  (expr_ttypes (ConstructedVal _ _ _) = {}) /\
  (expr_ttypes (DestructorCall _ _) = {}) /\
  (expr_ttypes (RValreq e) = expr_ttypes e) /\
  (expr_ttypes (ECompVal _ _) = {}) /\
  (expr_ttypes (EThrow eopt) = expropt_ttypes eopt) /\
  (expr_ttypes UndefinedExpr = {}) /\

  (exprl_ttypes [] = {}) /\
  (exprl_ttypes (e::elist) = expr_ttypes e UNION exprl_ttypes elist) /\

  (exprlopt_ttypes NONE = {}) /\
  (exprlopt_ttypes (SOME elist) = exprl_ttypes elist)  /\

  (expropt_ttypes NONE = {}) /\
  (expropt_ttypes (SOME e) = expr_ttypes e)
`;

(* what template calls are made inside a statement?
   This question is only asked of forms that are
   entirely ground, and have had their names resolved  *)
val stmt_ttypes_defn = Defn.Hol_defn "stmt_ttypes" `
  (stmt_ttypes (CLoop ee body) = eexpr_ttypes ee UNION stmt_ttypes body) /\
  (stmt_ttypes (CIf ee s1 s2) =
     eexpr_ttypes ee UNION stmt_ttypes s1 UNION stmt_ttypes s2) /\
  (stmt_ttypes (Standalone ee) = eexpr_ttypes ee) /\
  (stmt_ttypes (Block b vdl stl) =
     FOLDL (\a vd. a UNION vd_ttypes vd) {} vdl UNION
     FOLDL (\a st. a UNION stmt_ttypes st) {} stl) /\
  (stmt_ttypes (Ret ee) = eexpr_ttypes ee) /\
  (stmt_ttypes (Trap tt s) = stmt_ttypes s) /\
  (stmt_ttypes (Throw NONE) = {}) /\
  (stmt_ttypes (Throw (SOME ee)) = eexpr_ttypes ee) /\
  (stmt_ttypes (Catch s handlers) =
     stmt_ttypes s UNION
     FOLDL (\a (ep,st). a UNION stmt_ttypes st UNION
                        (case ep of
                            NONE -> {}
                         || SOME (_1, ty) -> ttypes ty))
           {} handlers) /\
  (stmt_ttypes _ = {}) /\

  (eexpr_ttypes (EX e se) = expr_ttypes e) /\
  (eexpr_ttypes (ST s c) = stmt_ttypes s) /\

  (* a forward declaration of a template function will cause its
     instantiation, so look for template calls in the name as well as the
     type *)
  (vd_ttypes (VDec ty nm) = ttypes ty UNION cidttypes nm) /\

  (* something that's initialised can't have a template name *)
  (vd_ttypes (VDecInit ty nm init) = ttypes ty UNION init_ttypes init) /\

  (vd_ttypes (VDecInitA ty vl init) = {}) /\ (* dynamic value only *)
  (vd_ttypes (VStrDec cspec cinfo_opt) =
       (case cinfo_opt of
           NONE -> {}
        || SOME ci -> cinfo_ttypes ci))

     /\

  (centry_ttypes (CFnDefn virtp retty sfld params bodyoptopt) =
     if sfldfrees sfld = {} then
       ttypes retty UNION sfld_ttypes sfld UNION
       FOLDL (\a (nm,ty). a UNION ttypes ty) {} params UNION
       (case bodyoptopt of NONE -> {}
                        || SOME NONE -> {}
                        || SOME (SOME st) -> stmt_ttypes st)
     else {}) /\
  (centry_ttypes (FldDecl string ty) = ttypes ty) /\
  (centry_ttypes (Constructor params meminits bodyopt) =
     FOLDL (\a (nm,ty). a UNION ttypes ty) {} params UNION
     (case bodyopt of NONE -> {} || SOME st -> stmt_ttypes st) UNION
     FOLDL (\a (memid, argsopt).
              a UNION cidttypes memid UNION
              exprlopt_ttypes argsopt)
           {} meminits) /\
  (centry_ttypes (Destructor virtp bodyopt) =
     case bodyopt of NONE -> {} || SOME s -> stmt_ttypes s) /\

  (cinfo_ttypes ci =
     FOLDL (\a (ce,b,p). a UNION centry_ttypes ce) {} ci.fields UNION
     FOLDL (\a (cs,b,p). a UNION cidttypes cs) {} ci.ancestors) /\

  (init_ttypes (DirectInit0 elist) = exprl_ttypes elist) /\
  (init_ttypes (DirectInit ee) = eexpr_ttypes ee) /\
  (init_ttypes (CopyInit ee) = eexpr_ttypes ee)
`;

val (stmt_ttypes_def, stmt_ttypes_ind) = Defn.tprove(stmt_ttypes_defn,
  WF_REL_TAC `^(last (TotalDefn.guessR stmt_ttypes_defn))` THEN
  SRW_TAC [ARITH_ss][] THENL [
    Induct_on `handlers` THEN SRW_TAC [][] THEN
    RES_TAC THEN SRW_TAC [ARITH_ss][],

    Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Induct_on `l` THEN SRW_TAC [ARITH_ss][] THEN RES_TAC THEN
    SRW_TAC [ARITH_ss][],

    Induct_on `vdl` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [DISJ_IMP_THM, FORALL_AND_THM] THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

    Induct_on `stl` THEN ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss) [] THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val _ = save_thm("stmt_ttypes_def", stmt_ttypes_def)
val _ = save_thm("stmt_ttypes_ind", stmt_ttypes_ind)
val _ = export_rewrites ["stmt_ttypes_def"]

val extdecl_ttypes_defn = Defn.Hol_defn "extdecl_ttypes" `
  (extdecl_ttypes (FnDefn ty nm params body) =
     if cppidfrees nm = {} then
       ttypes ty UNION cidttypes nm UNION
       FOLDL (\a (n,ty). a UNION ttypes ty) {} params UNION
       stmt_ttypes body
     else {}) /\
  (extdecl_ttypes (Decl d) = vd_ttypes d) /\
  (extdecl_ttypes (ClassConDef id params meminits body) =
     if cppidfrees id = {} then
       centry_ttypes (Constructor params meminits (SOME body))
     else {}) /\
  (extdecl_ttypes (ClassDestDef id body) =
     if cppidfrees id = {} then
       centry_ttypes (Destructor T (SOME body))
     else {}) /\
  (extdecl_ttypes (NameSpace n edecs) =
     FOLDL (\a ed. a UNION extdecl_ttypes ed) {} edecs) /\
  (extdecl_ttypes (TemplateInst id) = cidttypes id)
`;

val (extdecl_ttypes_def, extdecl_ttypes_ind) = Defn.tprove(
  extdecl_ttypes_defn,
  WF_REL_TAC `measure ext_decl_size` THEN
  Induct_on `edecs` THEN
  SRW_TAC [][#2 (TypeBase.size_of ``:ext_decl``)] THEN
  SRW_TAC [ARITH_ss][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`n`, `ed`] MP_TAC) THEN
  SRW_TAC [ARITH_ss][]);

val _ = save_thm("extdecl_ttypes_def", extdecl_ttypes_def)
val _ = save_thm("extdecl_ttypes_ind", extdecl_ttypes_ind)
val _ = export_rewrites ["extdecl_ttypes_def"]


val expr_constructors_defn = Hol_defn "expr_constructors" `
  (expr_constructors (COr e1 e2) =
     expr_constructors e1 UNION expr_constructors e2) /\
  (expr_constructors (CAnd e1 e2) =
     expr_constructors e1 UNION expr_constructors e2) /\
  (expr_constructors (CApBinary cbop e1 e2) =
     expr_constructors e1 UNION expr_constructors e2) /\
  (expr_constructors (Assign cbopopt e1 e2) =
     expr_constructors e1 UNION expr_constructors e2) /\
  (expr_constructors (CommaSep e1 e2) =
     expr_constructors e1 UNION expr_constructors e2) /\
  (expr_constructors (CCond e1 e2 e3) =
     expr_constructors e1 UNION expr_constructors e2 UNION
     expr_constructors e3) /\
  (expr_constructors (Deref e) = expr_constructors e) /\
  (expr_constructors (Addr e) = expr_constructors e) /\
  (expr_constructors (PostInc e) = expr_constructors e) /\
  (expr_constructors (Cast ty e) = expr_constructors e) /\
  (expr_constructors (CApUnary cuop e) = expr_constructors e) /\
  (expr_constructors (New ty optargs) =
     expr_optl_constructors optargs UNION
     (if class_type ty then
        let args = case optargs of NONE -> [] || SOME l -> l in
        let tyl = @tyl. listRel (expr_type s RValue) args tyl
        in
          {(dest_class ty, tyl)}
      else {})) /\
  (expr_constructors e = {}) /\

  (expr_optl_constructors NONE = {}) /\
  (expr_optl_constructors (SOME elist) = exprl_constructors elist) /\

  (exprl_constructors [] = {}) /\
  (exprl_constructors (e::elist) =
     expr_constructors e UNION exprl_constructors elist)
`;

val (expr_constructors_def, expr_constructors_ind) = Defn.tprove(
  expr_constructors_defn,
  WF_REL_TAC `^(last (TotalDefn.guessR expr_constructors_defn))` THEN
  SRW_TAC [ARITH_ss][] THEN
  Cases_on `optargs` THEN
  SRW_TAC [ARITH_ss][#2 (TypeBase.size_of ``:'a option``)] THEN
  Induct_on `x` THEN SRW_TAC [ARITH_ss][#2 (TypeBase.size_of ``:'a list``)]);

val stmt_constructors_defn = Hol_defn "stmt_constructors" `
  (stmt_constructors (CLoop (EX e se) bod) =
     expr_constructors s e UNION stmt_constructors bod) /\
  (stmt_constructors (CIf (EX e se) s1 s2) =
     expr_constructors s e UNION stmt_constructors s2 UNION
     stmt_constructors s2) /\
  (stmt_constructors (Standalone (EX e se)) = expr_constructors s e) /\
  (stmt_constructors (Block b vds sts) =
     FOLDL (\a vd. a UNION vd_constructors vd)
           (FOLDL (\a st. a UNION stmt_constructors st) {} sts)
           vds) /\
  (stmt_constructors (Ret (EX e se)) = expr_constructors s e) /\
  (stmt_constructors (Trap tt st) = stmt_constructors st) /\
  (stmt_constructors (Throw (SOME (EX e se))) = expr_constructors s e) /\
  (stmt_constructors (Catch st handlers) =
     FOLDL (\a (e,st). a UNION stmt_constructors st )
           (stmt_constructors st)
           handlers) /\
  (stmt_constructors st = {}) /\

  (vd_constructors (VDec ty nm) =
     if class_type ty then {(dest_class ty, [])} else {}) /\
  (vd_constructors (VDecInit ty nm (DirectInit0 elist)) =
     if class_type ty then
       let tyl = @tyl. listRel (expr_type s RValue) elist tyl
                  (* should allow for reference types *)
       in
         {(dest_class ty, tyl)}
     else {}) /\
  (vd_constructors (VDecInit ty nm (CopyInit (EX e se))) =
     expr_constructors s e UNION
     (if class_type ty then
       let cnm = dest_class ty in
       let ety = @ty. expr_type s RValue e ty
       in
         if const_type ety then
           {(cnm, [Ref (Const (Class cnm))])}
         else {(cnm, [Ref (Class cnm)])}
     else {})) /\
  (* ignore other constructors; local classes won't have templates; and
     when called for non-local declarations, we can rely on function
     bodies having been stripped out.  *)
  (vd_constructors x = {})
`;


val (stmt_constructors_def, stmt_constructors_ind) = Defn.tprove(
  stmt_constructors_defn,
  WF_REL_TAC `^(last (TotalDefn.guessR stmt_constructors_defn))` THEN
  SRW_TAC [ARITH_ss][] THENL [
    Induct_on `handlers` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `vds` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `sts` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);
val _ = save_thm("stmt_constructors_def", stmt_constructors_def)
val _ = save_thm("stmt_constructors_ind", stmt_constructors_ind)
val _ = export_rewrites ["stmt_constructors_def"]

val edec_constructors_def = Define`
  (edec_constructors s (FnDefn retty nm pms bod) =
     FOLDL (\a (nm,ty).
             a UNION
             (if class_type (strip_const ty) then
                {(dest_class (strip_const ty), [Ref ty])}
              else {}))
          (stmt_constructors s bod)
          pms) /\
  (edec_constructors s (Decl d) = vd_constructors s d) /\
  (edec_constructors s (ClassConDef cnm pms meminits bod) =
     FOLDL (\a (id,args).
              if is_qualified id then
                let elist = case args of NONE -> [] || SOME el -> el in
                let tyl = @tyl. listRel (expr_type s RValue) elist tyl
                in
                  (id,tyl) INSERT a
              else a)
           (FOLDL (\a (nm, ty).
                      a UNION
                      (if class_type (strip_const ty) then
                         {(dest_class (strip_const ty), [Ref ty])}
                       else {}))
                  (stmt_constructors s bod)
                  pms)
           meminits) /\
  (edec_constructors s (ClassDestDef cnm bod) = stmt_constructors s bod) /\
  (edec_constructors s ed = {})
`;

(* ----------------------------------------------------------------------
    Process definitions
      inspired by Program Instantiation (Fig. 6) of Siek and Taha
   ---------------------------------------------------------------------- *)

(* Siek and Taha have two sorts of external declaration, template
   definitions of classes (which are patterns wrapped around a field
   declaration), and member function definitions.

   We have rather more complexity than this.  We have normal
   functions, multiple members per class, and data fields.  In
   addition, we can have template member functions, template
   functions, and template template parameters

   This means that we need to do things slightly differently.

   The transformation process takes "states" to "states", where a
   state couples a phase-1 state with a pair of lists of declarations:
   the ground declarations and the template declarations.  After the
   program's actual declarations are read in, only the ground
   declaration list can grow.

   The Basic Loop is

     1. scan ground declarations for a reference to a type that has
        not got an exact declaration in the pattern list.  Get the
        appropriate instantiation of this type, and add it to the
        ground declaraiton list.  (Only add the class declaration;
        don't include any member definitions.)

        Put it into the namespace belonging to the argument types, and
        use phase1 analysis to resolve any free names.

     2. scan the ground declarations for references to undefined
        functions or static member objects.  For each such,
        instantiate, adding to the appropriate namespace as before.

     REPEAT until quiescent.

*)

(* removes function bodies, turning them into  *)
val strip_centry_defn = Hol_defn "strip_centry" `
  (strip_centry cnm (CFnDefn virtp retty sf pms (SOME (SOME body))) =
     (CFnDefn virtp retty sf pms NONE,
      [FnDefn retty (mk_member cnm sf) pms body])) /\
  (strip_centry cnm (NClass sf (SOME ci)) =
     let (ci', ds) = strip_cinfo (mk_member cnm sf) ci
     in
       (NClass sf (SOME ci'), ds)) /\
  (strip_centry cnm (CETemplateDef targs (NClass (IDName s) (SOME ci))) =
     let (ci',ds) = strip_cinfo (mk_member cnm (IDTempCall s targs)) ci
     in
       (CETemplateDef targs (NClass (IDName s) (SOME ci')), ds)) /\
  (strip_centry cnm (CETemplateDef targs
                                   (CFnDefn virtp retty sf pms
                                            (SOME (SOME body)))) =
     (CETemplateDef targs (CFnDefn virtp retty sf pms NONE),
      [TemplateDef targs (FnDefn retty (mk_member cnm sf) pms body)])) /\
  (strip_centry cnm (Constructor pms meminits (SOME bod)) =
     (Constructor pms meminits NONE, [ClassConDef cnm pms meminits bod])) /\
  (strip_centry cnm (Destructor virtp (SOME bod)) =
     (Destructor virtp NONE, [ClassDestDef cnm bod])) /\
  (strip_centry cnm x = (x, [])) /\

  (strip_cinfo cnm ci =
     let (flds, ds) = FOLDL (\ (ces,ds) (ce,b,p).
                               let (ce',ds0) = strip_centry cnm ce
                               in
                                 (ces ++ [(ce',b,p)], ds ++ ds0))
                            ([], [])
                            ci.fields
     in
       (ci with fields := flds, ds))
`

val (strip_centry_def, strip_centry_ind) = Defn.tprove(
  strip_centry_defn,
  WF_REL_TAC `measure (\s. case s of INL (cnm, ce) -> class_entry_size ce
                                  || INR (cnm, ci) -> class_info_size ci)` THEN
  SRW_TAC [ARITH_ss][] THEN
  Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Induct_on `l` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []);
val _ = save_thm("strip_centry_def", strip_centry_def)
val _ = save_thm("strip_centry_ind", strip_centry_ind)
val _ = export_rewrites ["strip_centry_def"]


(* restricts an instantiation to be with respect to a particular set of
   free varirables *)
val _ = set_fixity "only_changes" (Infixl 500)
val only_changes_def = Define`
  inst only_changes frees =
    !id. DISJOINT (cppidfrees id) frees ==>
         (cppID_inst inst id = SOME id)
`;

val _ = set_fixity "is_sub_tid" (Infix(NONASSOC, 425))
val is_sub_tid_def = Define`
  (IDConstant b1 sfs1 sf1) is_sub_tid (IDConstant b2 sfs2 sf2) =
     (b1 = b2) /\ (?s targs. sf1 = IDTempCall s targs) /\
     ?rst. sfs2 = sfs1 ++ sf1::rst
`;



val targsfrees_def = Define`
  targsfrees talist = FOLDL (\a ta. tafrees ta UNION a) {} talist
`;


(* "returns" the uninstantiated cinfo for the given class identifier *)
val best_class_match_def = Define`
  best_class_match Temps id sub (id', ci) =
    (?targs. (cppID_inst sub id' = SOME id) /\
             MEM (TemplateDef targs (Decl (VStrDec id' ci))) Temps /\
             sub only_changes targsfrees targs) /\
    !id2 ci2 sub2 targs.
        MEM (TemplateDef targs (Decl (VStrDec id2 ci2))) Temps /\
        sub2 only_changes targsfrees targs /\
        (cppID_inst sub2 id2 = SOME id) ==>
        ?sub'. (cppID_inst sub' id2 = SOME id') /\
               sub' only_changes targsfrees targs
`;

(* "returns" the uninstantiated defn for the given function identifier *)
val best_function_match_def = Define`
  best_function_match Temps id sub (id', (retty,pms,bod)) =
    (?targs.
        (cppID_inst sub id' = SOME id) /\
        MEM (TemplateDef targs (FnDefn retty id' pms bod)) Temps /\
        sub only_changes targsfrees targs) /\
    !id2 retty2 pms2 bod2 sub2 targs.
        MEM (TemplateDef targs (FnDefn retty2 id2 pms2 bod2)) Temps /\
        sub2 only_changes targsfrees targs /\
        (cppID_inst sub2 id2 = SOME id) ==>
        ?sub'. (cppID_inst sub' id2 = SOME id') /\
               sub' only_changes targsfrees targs
`;

val best_obj_match_def = Define`
  best_obj_match Temps id sub (id', (ty, init)) =
    (?targs.
        (cppID_inst sub id' = SOME id) /\
        MEM (TemplateDef targs (Decl (VDecInit ty id' init))) Temps /\
        sub only_changes targsfrees targs) /\
    !id2 ty2 init2 sub2 targs.
        MEM (TemplateDef targs (Decl (VDecInit ty2 id2 init2))) Temps /\
        sub2 only_changes targsfrees targs /\
        (cppID_inst sub2 id2 = SOME id) ==>
        ?sub'. (cppID_inst sub' id2 = SOME id') /\
               sub' only_changes targsfrees targs
`;

val best_constructor_match_def = Define`
  best_constructor_match Temps (id,types) sub  (id', (meminits,pms,bod)) =
    (?targs.
        (cppID_inst sub id' = SOME id) /\
        MEM (TemplateDef targs (ClassConDef id' pms meminits bod)) Temps /\
        sub only_changes targsfrees targs /\
        (MAP (\ (n,ty). THE (type_inst sub ty)) pms = types)) /\
    !id2 pms2 meminits2 bod2 sub2 targs.
        (cppID_inst sub id' = SOME id) /\
        MEM (TemplateDef targs (ClassConDef id' pms2 meminits2 bod2)) Temps /\
        sub2 only_changes targsfrees targs /\
        (MAP (\ (n,ty). THE (type_inst sub2 ty)) pms2 = types) ==>
        ?sub'. (cppID_inst sub' id2 = SOME id') /\
               sub' only_changes targsfrees targs
`;

val best_destructor_match_def = Define`
  best_destructor_match Temps id sub (id',bod) =
    (?targs.
        (cppID_inst sub id' = SOME id) /\
        MEM (TemplateDef targs (ClassDestDef id' bod)) Temps /\
        sub only_changes targsfrees targs) /\
    !id2 bod2 sub2 targs.
        (cppID_inst sub2 id' = SOME id) /\
        MEM (TemplateDef targs (ClassDestDef id2 bod2)) Temps /\
        ?sub'. (cppID_inst sub' id2 = SOME id') /\
               sub' only_changes targsfrees targs
`;




val declared_type_def = Define`
  (declared_type (Decl (VStrDec id ci)) = {id}) /\
  (declared_type x = {})
`
val _ = export_rewrites ["declared_type_def"]

val defined_fn_def = Define`
  (defined_fn (FnDefn retty id pms bod) = {id}) /\
  (defined_fn x = {})
`;
val _ = export_rewrites ["defined_fn_def"]

val declared_types_def = Define`
  (declared_types [] = {}) /\
  (declared_types (e::es) = declared_type e UNION declared_types es)
`;
val _ = export_rewrites ["declared_types_def"]

val defined_fns_def = Define`
  (defined_fns [] = {}) /\
  (defined_fns (e::es) = defined_fn e UNION defined_fns es)
`;
val _ = export_rewrites ["defined_fns_def"]

val defined_obj_def = Define`
  (defined_obj (Decl (VDecInit ty nm init)) = {nm}) /\
  (defined_obj x = {})
`;
val defined_objs_def = Define`
  (defined_objs [] = {}) /\
  (defined_objs (e::es) = defined_obj e UNION defined_objs es)
`;

val defined_constructor_def = Define`
  (defined_constructor (ClassConDef cnm pms meminits bod) =
     {(cnm,MAP SND pms)}) /\
  (defined_constructor e = {})
`;
val defined_constructors_def = Define`
  (defined_constructors [] = {}) /\
  (defined_constructors (e::es) =
     defined_constructor e UNION defined_constructors es)
`;

val defined_destructor_def = Define`
  (defined_destructor (ClassDestDef id bod) = {id}) /\
  (defined_destructor e = {})
`;
val defined_destructors_def = Define`
  (defined_destructors [] = {}) /\
  (defined_destructors (e::es) =
     defined_destructor e UNION defined_destructors es)
`;

val used_ttypes_def = Define`
  used_ttypes pats decls =
      { id | ?d id' ci sub targs.
               MEM d decls /\
               id IN extdecl_ttypes d /\
               MEM (TemplateDef targs (Decl (VStrDec id' ci))) pats /\
               sub only_changes targsfrees targs /\
               (cppID_inst sub id' = SOME id) }
`;

val used_tfns_def = Define`
  used_tfns pats decls =
     { id | ?d id' sub targs retty pms bod.
               MEM d decls /\
               id IN extdecl_ttypes d /\
               MEM (TemplateDef targs (FnDefn retty id' pms bod)) pats /\
               sub only_changes targsfrees targs /\
               (cppID_inst sub id' = SOME id) }
`;

val used_statmembers_def = Define`
  used_statmembers pats decls =
     { id | ?d id' ty sub targs init.
               MEM d decls /\
               id IN extdecl_ttypes d /\
               MEM (TemplateDef targs (Decl (VDecInit ty id' init))) pats /\
               sub only_changes targsfrees targs /\
               (cppID_inst sub id' = SOME id) }
`;

val used_constructors_def = Define`
  used_constructors pats decls =
     { id | ?d id' sub targs pms mis bod.
               MEM d decls /\
               id IN extdecl_ttypes d /\
               MEM (TemplateDef targs (ClassConDef id' pms mis bod)) pats /\
               sub only_changes targsfrees targs /\
               (cppID_inst sub id' = SOME id) }
`;


(* seek out necessary types *)
val template_phase1_def = Define`
  template_phase1 pats (ps0, grds0) (ps, grds) =
    ?id id' sub ci0.
      id IN used_ttypes pats grds0 /\
      ~(id IN declared_types grds0) /\
      (!sub_id. sub_id is_sub_tid id ==> sub_id IN declared_types grds0) /\
      best_class_match pats id sub (id', ci0) /\
      phase1 ([P1Decl (Decl (VStrDec id (cinfo_inst sub (THE ci0))))], ps0)
             ([], ps) /\
      (grds = grds0 ++ [LAST ps.accdecls])
`

(* extract and instantiate function references *)
val template_phase2_fns_def = Define`
  template_phase2_fns pats (ps0, grds0) (ps, grds) =
    ?id id' sub retty pms bod.
      id IN used_tfns pats grds0 /\
      ~(id IN defined_fns grds0) /\
      (!sub_id. sub_id is_sub_tid id ==> sub_id IN declared_types grds0) /\
      best_function_match pats id sub (id', (retty, pms, bod)) /\
      phase1 ([P1Decl (FnDefn
                         (THE (type_inst sub retty))
                         id
                         (MAP (\ (n,ty). (n,THE (type_inst sub ty))) pms)
                         (THE (stmt_inst sub bod)))], ps0)
             ([], ps) /\
      (grds = grds0 ++ [LAST ps.accdecls])
`;

(* extract and instantiate static members of template classes *)
val template_phase2_statmems_def = Define`
  template_phase2_statmems pats (ps0, grds0) (ps, grds) =
    ?id id' sub ty init.
      id IN used_statmembers pats grds0 /\
      ~(id IN defined_objs grds0) /\
      (!sub_id. sub_id is_sub_tid id ==> sub_id IN declared_types grds0) /\
      best_obj_match pats id sub (id', (ty, init)) /\
      phase1 ([P1Decl (Decl (VDecInit
                               (THE (type_inst sub ty))
                               id
                               (THE (initialiser_inst sub init))))], ps0)
             ([], ps) /\
      (grds = grds0 ++ [LAST ps.accdecls])
`;

(* extract and instantiate constructors for template classes *)
val template_phase2_constructors_def = Define`
  template_phase2_constructors pats (ps0, grds0) (ps, grds) =
    ?id id' s args sub bod edec meminits pms types.
      MEM edec grds0 /\
      (id,types) IN edec_constructors ps0.global edec /\
      (IDtl id = IDTempCall s args) /\
      ~((id,types) IN defined_constructors grds0) /\
      (!sub_id. sub_id is_sub_tid id ==> sub_id IN declared_types grds0) /\
      id IN declared_types grds0 /\
      best_constructor_match pats (id,types) sub (id', (meminits,pms,bod)) /\
      phase1 ([P1Decl (ClassConDef
                         id
                         (MAP (\ (nm,ty). (nm, THE (type_inst sub ty))) pms)
                         (MAP (\ (id,elistopt).
                                 (THE (cppID_inst sub id),
                                  case elistopt of
                                     NONE -> NONE
                                  || SOME elist ->
                                       SOME (MAP (\e. THE (expr_inst sub e))
                                                 elist)))
                              meminits)
                         (THE (stmt_inst sub bod)))], ps0)
            ([], ps) /\
      (grds = grds0 ++ [LAST ps.accdecls])
`;

val template_phase2_destructors_def = Define`
  template_phase2_destructors pats (ps0, grds0) (ps, grds) =
    ?id bod id' sub.
      id IN declared_types grds0 /\
      ~(id IN defined_destructors grds) /\
      (!sub_id. sub_id is_sub_tid id ==> sub_id IN declared_types grds0) /\
      best_destructor_match pats id sub (id',bod) /\
      phase1 ([P1Decl (ClassDestDef id (THE (stmt_inst sub bod)))], ps0)
             ([], ps) /\
      (grds = grds0 ++ [LAST ps.accdecls])
`;


val template_analysis_def = Define`
  template_analysis pats =
    TC ((template_phase2_destructors pats RUNION
         template_phase2_constructors pats RUNION
         template_phase2_statmems pats RUNION
         template_phase2_fns pats) O
        TC (template_phase1 pats))
`;


val _ = export_theory();



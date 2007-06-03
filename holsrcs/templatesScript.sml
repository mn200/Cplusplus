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
        SFName _ -> {}
     || SFTempCall s targs -> {IDConstant b sfs last}) /\
  (id_tcalls b sfs (h :: t) last =
     case h of
        SFName _ -> id_tcalls b (sfs ++ [h]) t last
     || SFTempCall s targs -> (IDConstant b sfs h) INSERT
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
  (ttypes (Ptr ty) = ttypes ty) /\
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

  (sfld_ttypes (SFTempCall s tal) = talttypes tal) /\
  (sfld_ttypes (SFName s) = {}) /\

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
  (expr_ttypes (FnApp_sqpt e elist) =
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

  (eexpr_ttypes (NormE e se) = expr_ttypes e) /\
  (eexpr_ttypes (EStmt s c) = stmt_ttypes s) /\

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


(* ----------------------------------------------------------------------
    process definitions
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

(* restricts an instantiation to be with respect to a particular set of 
   free varirables *)
val _ = set_fixity "only_changes" (Infixl 500)
val only_changes_def = Define`
  inst only_changes frees = 
    !id. DISJOINT (cppidfrees id) frees ==> 
         (cppID_inst inst id = SOME id)
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


val declared_type_def = Define`
  (declared_type (Decl (VStrDec id ci)) = {id}) /\
  (declared_type x = {})
`
val _ = export_rewrites ["declared_type_def"]

val declared_types_def = Define`
  (declared_types [] = {}) /\
  (declared_types (e::es) = declared_type e UNION declared_types es)
`;
val _ = export_rewrites ["declared_types_def"]

val used_ttypes_def = Define`
  used_ttypes pats decls = 
      { id | ?d id' ci sub targs. 
               MEM d decls /\
               id IN extdecl_ttypes d /\
               MEM (TemplateDef targs (Decl (VStrDec id' ci))) pats /\
               sub only_changes targsfrees targs /\
               (cppID_inst sub id' = SOME id) }
`;

(* removes function bodies, turning them into  *)
val strip_centry_defn = Hol_defn "strip_centry" `
  (strip_centry cnm (CFnDefn virtp retty sf pms (SOME (SOME body))) = 
     (CFnDefn virtp retty sf pms NONE, 
      [FnDefn retty (mk_member cnm sf) pms body])) /\
  (strip_centry cnm (NClass sf (SOME ci)) = 
     let (ci', ds) = strip_cinfo (mk_member cnm sf) ci
     in
       (NClass sf (SOME ci'), ds)) /\
  (strip_centry cnm (CETemplateDef targs (NClass (SFName s) (SOME ci))) = 
     let (ci',ds) = strip_cinfo (mk_member cnm (SFTempCall s targs)) ci
     in
       (CETemplateDef targs (NClass (SFName s) (SOME ci')), ds)) /\
  (strip_centry cnm (CETemplateDef targs 
                                   (CFnDefn virtp retty sf pms 
                                            (SOME (SOME body)))) = 
     (CETemplateDef targs (CFnDefn virtp retty sf pms NONE), 
      [TemplateDef targs (FnDefn retty (mk_member cnm sf) pms body)])) /\
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


val template_phase1_def = Define`
  template_phase1 pats (ps0, grds0) (ps, grds) = 
    ?id id' sub ci0 stripped_ci final_ci. 
      id IN used_ttypes pats grds0 /\
      ~(id IN declared_types grds0) /\
      best_class_match pats id sub (id', ci0) /\
      phase1 (P1Decl (
        

    case FINDL (\d. ?tid sub id ci. 
                      tid IN extdecl_ttypes d /\
                      best_class_match pats tid sub (id,ci) /\
                      !ci'. 
                             
  


(*

val _ = Hol_datatype `inststate = Running of 'a | Done of 'b | Failed`
val _ = Hol_datatype `instneed_type = NeedFn | NeedVr`


val _ = Hol_datatype `
  FunctionRef = CallConstructor of CPP_ID => CPP_Type list
              | CallDestructor of CPP_ID
              | FnCall of CPP_ID
              | StaticVar of CPP_ID => string
`


val _ = Hol_datatype`
   fnref_ctxt = <| classes : CPP_ID |-> class_info  ;
                   vars    : CPP_ID |-> CPP_Type ;
                   thisinfo: CPP_Type option |>
`;
val empty_ctxt_def = Define`
  empty_ctxt = <| classes := FEMPTY ; vars := FEMPTY ; thisinfo := NONE |>
`;
val ctxt_typing_def = Define`
  ctxt_typing (c:fnref_ctxt) =
    <| class_fields :=
          (\ci. mapPartial
                     (\ce. case ce of
                              (CFnDefn ret nm args bod, stat, prot) -> NONE
                           || (FldDecl fld ty, stat, prot) ->
                                 if stat then NONE
                                 else SOME (SFName fld, ty)
                           || _ -> NONE)
                     (ci.fields)) o_f c.classes ;
       abs_classes := {};
       this_type := c.thisinfo;
       var_types := c.vars
    |>
`;

val extend_ctxt_def = Define`
  extend_ctxt ty nm ctxt = ctxt with vars updated_by (\fm. fm |+ (nm,ty))
`;

val str_extend_ctxt_def = Define`
  str_extend_ctxt nm ciopt ctxt =
    case ciopt of NONE -> ctxt
               || SOME ci -> ctxt with classes updated_by (\fm. fm |+ (nm,ci))
`

(* given a "context", checks whether or not a name is the name of a
   function.  If so, it may need to have its declaration and definition
   instantiated from a template *)
val is_function_name_def = Define`
  is_function_name ctxt id =
    case id of
       IDVar s -> F (* should never have variables at this stage *)
    || IDFld classid sfld ->
          (?ci ty nm params bopt stat prot.
              (FLOOKUP ctxt.classes classid = SOME ci) /\
              MEM (CFnDefn ty nm params bopt, stat, prot) ci.fields /\
              (sfld_basename nm = sfld_basename sfld))
    || IDTempCall tid args -> T
    || IDConstant tname ->
          ?ty tname'. (FLOOKUP ctxt.vars tname' = SOME ty) /\
                      function_type ty /\
                      (id_basename tname' = SOME tname)
`;

val expr_extract_fnrefs_defn = Hol_defn "expr_extract_fnrefs" `
  (expr_extract_fnrefs ctxt (Var n) =
     if is_function_name ctxt n then {FnCall n} else {}) /\
  (expr_extract_fnrefs ctxt (COr e1 e2) =
     expr_extract_fnrefs ctxt e1 UNION expr_extract_fnrefs ctxt e2) /\
  (expr_extract_fnrefs ctxt (CAnd e1 e2) =
     expr_extract_fnrefs ctxt e1 UNION expr_extract_fnrefs ctxt e2) /\
  (expr_extract_fnrefs ctxt (CCond e1 e2 e3) =
     expr_extract_fnrefs ctxt e1 UNION
     expr_extract_fnrefs ctxt e2 UNION
     expr_extract_fnrefs ctxt e3) /\
  (expr_extract_fnrefs ctxt (CApBinary bop e1 e2) =
     expr_extract_fnrefs ctxt e1 UNION expr_extract_fnrefs ctxt e2) /\
  (expr_extract_fnrefs ctxt (Deref e) = expr_extract_fnrefs ctxt e) /\
  (expr_extract_fnrefs ctxt (Addr e) = expr_extract_fnrefs ctxt e) /\
  (expr_extract_fnrefs ctxt (MemAddr cid sfld) =
     if is_function_name ctxt (IDFld cid sfld) then {FnCall (IDFld cid sfld)}
     else {}) /\
  (expr_extract_fnrefs ctxt (Assign bopt e1 e2) =
     expr_extract_fnrefs ctxt e1 UNION expr_extract_fnrefs ctxt e2) /\
  (expr_extract_fnrefs ctxt (SVar e sfld) =
     expr_extract_fnrefs ctxt e UNION
     (let cname = @cname. expr_type (ctxt_typing ctxt) RValue e (Class cname)
      in
          if is_function_name ctxt (IDFld cname sfld) then
            {FnCall (IDFld cname sfld)}
          else {})) /\
  (expr_extract_fnrefs ctxt (FnApp e elist) =
     FOLDL (\a e. a UNION expr_extract_fnrefs ctxt e)
           (expr_extract_fnrefs ctxt e)
           elist) /\
  (expr_extract_fnrefs ctxt (CommaSep e1 e2) =
     expr_extract_fnrefs ctxt e1 UNION expr_extract_fnrefs ctxt e2) /\
  (expr_extract_fnrefs ctxt (Cast ty e) = expr_extract_fnrefs ctxt e) /\
  (expr_extract_fnrefs ctxt (PostInc e) = expr_extract_fnrefs ctxt e) /\
  (expr_extract_fnrefs ctxt (New ty NONE) =
     case strip_const ty of
        Class id -> {CallConstructor id []; CallDestructor id}
     || _ -> {}) /\
  (expr_extract_fnrefs ctxt (New ty (SOME elist)) =
     let tylist =
           @tylist. listRel (expr_type (ctxt_typing ctxt) RValue) elist tylist
     in
       FOLDL (\a e. a UNION expr_extract_fnrefs ctxt e)
             (case ty of
                 Class id -> {CallConstructor id tylist; CallDestructor id}
              || _ -> {})
             elist) /\
   (expr_extract_fnrefs ctxt _ = {})
`;

val (expr_extract_fnrefs_def, expr_extract_fnrefs_ind) = Defn.tprove(
  expr_extract_fnrefs_defn,
  WF_REL_TAC `^(last (TotalDefn.guessR expr_extract_fnrefs_defn))` THEN
  SRW_TAC [ARITH_ss][] THENL [
    Induct_on `elist` THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss) [] THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `elist` THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss) [] THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val alt_size_defn = Hol_defn "alt_size" `
  (alt_size (CLoop ee s) = eealt_size ee + alt_size s + 1n) /\
  (alt_size (CIf ee s1 s2) = eealt_size ee + alt_size s1 + alt_size s2 + 1) /\
  (alt_size (Standalone ee) = eealt_size ee + 1) /\
  (alt_size (Block b vdl stl) =
     FOLDL (\a vd. a + vdalt_size vd)
           (FOLDL (\a st. a + alt_size st) 0 stl + 1)
           vdl) /\
  (alt_size (Ret ee) = eealt_size ee + 1) /\
  (alt_size (Trap tt st) = alt_size st + 1) /\
  (alt_size (Throw (SOME ee)) = eealt_size ee + 1) /\
  (alt_size (Catch st handlers) =
     FOLDL (\a (e,s). a + alt_size s) (alt_size st + 1) handlers) /\
  (alt_size _ = 0)

     /\

  (eealt_size (NormE e se) = 0) /\
  (eealt_size (EStmt st c) = alt_size st + 1)

     /\

  (vdalt_size (VDec ty n) = 0) /\
  (vdalt_size (VDecInit ty n init) = initalt_size init + 1) /\
  (vdalt_size (VStrDec nm NONE) = 0) /\
  (vdalt_size (VStrDec nm (SOME ci)) = cinfoalt_size ci + 1) /\
  (vdalt_size _ = 0) /\

  (cealt_size (CFnDefn ret snm params NONE) = 0) /\
  (cealt_size (CFnDefn ret snm params (SOME body)) = 2 + alt_size body) /\
  (cealt_size (FldDecl str ty) = 0) /\
  (cealt_size (Constructor params meminits NONE) = 0) /\
  (cealt_size (Constructor params meminits (SOME body)) =
     2 + alt_size body) /\
  (cealt_size (Destructor NONE) = 0) /\
  (cealt_size (Destructor (SOME body)) = 1 + alt_size body)

     /\

  (cinfoalt_size ci = 1 + FOLDL (\a (ce,b,p). a + cealt_size ce) 0 ci.fields)

     /\

  (initalt_size (DirectInit0 _) = 0) /\
  (initalt_size (DirectInit ee) = eealt_size ee + 1) /\
  (initalt_size (CopyInit ee) = eealt_size ee + 1)
`;

val (alt_size_def, alt_size_ind) = Defn.tprove(
  alt_size_defn,
  WF_REL_TAC `^(last (TotalDefn.guessR alt_size_defn))` THEN
  SRW_TAC [ARITH_ss][] THENL [
    Induct_on `handlers` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss ++ DNF_ss) [] THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

    Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN Induct_on `l` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss ++ DNF_ss) [] THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

    Induct_on `vdl` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss ++ DNF_ss) [] THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

    Induct_on `stl` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss ++ DNF_ss) [] THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);
val _ = save_thm("alt_size_def", alt_size_def)
val _ = export_rewrites ["alt_size_def"]


val extract_fnrefs_defn = Hol_defn "extract_fnrefs" `
  (extract_fnrefs ctxt (CLoop ee s) =
     eexpr_extract_fnrefs ctxt ee UNION
     extract_fnrefs ctxt s) /\
  (extract_fnrefs ctxt (CIf ee s1 s2) =
     eexpr_extract_fnrefs ctxt ee UNION
     extract_fnrefs ctxt s1 UNION extract_fnrefs ctxt s2) /\
  (extract_fnrefs ctxt (Standalone ee) =
     eexpr_extract_fnrefs ctxt ee) /\
  (extract_fnrefs ctxt (Block b vdl stl) =
     let (dlcalls, ctxt') =
         FOLDL (\ (calls0, ctxt) vd.
                     let (calls, c') = vd_extract_fnrefs ctxt vd
                     in
                         (calls0 UNION calls, c'))
               ({}, ctxt)
               vdl
     in
         FOLDL (\a st. a UNION extract_fnrefs ctxt' st) dlcalls stl) /\
  (extract_fnrefs ctxt (Ret ee) = eexpr_extract_fnrefs ctxt ee) /\
  (extract_fnrefs ctxt (Trap tt st) = extract_fnrefs ctxt st) /\
  (extract_fnrefs ctxt (Throw NONE) = {}) /\
  (extract_fnrefs ctxt (Throw (SOME ee)) = eexpr_extract_fnrefs ctxt ee) /\
  (extract_fnrefs ctxt (Catch st handlers) =
     FOLDL (\a (e,s). a UNION extract_fnrefs ctxt s)
           (extract_fnrefs ctxt st)
           handlers) /\
  (extract_fnrefs ctxt _ = {})

     /\

  (eexpr_extract_fnrefs ctxt (NormE e se) = expr_extract_fnrefs ctxt e) /\
  (eexpr_extract_fnrefs ctxt (EStmt st c) = extract_fnrefs ctxt st)

     /\

  (vd_extract_fnrefs ctxt (VDec ty nm) =
     ((case strip_const ty of
          Class id -> {CallConstructor id []; CallDestructor id}
       || _ -> {}), extend_ctxt ty nm ctxt)) /\
  (vd_extract_fnrefs ctxt (VDecInit ty nm init) =
     let ctxt' = extend_ctxt ty nm ctxt in
     let (conarg_types, calls) = init_extract_fnrefs ty ctxt' init
     in
         ((case strip_const ty of
              Class id -> {CallConstructor id conarg_types;
                           CallDestructor id}
           || _ -> {}) UNION calls,
          ctxt')) /\
  (vd_extract_fnrefs ctxt (VStrDec nm ciopt) =
     let ctxt' = str_extend_ctxt nm ciopt ctxt in
     let calls = case ciopt of NONE -> {}
                            || SOME ci -> ci_extract_fnrefs ctxt ci
     in
         (calls, ctxt')) /\
  (vd_extract_fnrefs ctxt _ = ({}, ctxt))

     /\

  (ci_extract_fnrefs ctxt ci =
     FOLDL (\a (ce,b,p). a UNION centry_extract_fnrefs ctxt ce)
           {}
           ci.fields)

     /\

  (centry_extract_fnrefs ctxt (CFnDefn ty sfnm params NONE) = {}) /\
  (centry_extract_fnrefs ctxt (CFnDefn ty sfnm params (SOME st)) =
     let pdecs = MAP (\ (n,ty). VDec ty (Base n)) params
     in
         extract_fnrefs ctxt (Block T pdecs [st])) /\
  (centry_extract_fnrefs ctxt (FldDecl fldnm ty) = {}) /\
  (centry_extract_fnrefs ctxt (Constructor params meminits bodyopt) =
     FOLDL (\a (memid, aopt).
              case aopt of
                 NONE -> {}
              || SOME args -> FOLDL (\a e. a UNION
                                           expr_extract_fnrefs ctxt e)
                                    a
                                    args)
           (case bodyopt of
               NONE -> {}
            || SOME st ->
                 let pdecs = MAP (\ (n,ty). VDec ty (Base n)) params
                 in
                     extract_fnrefs ctxt (Block T pdecs [st]))
           meminits) /\
  (centry_extract_fnrefs ctxt (Destructor NONE) = {}) /\
  (centry_extract_fnrefs ctxt (Destructor (SOME st)) =
     extract_fnrefs ctxt st)

     /\

  (init_extract_fnrefs ty ctxt (DirectInit0 elist) =
     let tylist = (@tylist. listRel (expr_type (ctxt_typing ctxt) RValue)
                                    elist tylist)
     in
         (tylist,
          FOLDL (\a e. expr_extract_fnrefs ctxt e UNION a) {} elist)) /\
  (init_extract_fnrefs ty ctxt (CopyInit ee) =
     ([ty], eexpr_extract_fnrefs ctxt ee))
`;

val LT_FOLDL = prove(
  ``!elems f x acc. x:num < acc ==> x < FOLDL (\a e. a + f e) acc elems``,
  Induct THEN SRW_TAC [ARITH_ss][]);
val LT_FOLDL2 = prove(
  ``!elems f x acc. 0n < acc /\ MEM x elems ==>
                    f x < FOLDL (\a e. a + f e) acc elems``,
  Induct THEN SRW_TAC [ARITH_ss][] THEN SRW_TAC [ARITH_ss][LT_FOLDL]);
val LE_FOLDL1 = prove(
  ``!elems f x acc. x:num <= acc ==> x <= FOLDL (\a e. a + f e) acc elems``,
  Induct THEN SRW_TAC [ARITH_ss][]);
val LE_FOLDL2 = prove(
  ``!elems (f:'a->num) x acc.
        MEM x elems ==> f x <= FOLDL (\a e. a + f e) acc elems``,
  Induct THEN SRW_TAC [ARITH_ss][] THENL [
    SRW_TAC [ARITH_ss][LE_FOLDL1],
    RES_TAC THEN SRW_TAC [][]
  ]);


val UNCURRY_alt = prove(``UNCURRY f = \p. f (FST p) (SND p)``,
                        SRW_TAC [][FUN_EQ_THM, pairTheory.UNCURRY])
val (extract_fnrefs_def, extract_fnrefs_ind) = Defn.tprove(
  extract_fnrefs_defn,
  WF_REL_TAC
    `measure (\sum.
       case sum of
          INL (c,st) -> alt_size st
       || INR (INL (c, ee)) -> eealt_size ee
       || INR (INR (INL (c, vd))) -> vdalt_size vd
       || INR (INR (INR (INL (c, ci)))) -> cinfoalt_size ci
       || INR (INR (INR (INR (INL (c, ce))))) -> cealt_size ce
       || INR (INR (INR (INR (INR (ty, c, init))))) -> initalt_size init)` THEN
  REPEAT CONJ_TAC THEN
  SRW_TAC [ARITH_ss][] THENL [
    Q.SPEC_TAC (`alt_size st`,`m:num`) THEN
    Induct_on `handlers` THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss) [pairTheory.FORALL_PROD] THEN
    REPEAT STRIP_TAC THENL [
      POP_ASSUM (K ALL_TAC) THEN
      Q_TAC SUFF_TAC
            `!n:num m f. n < m ==> n < FOLDL (\a p. a + f p) m handlers`
            THEN1 (DISCH_THEN
                     (Q.SPECL_THEN [`alt_size s`, `m + (alt_size s + 1)`,
                                    `\ (e,s). alt_size s`] MP_TAC) THEN
                   SRW_TAC [ARITH_ss][] THEN
                   FULL_SIMP_TAC (srw_ss()) [UNCURRY_alt]) THEN
      Induct_on `handlers` THEN SRW_TAC [ARITH_ss][],
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `m + alt_size p_2` MP_TAC) THEN
      SRW_TAC [ARITH_ss][]
    ],

    Q.MATCH_ABBREV_TAC `LHS < alt_size s + 2` THEN
    Q_TAC SUFF_TAC `LHS = alt_size s + 1` THEN1 DECIDE_TAC THEN
    Q.UNABBREV_ALL_TAC THEN Induct_on `params` THEN SRW_TAC [][] THEN
    Cases_on `h` THEN SRW_TAC [][],

    MATCH_MP_TAC LT_FOLDL THEN
    Q_TAC SUFF_TAC `alt_size st <= FOLDL (\a st. a + alt_size st) 0 stl`
          THEN1 DECIDE_TAC THEN
    MATCH_MP_TAC LE_FOLDL2 THEN SRW_TAC [][],

    Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    MATCH_MP_TAC (DECIDE ``!x y:num. x <= y ==> x < y + 1``) THEN
    Q.ISPECL_THEN [`l`, `\ (ce,b:bool,p:protection). cealt_size ce`] MP_TAC
                  LE_FOLDL2 THEN
    SRW_TAC [][UNCURRY_alt] THEN RES_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [],

    MATCH_MP_TAC LT_FOLDL2 THEN SRW_TAC [ARITH_ss][],

    Q.MATCH_ABBREV_TAC `LHS < alt_size s + 2` THEN
    Q_TAC SUFF_TAC `LHS = alt_size s + 1` THEN1 DECIDE_TAC THEN
    Q.UNABBREV_ALL_TAC THEN Induct_on `params` THEN SRW_TAC [][] THEN
    Cases_on `h` THEN SRW_TAC [][],

    Q.MATCH_ABBREV_TAC `lhs:num < FOLDL f acc handlers` THEN
    `f = (\a p. a + (\ (e,s). alt_size s) p)`
       by SRW_TAC [][FUN_EQ_THM, UNCURRY_alt, Abbr`f`] THEN
    SRW_TAC [][LT_FOLDL, Abbr`lhs`, Abbr`acc`]
  ]);
val _ = save_thm("extract_fnrefs_def", extract_fnrefs_def)
val _ = export_rewrites ["extract_fnrefs_def"]

val edec_ctxt_def = Define`
  (edec_ctxt ctxt (FnDefn ty id params body) =
     let funty = Function ty (MAP SND params)
     in
       case id of
          IDTempCall tid args ->
             ctxt with vars updated_by (\fm. fm |+ (id, funty))
       || IDConstant tname ->
             ctxt with vars updated_by (\fm. fm |+ (id, funty))
       || id -> ctxt) /\
  (edec_ctxt ctxt (ClassConDef nm params meminits bod) = ctxt) /\
  (edec_ctxt ctxt (ClassDestDef nm body) = ctxt) /\
  (edec_ctxt ctxt (Decl (VDec ty nm)) =
      ctxt with vars updated_by (\fm. fm |+ (nm,ty))) /\
  (edec_ctxt ctxt (Decl (VDecInit ty nm init)) =
      ctxt with vars updated_by (\fm. fm |+ (nm,ty))) /\
  (edec_ctxt ctxt (Decl (VStrDec nm NONE)) = ctxt) /\
  (edec_ctxt ctxt (Decl (VStrDec nm (SOME ci))) =
      ctxt with classes updated_by (\fm. fm |+ (nm, ci)))
`;




(* create a context or name environment  for scanning a function body or
   expression. The nm is the name of the function, which is used to determine
   the type of "this" *)
val mk_initial_ctxt_def = Define`
  mk_initial_ctxt Templates Residuals nm params =
    let alldecs = SET_TO_LIST Templates ++ REVERSE Residuals in
    let ctxt0 = FOLDL edec_ctxt empty_ctxt alldecs in
    let ctxt1 = FOLDL edec_ctxt ctxt0
                      (MAP (\ (n, ty). Decl (VDec ty (Base n))) params) in
    let thisty =
          case nm of
             IDConstant tn -> NONE
          || IDTempCall tid targs -> NONE
          || IDVar s -> NONE (* impossible *)
          || IDFld cnm sfld -> SOME (Class cnm)
    in
       ctxt1 with thisinfo := thisty
`;

val already_present_def = Define`
  (already_present residuals (FnCall id) =
      ?ty params body. MEM (FnDefn ty id params body) residuals) /\
  (already_present residuals (CallConstructor id ptypes) =
      ?params meminits body.
         MEM (ClassConDef id params meminits body) residuals /\
         (MAP SND params = ptypes)) /\
  (already_present residuals (CallDestructor id) =
      ?body. MEM (ClassDestDef id body) residuals) /\
  (already_present residuals (StaticVar cnm fldname) =
      ?ty init. MEM (Decl (VDecInit ty (IDFld cnm (SFName fldname)) init))
                    residuals)
`;

(* a comparison function for external declarations, lifting the order on
   identifiers *)
val decl_comp_def = Define`
  (decl_comp (FnDefn _ nm1 _ _) (FnDefn _ nm2 _ _) =
     ?sub. cppID_inst sub nm1 = SOME nm2) /\
  (decl_comp (Decl d1) (Decl d2) = ?sub. vdec_inst sub d1 = SOME d2) /\
  (decl_comp (ClassConDef nm1 _ _ _) (ClassConDef nm2 _ _ _) =
     ?sub. cppID_inst sub nm1 = SOME nm2) /\
  (decl_comp (ClassDestDef nm1 _) (ClassDestDef nm2 _) =
     ?sub. cppID_inst sub nm1 = SOME nm2) /\
  (decl_comp _ _ = F)
`;

val setmax_def = Define`
  setmax order s = if ?e. e IN s /\ (!e'. e' IN s ==> order e' e) then
                     SOME (@e. e IN s /\ !e'. e' IN s ==> order e' e)
                   else NONE
`;

val setmax_unique = store_thm(
  "setmax_unique",
  ``(!e f. order e f /\ order f e ==> (e = f)) /\
    e IN s /\ (!e'. e' IN s ==> order e' e) ==>
    (setmax order s = SOME e)``,
  SRW_TAC [][setmax_def] THENL [
    SELECT_ELIM_TAC THEN CONJ_TAC THEN METIS_TAC [],
    METIS_TAC []
  ]);


(* "returns" the uninstantiated decl for the given function identifier *)
val best_function_match_def = Define`
  best_function_match Temps id sub (id', decl) =
    (cppID_inst sub id' = SOME id) /\
    ?retty ptys.
      (Decl (VDec (Function retty ptys) id) = decl) /\
      decl IN Temps /\
      !retty' ptys' id2.
         Decl (VDec (Function retty' ptys') id2) IN Temps ==>
         ?sub'. cppID_inst sub' id2 = SOME id'
`

val fndefn_by_name_def = Define`
  fndefn_by_name Templates fnm =
    THEOPT d. ?r p b. (d = FnDefn r fnm p b) /\ d IN Templates
`;

val find_defn_def = Define`
  (find_defn Templates (FnCall id) =
      case id of
         IDFld cnm sfld ->
          (let (sub, cnm', ci) =
              (@(sub,cnm',ci). best_class_match Templates cnm sub (cnm', ci)) in
           let (sfsub,sfld',decl0) =
               (@(sfsub,sfld',decl0). best_function_match
                                         Templates
                                         (IDFld cnm' sfld)
                                         sfsub
                                         (IDFld cnm' sfld', decl0)) in
           let best_declared_name = IDFld cnm' sfld'
           in
             OPTION_MAP (THE o extdecl_inst (inst_comp sfsub sub))
                        (fndefn_by_name Templates best_declared_name))
      || IDVar s -> NONE (* can't happen *)
      || IDConstant tn -> NONE (* this is a reference to a non-template
                                  function that doesn't have a definition in
                                  Residuals.  It's not going to have a
                                  Templates definition (TODO no implicit use of
                                  template functions TODO) *)
      || IDTempCall tid targs ->
           let (sub,id',decl0) =
               @(sub,id',decl0). best_function_match Templates
                                   id
                                   sub
                                   (id', decl0)
           in
             OPTION_MAP (THE o extdecl_inst sub)
                        (fndefn_by_name Templates id')) /\
  (find_defn Templates (CallConstructor cnm ptys) =
      let (sub,cnm',ci) =
         @(sub,cnm',ci). best_class_match Templates cnm sub (cnm',ci)
      in
         OPTION_MAP (THE o extdecl_inst sub)
                    (THEOPT d. ?params meminits body.
                        (d = ClassConDef cnm' params meminits body) /\
                        d IN Templates /\
                        (MAP (THE o type_inst sub o SND) params = ptys))) /\
  (find_defn Templates (CallDestructor cnm) =
     let (sub,cnm',ci) =
         @(sub,cnm',ci). best_class_match Templates cnm sub (cnm',ci)
     in
         OPTION_MAP (THE o extdecl_inst sub)
                    (THEOPT d. ?body.
                       (d = ClassDestDef cnm' body) /\ d IN Templates)) /\
  (find_defn Templates (StaticVar cnm s) =
     let (sub,cnm',ci) =
         @(sub,cnm',ci). best_class_match Templates cnm sub (cnm',ci)
     in
         OPTION_MAP (THE o extdecl_inst sub)
                    (THEOPT d. ?ty init.
                       (d = Decl (VDecInit ty (IDFld cnm' (SFName s)) init)) /\
                       d IN Templates))
`

(* given a ground external declaration that we're seeing for the first time,
   extract any template types, and put them onto the work list, ahead of the
   original external declaration attached to 1 (rather than zero), to signify
   that this step has been performed *)
val insert_type_requirements_def = Define`
  insert_type_requirements Templates Residuals Needs edecs edec =
    let tys = extdecl_ttypes edec in
    let cmp id1 id2 = CPP_ID_size id1 <= CPP_ID_size id2 in
    let tyl = QSORT cmp
                (SET_TO_LIST (IMAGE (\ (tid,targs).
                                       IDTempCall tid targs)
                                    tys))
    in
      Running(Templates,
              Residuals,
              Needs,
              MAP (\id. (Decl (VStrDec id NONE), 0n)) tyl ++
                  [(edec,1)] ++ edecs)
`;

(* first thing to do on seeing a function definition (could be member function
   or not), is to check if it's at a ground type, or a template definition.
   If the latter, just put it into the Templates field, and check to see
   whether or not it might be needed.

   Otherwise, scan it for ground template types, and put these onto
   the work-list.  *)

val fndefn0_def = Define`
  fndefn0 Templates Residuals Needs edecs edec =
    let checkid = case edec of
                     FnDefn ty nm ps b -> SOME nm
                  || ClassConDef nm params memints b -> SOME nm
                  || ClassDestDef nm b -> SOME nm
                  || Decl d -> NONE
    in
      case checkid of
        SOME nm ->
          if cppidfrees nm = {} then
            if MEM edec Residuals then
              Running (Templates, Residuals, Needs, edecs)
            else
              insert_type_requirements Templates Residuals Needs edecs edec
          else (* here we could also check that edec is not a partial
                  specialisation occurring before the general pattern is
                  given *)
            (let newTemps = edec INSERT Templates in
             let (new_instances, newNeeds) =
                  optimage (find_defn newTemps) Needs
             in
               Running (newTemps,
                        Residuals,
                        newNeeds,
                        MAP (\e. (e,0n)) (SET_TO_LIST new_instances) ++ edecs))
      || NONE -> Failed
`;

(* defining/initialising a variable is just like defining a function *)
val var_init0_def = Define`
  var_init0 Templates Residuals Needs edecs (ty,nm,init) =
    let edec = Decl (VDecInit ty nm init)
    in
      if cppidfrees nm = {} then
        if MEM edec Residuals then
          Running(Templates, Residuals, Needs, edecs)
        else
          insert_type_requirements Templates Residuals Needs edecs edec
      else (* is a template initialisation of a static data member, and might
              be needed *)
        let newTemps = edec INSERT Templates in
        let (new_instances, newNeeds) = optimage (find_defn newTemps) Needs
        in
          Running(newTemps, Residuals, newNeeds,
                  MAP (\e. (e,0n)) (SET_TO_LIST new_instances) ++ edecs)
`

(* strip function definitions out of a cinfo *)
val strip_centry_defs_def = Define`
  (strip_centry_defs cnm (CFnDefn ty snm params (SOME body)) =
     (CFnDefn ty snm params NONE, [FnDefn ty (IDFld cnm snm) params body])) /\
  (strip_centry_defs cnm (Constructor params meminits (SOME body)) =
     (Constructor params [] NONE, [ClassConDef cnm params meminits body])) /\
  (strip_centry_defs cnm (Destructor (SOME body)) =
     (Destructor NONE, [ClassDestDef cnm body])) /\
  (strip_centry_defs cnm x = (x, []))
`;
val strip_cinfo_defs_def = Define`
  strip_cinfo_defs cnm ci =
    let (newfields, extdefs) =
        FOLDL (\ (flds, defs) (e,b,p).
               let (fld, edefs) = strip_centry_defs cnm e
               in
                 (flds ++ [(fld,b,p)], defs ++ edefs))
              ([], [])
              ci.fields
    in
      (ci with fields := newfields, extdefs)
`

(* declaring/defining a class type - phase 0 *)
val str_init0_def = Define`
  (str_init0 Templates Residuals Needs edecs (cnm, NONE) =
     let edec = Decl (VStrDec cnm NONE)
     in
       (* declaring a type, which may be requesting an instantiation if the
          type-name is ground and a template form *)
       if cppidfrees cnm = {} then
         if MEM edec Residuals then
           Running(Templates, Residuals, Needs, edecs)
         else
           (* need to look this type up, and see if there is a generalised
              cinfo for it that we can instantiate. *)
           case cnm of
              IDVar v -> Failed (* can't happen *)
           || IDConstant tn -> (* it's a forward declaration of a normal
                                  class *)
                Running(Templates, edec :: Residuals, Needs, edecs)
           || IDFld id sfld -> Failed (* can't happen *)
           || IDTempCall tid targs ->
                let (sub,cnm',ci) =
                  @(sub,cnm',ci). best_class_match Templates cnm sub (cnm',ci)
                in
                  case ci of
                     NONE -> Failed
                  || SOME cinfo ->
                      (* found something to instantiate.  Don't want to
                         have member functions defined here though, so these
                         get stripped out *)
                      let cinfo' = THE (cinfo_inst sub cinfo) in
                      let cinfo'' = FST (strip_cinfo_defs cnm' cinfo')
                      in
                          insert_type_requirements
                            Templates Residuals
                            Needs edecs
                            (Decl (VStrDec cnm (SOME cinfo'')))
       else (* forward declaration of a template type *)
         Running (edec INSERT Templates, Residuals, Needs, edecs)) /\
  (str_init0 Templates Residuals Needs edecs (cnm, SOME cinfo) =
     let edec = Decl (VStrDec cnm (SOME cinfo))
     in
       if cppidfrees cnm = {} then
         if MEM edec Residuals then
           Running (Templates, Residuals, Needs, edecs)
         else
           let cinfo' = FST (strip_cinfo_defs cnm cinfo)
           in
             insert_type_requirements Templates Residuals Needs edecs
                                      (Decl(VStrDec cnm (SOME cinfo')))
       else
         let (cinfo', newdefs) = strip_cinfo_defs cnm cinfo in
         let new_edec = Decl (VStrDec cnm (SOME cinfo')) in
         let new_edecs = new_edec INSERT LIST_TO_SET newdefs
         in
           Running (new_edecs UNION Templates, Residuals, Needs, edecs))
`

(* if we get this far, we can be sure that all the ground type declarations
   are in scope, and that the function we're looking at is itself not a
   template.  Now we have to see what functions might also be required.
   When we extract the functions,
     1. we have to check if they're already in Residuals.
     2. If they are not, we can check if they're in Needs.  If so
        leave it, and continue.
     3. Otherwise, we can look for a definition in Templates.
     4. There should be a declaration there, but there may not be a
        definition.
     5. If there is a definition, we pull it out, instantiate it, and
        put that onto the list of functions to check.
     6. Otherwise, we put the function into the Needs list and continue.
*)
val fndefn1_def = Define`
  fndefn1 Templates Residuals Needs edecs (FnDefn ty nm params body) =
    let edec = FnDefn ty nm params body in
    let ctxt = mk_initial_ctxt Templates Residuals nm params in
    let fnrefs = extract_fnrefs ctxt body in
    let newfns = fnrefs DIFF (already_present Residuals UNION Needs) in
    let (NewlyInstantiated, NewNeeds) = optimage (find_defn Templates) newfns
    in
      Running(Templates, edec :: Residuals, NewNeeds UNION Needs,
              MAP (\e. (e,0n)) (SET_TO_LIST NewlyInstantiated) ++
              edecs)
`;

(* when a variable initialisation has had its referred-to types dealt with,
   we have to look at the initialising expression, which may involve
   references to template things *)
val var_init1_def = Define`
  var_init1 Templates Residuals Needs edecs (ty,nm,init) =
    let vd = VDecInit ty nm init in
    let edec = Decl vd in
    let ctxt = mk_initial_ctxt Templates Residuals (IDConstant ARB) [] in
    let (fnrefs, ctxt') = vd_extract_fnrefs ctxt vd in
    let newfns = fnrefs DIFF (already_present Residuals UNION Needs) in
    let (NewlyInstantiated, NewNeeds) = optimage (find_defn Templates) newfns
    in
      Running (Templates, edec :: Residuals, NewNeeds UNION Needs,
               MAP (\e. (e,0n)) (SET_TO_LIST NewlyInstantiated) ++
               edecs)
`

(* the only thing that needs to be resolved after a struct's type dependencies
   have been dealt with is the struct's static data members.  *)
val str_init1_def = Define`
  str_init1 Templates Residuals Needs edecs (cnm, cinfo_opt) =
    let (sub,cnm',ci) =
        @(sub,cnm',ci). best_class_match Templates cnm sub (cnm',ci) in
    let cinfo = THE (cinfo_inst sub (THE ci)) in
    let stat_flds =
        mapPartial
          ( \(ce,b,p). if b then
                         case ce of
                            FldDecl nm ty ->
                                   if function_type ty then NONE
                                   else SOME (StaticVar cnm nm)
                         || _ -> NONE
                       else NONE)
          cinfo.fields in
    let (NewlyInstantiated, NewNeeds) = optimage (find_defn Templates)
                                                 (LIST_TO_SET stat_flds)
    in
      Running(Templates, Residuals, Needs UNION NewNeeds,
              MAP (\e. (e,0n)) (SET_TO_LIST NewlyInstantiated) ++ edecs)
`


val decl_instantiate_def = Define`
  decl_instantiate Templates Residuals Needs edecs d m =
    case d of
       VDec ty nm ->
          if m = 0 then
            if cppidfrees nm = {} then
              insert_type_requirements Templates Residuals Needs edecs (Decl d)
            else
              (* is a declaration of a template function *)
              Running(Decl d INSERT Templates, Residuals, Needs, edecs)
          else
            Running(Templates, Decl d :: Residuals, Needs, edecs)
    || VDecInit ty nm init ->
          if m = 0n then var_init0 Templates Residuals Needs edecs (ty,nm,init)
          else var_init1 Templates Residuals Needs edecs (ty,nm,init)
    || VStrDec cnm cinfo ->
          if m = 0 then str_init0 Templates Residuals Needs edecs (cnm, cinfo)
          else str_init1 Templates Residuals Needs edecs (cnm, cinfo)
    || _ -> Failed
`


val prog_inst_def = Define`
  prog_inst (Templates, Residuals, Needs, extdecllist) =
    case extdecllist of
       [] -> Done (Residuals, Needs)
    || ((edec,m) :: edecs) ->
          (case edec of
              Decl d -> decl_instantiate Templates Residuals Needs edecs d m
           || _ ->
                if m = 0 then fndefn0 Templates Residuals Needs edecs edec
                else fndefn1 Templates Residuals Needs edecs edec)
`

val program_instantiate_def = Define`
  program_instantiate edecs =
    WHILE (\s. case s of Running x -> T || y -> F)
          (\s. case s of Running x -> prog_inst x)
          (Running({}, [], {}, MAP (\e. (e,0)) edecs))
`;


*)

val _ = export_theory();



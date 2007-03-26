(* Operations on templates *)

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

val _ = new_theory "templates"


val _ = Hol_datatype`cppid_inst_result = TypeResult of CPP_Type
                                       | IDResult of CPP_ID
                                       | BadResult
`;

val _ = Hol_datatype`inst_record = <| typemap : string -> CPP_Type ;
                                      tempmap : string -> TemplateID ;
                                      valmap : string -> TemplateValueArg |>`

val empty_inst_def = Define`
  empty_inst = <| typemap := TypeID o IDVar;
                  tempmap := TemplateVar;
                  valmap := TVAVar |>
`;


val tempid_inst_def = Define`
  (tempid_inst sigma (TemplateConstant tn) = TemplateConstant tn) /\
  (tempid_inst sigma (TemplateVar s) = sigma.tempmap s)
`
val _ = export_rewrites ["tempid_inst_def"]

val NIL_tempid_inst = store_thm(
  "NIL_tempid_inst",
  ``!tid. tempid_inst empty_inst tid = tid``,
  Induct THEN SRW_TAC [][empty_inst_def]);
val _ = export_rewrites ["NIL_tempid_inst"]

(* instantiate a type with template arguments *)
val type_inst_defn = Hol_defn "type_inst" `
  (type_inst sigma (TypeID cid) =
     case cppid_inst sigma cid of
        IDResult cid' -> SOME (TypeID cid')
     || TypeResult ty -> SOME ty
     || BadResult -> NONE) /\
  (type_inst sigma (Ptr ty) = OPTION_MAP Ptr (type_inst sigma ty)) /\
  (type_inst sigma (MPtr nm ty) =
     let tyopt = type_inst sigma ty
     in
       case cppid_inst sigma nm of
          IDResult cid' -> OPTION_MAP (MPtr cid') tyopt
       || TypeResult (Class cid') ->
              OPTION_MAP (MPtr cid') tyopt
       || TypeResult (TypeID cid') -> OPTION_MAP (MPtr cid') tyopt
       || id1 -> NONE) /\
  (type_inst sigma (Ref ty) = OPTION_MAP Ref (type_inst sigma ty)) /\
  (type_inst sigma (Array ty n) =
     OPTION_MAP (\ty. Array ty n) (type_inst sigma ty)) /\
  (type_inst sigma (Function ty tylist) =
     case type_inst sigma ty of
        NONE -> NONE
     || SOME ty' -> OPTION_MAP (Function ty')
                               (olmap (type_inst sigma) tylist)) /\
  (type_inst sigma (Const ty) = OPTION_MAP Const (type_inst sigma ty)) /\
  (type_inst sigma (Class cid) =
      case cppid_inst sigma cid of
         IDResult cid' -> SOME (Class cid')
      || TypeResult ty -> NONE
      || BadResult -> NONE) /\
  (type_inst sigma ty = SOME ty)

    /\

  (cppid_inst sigma (IDVar s) =
     case sigma.typemap s of
        TypeID id -> IDResult id
     || Class id -> IDResult id
     || ty -> TypeResult ty) /\
  (cppid_inst sigma (IDFld cid fld) =
     case cppid_inst sigma cid of
        IDResult cid' ->
           (case sfld_inst sigma fld of
               NONE -> BadResult
            || SOME fld' -> IDResult (IDFld cid' fld'))
     || id1 -> BadResult) /\
  (cppid_inst sigma (IDTempCall tempid tempargs) =
     case olmap (temparg_inst sigma) tempargs of
        NONE -> BadResult
     || SOME tempargs' ->
          IDResult (IDTempCall (tempid_inst sigma tempid) tempargs')) /\
  (cppid_inst sigma (IDConstant tnm) = IDResult (IDConstant tnm))

    /\

  (temparg_inst sigma (TType ty) = OPTION_MAP TType (type_inst sigma ty)) /\
  (temparg_inst sigma (TTemp tid) = SOME (TTemp (tempid_inst sigma tid))) /\
  (temparg_inst sigma (TVal tva) =
      OPTION_MAP TVal (temp_valarg_inst sigma tva))

    /\

  (temp_valarg_inst sigma (TNum i) = SOME (TNum i)) /\
  (temp_valarg_inst sigma (TObj id) =
      case cppid_inst sigma id of
         IDResult id' -> SOME (TObj id')
      || id1 -> NONE) /\
  (temp_valarg_inst sigma (TMPtr id ty) =
      case cppid_inst sigma id of
         IDResult id' -> OPTION_MAP (TMPtr id') (type_inst sigma ty)
      || id1 -> NONE) /\
  (temp_valarg_inst sigma (TVAVar s) = SOME (sigma.valmap s))

    /\

  (sfld_inst sigma (SFTempCall s targs) =
      OPTION_MAP (SFTempCall s) (olmap (temparg_inst sigma) targs)) /\
  (sfld_inst sigma (SFName s) = SOME (SFName s))
`

val (type_inst_def, type_inst_ind) = Defn.tprove(type_inst_defn,
  WF_REL_TAC
  `measure
     (\a. case a of
             INL (_, ty) -> CPP_Type_size ty
          || INR (INL (_, id)) -> CPP_ID_size id
          || INR (INR (INL (_, targ))) -> TemplateArg_size targ
          || INR (INR (INR (INL (_, tva)))) ->
               TemplateValueArg_size tva
          || INR (INR (INR (INR (_, sfld)))) -> StaticField_size sfld)`
     THEN
  SRW_TAC [ARITH_ss][] THENL [
    Induct_on `tempargs` THEN SRW_TAC [][] THEN
    SRW_TAC [ARITH_ss][] THEN RES_TAC THEN DECIDE_TAC,
    Induct_on `tylist` THEN SRW_TAC [][] THEN
    SRW_TAC [ARITH_ss][] THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `targs` THEN SRW_TAC [][] THEN
    SRW_TAC [ARITH_ss][] THEN RES_TAC THEN DECIDE_TAC
  ]);

val _ = save_thm("type_inst_def", type_inst_def)
val _ = save_thm("type_inst_ind", type_inst_ind)
val _ = export_rewrites ["type_inst_def"]

val type_match_def = Define`
  type_match ty1 ty2 = ?s. type_inst s ty1 = SOME ty2
`;

val _ = overload_on ("<=", ``type_match``);

val type_inst_empty = store_thm(
  "type_inst_empty",
  ``(!ty. type_inst empty_inst ty = SOME ty) /\
    (!id. cppid_inst empty_inst id = IDResult id) /\
    (!ta. temparg_inst empty_inst ta = SOME ta) /\
    (!tva. temp_valarg_inst empty_inst tva = SOME tva) /\
    (!sfld. sfld_inst empty_inst sfld = SOME sfld)``,
  Q_TAC SUFF_TAC
   `(!s ty. (s = empty_inst) ==> (type_inst s ty = SOME ty)) /\
    (!s id. (s = empty_inst) ==> (cppid_inst s id = IDResult id)) /\
    (!s ta. (s = empty_inst) ==> (temparg_inst s ta = SOME ta)) /\
    (!s tva. (s = empty_inst) ==> (temp_valarg_inst s tva = SOME tva)) /\
    (!s sfld. (s = empty_inst) ==> (sfld_inst s sfld = SOME sfld))`
   THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC type_inst_ind THEN
  SRW_TAC [][] THEN SRW_TAC [][] THENL [
    RES_TAC THEN Induct_on `tylist` THEN SRW_TAC [][],
    SRW_TAC [][empty_inst_def],
    `olmap (\a. temparg_inst empty_inst a) tempargs = SOME tempargs`
       by (Induct_on `tempargs` THEN SRW_TAC [][empty_inst_def]) THEN
    SRW_TAC [][],
    SRW_TAC [][empty_inst_def],
    SRW_TAC [ETA_ss] [] THEN Induct_on `targs` THEN SRW_TAC [][]
  ]);

val type_match_refl = store_thm(
  "type_match_refl",
  ``!ty:CPP_Type. ty <= ty``,
  SIMP_TAC (srw_ss()) [type_match_def] THEN
  METIS_TAC [type_inst_empty]);

val inst_comp_def = Define`
  inst_comp i2 i1 = <| typemap := THE o type_inst i2 o i1.typemap ;
                       tempmap := tempid_inst i2 o i1.tempmap ;
                       valmap  := THE o temp_valarg_inst i2 o i1.valmap |>
`;

val tempid_inst_comp = store_thm(
  "tempid_inst_comp",
  ``tempid_inst (inst_comp s2 s1) tid = tempid_inst s2 (tempid_inst s1 tid)``,
  Cases_on `tid` THEN SRW_TAC [][inst_comp_def]);
val _ = export_rewrites ["tempid_inst_comp"]

val inst_comp_thm = store_thm(
  "inst_comp_thm",
  ``(!id1 s1 s2.
       (!id2 id3. (cppid_inst s1 id1 = IDResult id2) /\
                  (cppid_inst s2 id2 = IDResult id3) ==>
                  (cppid_inst (inst_comp s2 s1) id1 = IDResult id3))
(*       (!ty.  (cppid_inst s1 id1 = TypeResult ty) ==>
              (cppid_inst (inst_comp s2 s1) id1 =
                 case type_inst s2 ty of
                    NONE -> BadResult
                 || SOME ty' -> TypeResult ty')) *)) /\
    (!sfld1 sfld2 s1 s2.
        (sfld_inst s1 sfld1 = SOME sfld2) ==>
        (sfld_inst (inst_comp s2 s1) sfld1 = sfld_inst s2 sfld2)) /\
    (!ta1 ta2 s1 s2.
        (temparg_inst s1 ta1 = SOME ta2) ==>
        (temparg_inst (inst_comp s2 s1) ta1 = temparg_inst s2 ta2)) /\
    (!tva1 tva2 s1 s2.
        (temp_valarg_inst s1 tva1 = SOME tva2) ==>
        (temp_valarg_inst (inst_comp s2 s1) tva1 =
           temp_valarg_inst s2 tva2)) /\
    (!ty1 ty2 s1 s2.
        (type_inst s1 ty1 = SOME ty2) ==>
        (type_inst (inst_comp s2 s1) ty1 = type_inst s2 ty2)) /\
    (!tal1 tal2 s1 s2.
        (olmap (temparg_inst s1) tal1 = SOME tal2) ==>
        (olmap (temparg_inst (inst_comp s2 s1)) tal1 =
           olmap (temparg_inst s2) tal2)) /\
    (!tyl1 tyl2 s1 s2.
        (olmap (type_inst s1) tyl1 = SOME tyl2) ==>
        (olmap (type_inst (inst_comp s2 s1)) tyl1 =
           olmap (type_inst s2) tyl2))``,
  Induct THEN SRW_TAC [][] THENL [
    Cases_on `s1.typemap s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][inst_comp_def],

    Cases_on `cppid_inst s1 id1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `sfld_inst s1 sfld1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `cppid_inst s2 C'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `sfld_inst s2 x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN
    `cppid_inst (inst_comp s2 s1) id1 = IDResult C''` by SRW_TAC [][] THEN
    SRW_TAC [][] THEN
    `sfld_inst (inst_comp s2 s1) sfld1 = sfld_inst s2 x` by SRW_TAC [][] THEN
    SRW_TAC [][],

    Cases_on `olmap (\a. temparg_inst s1 a) tal1` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THEN RES_TAC THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `olmap (\a. temparg_inst s2 a) x` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THEN
    SRW_TAC [][],

    FULL_SIMP_TAC (srw_ss()) [],

    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THEN RES_TAC THEN
    SRW_TAC [][],

    SRW_TAC [][],

    RES_TAC THEN SRW_TAC [][],

    SRW_TAC [][],

    RES_TAC THEN SRW_TAC [][],

    SRW_TAC [][],

    Cases_on `cppid_inst s1 id1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
    SRW_TAC [][] THEN SRW_TAC [][inst_comp_def]



(* this would be a nice SANITY theorem, but it's hard to prove, because
   it's hard to come up with the appropriate induction hypothesis.  *)
(*
val type_match_trans = store_thm(
  "type_match_trans",
  ``!(ty1:CPP_Type) ty2 ty3. ty1 <= ty2 /\ ty2 <= ty3 ==> ty1 <= ty3``,
  SRW_TAC [][type_match_def] THEN Q.EXISTS_TAC `inst_comp s' s` THEN
*)


(* instantiate an expression *)
val expr_inst_def = Define`
  (expr_inst sigma (Cnum n) = Cnum n) /\
  (expr_inst sigma (Cchar n) = Cchar n) /\
  (expr_inst sigma (Cnullptr ty) = Cnullptr (type_inst sigma ty)) /\
  (expr_inst sigma This = This) /\
  (expr_inst sigma (Var id) =
     case id of
        IDConstant (F,[],s) ->
           (case FINDL (\ (p,a). p = TVal (TVAVar s)) sigma of
               NONE -> Var id
            || SOME (p, a) ->
                 (case a of
                     TVal (TNum i) -> Cnum i
                  || TVal (TObj id') -> Var id'
                  || TVal (TMPtr cid ty) ->
                        (case cid of
                            IDFld cnm fldname -> MemAddr cnm fldname)))
     || x -> Var id) /\
  (expr_inst sigma (COr e1 e2) =
     COr (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (CAnd e1 e2) =
     CAnd (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (CCond e1 e2 e3) =
     CCond (expr_inst sigma e1) (expr_inst sigma e2) (expr_inst sigma e3)) /\
  (expr_inst sigma (CApBinary cbop e1 e2) =
     CApBinary cbop (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (CApUnary cuop e) = CApUnary cuop (expr_inst sigma e)) /\
  (expr_inst sigma (Addr e) = Addr (expr_inst sigma e)) /\
  (expr_inst sigma (Deref e) = Deref (expr_inst sigma e)) /\
  (expr_inst sigma (MemAddr cid fld) =
     MemAddr (cppid_inst sigma cid) (sfld_inst sigma fld)) /\
  (expr_inst sigma (Assign bopopt e1 e2) =
     Assign bopopt (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (SVar e fld) = SVar (expr_inst sigma e)
                                       (sfld_inst sigma fld)) /\
  (expr_inst sigma (FnApp e args) =
     FnApp (expr_inst sigma e) (exprl_inst sigma args)) /\
  (expr_inst sigma (CommaSep e1 e2) =
     CommaSep (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (Cast ty e) =
     Cast (type_inst sigma ty) (expr_inst sigma e)) /\
  (expr_inst sigma (PostInc e) = PostInc (expr_inst sigma e)) /\
  (expr_inst sigma (New ty args_opt) =
     New (type_inst sigma ty) (exprlop_inst sigma args_opt)) /\
  (expr_inst sigma (CAndOr_sqpt e) = CAndOr_sqpt (expr_inst sigma e)) /\
  (expr_inst sigma (FnApp_sqpt e args) =
     FnApp_sqpt (expr_inst sigma e) (exprl_inst sigma args)) /\
  (expr_inst sigma (LVal ad ty nms) =
     LVal ad (type_inst sigma ty) (MAP (cppid_inst sigma) nms)) /\
  (expr_inst sigma (FVal fnid ty eopt) =
     FVal fnid (type_inst sigma ty) (expropt_inst sigma eopt)) /\
  (expr_inst sigma (ConstructorFVal b1 b2 ad nm) =
     ConstructorFVal b1 b2 ad (cppid_inst sigma nm)) /\
  (expr_inst sigma (ConstructedVal b ad nm) =
     ConstructedVal b ad (cppid_inst sigma nm)) /\
  (expr_inst sigma (DestructorCall ad nm) =
     DestructorCall ad (cppid_inst sigma nm)) /\
  (expr_inst sigma (RValreq e) = RValreq (expr_inst sigma e)) /\
  (expr_inst sigma (ECompVal bytes ty) =
     ECompVal bytes (type_inst sigma ty)) /\
  (expr_inst sigma (ExceptionExpr e) = ExceptionExpr (expr_inst sigma e)) /\

  (exprl_inst sigma [] = []) /\
  (exprl_inst sigma (e::es) = expr_inst sigma e :: exprl_inst sigma es) /\

  (exprlop_inst sigma NONE = NONE) /\
  (exprlop_inst sigma (SOME elist) = SOME (exprl_inst sigma elist)) /\

  (expropt_inst sigma NONE = NONE) /\
  (expropt_inst sigma (SOME e) = SOME (expr_inst sigma e))
`

(* this shouldn't ever actually be called, because instantiation shouldn't
   ever see programs with dynamic helper syntax (such as this) in place *)
val varlocn_inst_def = Define`
  (varlocn_inst sigma (RefPlace nopt nm) =
     RefPlace nopt (cppid_inst sigma nm)) /\
  (varlocn_inst sigma (ObjPlace n) = ObjPlace n)
`;

(* fields that are initialised can't be member functions, so there is no
   chance the MI_fld could be a template call *)
val meminitid_inst_def = Define`
  (meminitid_inst sigma (MI_C id) = MI_C (cppid_inst sigma id)) /\
  (meminitid_inst sigma (MI_fld nm) = MI_fld nm)
`;

val stmt_inst_defn = Hol_defn "stmt_inst" `
  (stmt_inst sigma EmptyStmt = EmptyStmt) /\
  (stmt_inst sigma (CLoop ee st) =
     CLoop (eexpr_inst sigma ee) (stmt_inst sigma st)) /\
  (stmt_inst sigma (CIf ee st1 st2) =
     CIf (eexpr_inst sigma ee) (stmt_inst sigma st1) (stmt_inst sigma st2)) /\
  (stmt_inst sigma (Standalone ee) = Standalone (eexpr_inst sigma ee)) /\
  (stmt_inst sigma (Block b vdl stl) =
     Block b (MAP (vdec_inst sigma) vdl) (MAP (stmt_inst sigma) stl)) /\
  (stmt_inst sigma (Ret ee) = Ret (eexpr_inst sigma ee)) /\
  (stmt_inst sigma EmptyRet = EmptyRet) /\
  (stmt_inst sigma Break = Break) /\
  (stmt_inst sigma Cont = Cont) /\
  (stmt_inst sigma (Trap tt st) = Trap tt (stmt_inst sigma st)) /\
  (stmt_inst sigma (Throw eeopt) =
     Throw (OPTION_MAP (eexpr_inst sigma) eeopt)) /\
  (stmt_inst sigma (Catch st handlers) =
     Catch (stmt_inst sigma st)
           (MAP (\ (exnpd, st).
                   ((case exnpd of
                        NONE -> NONE
                     || SOME (sopt,ty) -> SOME (sopt, type_inst sigma ty)),
                    stmt_inst sigma st))
                handlers)) /\
  (stmt_inst sigma ClearExn = ClearExn)

     /\

  (eexpr_inst sigma (NormE e se) = NormE (expr_inst sigma e) se) /\
  (eexpr_inst sigma (EStmt st c) = EStmt (stmt_inst sigma st) c)

     /\

  (vdec_inst sigma (VDec ty nm) =
     VDec (type_inst sigma ty) (cppid_inst sigma nm)) /\
  (vdec_inst sigma (VDecInit ty nm init) =
     VDecInit (type_inst sigma ty)
              (cppid_inst sigma nm)
              (initialiser_inst sigma init)) /\
  (vdec_inst sigma (VDecInitA ty vlocn init) =
     VDecInitA (type_inst sigma ty)
               (varlocn_inst sigma vlocn)
               (initialiser_inst sigma init)) /\
  (vdec_inst sigma (VStrDec id infoopt) =
     VStrDec (cppid_inst sigma id) (OPTION_MAP (cinfo_inst sigma) infoopt)) /\
  (vdec_inst sigma (VException e) = VException (expr_inst sigma e))

     /\

  (centry_inst sigma (CFnDefn ty fld params body) =
     CFnDefn (type_inst sigma ty)
             (sfld_inst sigma fld)
             (MAP (\ (n,ty). (n, type_inst sigma ty)) params)
             (OPTION_MAP (stmt_inst sigma) body)) /\
  (centry_inst sigma (FldDecl fldnm ty) =
     FldDecl fldnm (type_inst sigma ty)) /\
  (centry_inst sigma (Constructor params meminits bodyopt) =
     Constructor (MAP (\ (n,ty). (n, type_inst sigma ty)) params)
                 (MAP (\ (mid,optargs). (meminitid_inst sigma mid,
                                         OPTION_MAP (MAP (expr_inst sigma))
                                                    optargs))
                      meminits)
                 (OPTION_MAP (stmt_inst sigma) bodyopt)) /\
  (centry_inst sigma (Destructor bodyopt) =
     Destructor (OPTION_MAP (stmt_inst sigma) bodyopt))

     /\

  (cinfo_inst sigma ci =
     <| fields := MAP (\ (ce,b,p). (centry_inst sigma ce, b, p)) ci.fields;
        ancestors := MAP (\ (cs,b,p). (cppid_inst sigma cs, b, p))
                         ci.ancestors |>)

     /\

  (initialiser_inst sigma (DirectInit0 elist) =
     DirectInit0 (MAP (expr_inst sigma) elist)) /\
  (initialiser_inst sigma (DirectInit ee) =
     DirectInit (eexpr_inst sigma ee)) /\
  (initialiser_inst sigma (CopyInit ee) = CopyInit (eexpr_inst sigma ee))
`;

val size_def = DB.fetch "statements" "CStmt_size_def"
val _ = augment_srw_ss [rewrites [size_def]]

val (stmt_inst_def, stmt_inst_ind) = Defn.tprove(
  stmt_inst_defn,
  WF_REL_TAC
    `measure
      (\s.
        case s of
           INL (_, st) -> CStmt_size st
        || INR (INL (_, ee)) -> ExtE_size ee
        || INR (INR (INL (_, vd))) -> var_decl_size vd
        || INR (INR (INR (INL (_, ce)))) -> class_entry_size ce
        || INR (INR (INR (INR (INL (_, ci))))) -> class_info_size ci
        || INR (INR (INR (INR (INR (_, i))))) -> initializer_size i)` THEN
  SRW_TAC [ARITH_ss][] THENL [
    Induct_on `handlers` THEN SRW_TAC [][] THEN SRW_TAC [ARITH_ss][] THEN
    RES_TAC THEN DECIDE_TAC,
    Induct_on `vdl` THEN SRW_TAC [][] THEN SRW_TAC [ARITH_ss][] THEN
    RES_TAC THEN DECIDE_TAC,
    Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Induct_on `l` THEN SRW_TAC [][] THEN SRW_TAC [ARITH_ss][] THEN
    RES_TAC THEN DECIDE_TAC,
    Induct_on `stl` THEN SRW_TAC [][] THEN SRW_TAC [ARITH_ss][] THEN
    RES_TAC THEN DECIDE_TAC
  ]);


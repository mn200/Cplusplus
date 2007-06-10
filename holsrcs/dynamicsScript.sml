(* Dynamic Semantics of C++ forms *)

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
in end

val _ = new_theory "dynamics";

val _ = set_trace "inddef strict" 1

(* an e-context is a function defining contexts where expression evaluation
   can occur *)
val valid_econtext_def = Define`
  valid_econtext f =
      (?f' e1. f = CApBinary f' e1) \/
      (?f' e2. f = \e1. CApBinary f' e1 e2) \/
      (?f' e2. f = \e1. Assign f' e1 e2) \/
      (?f' e1. f = \e2. Assign f' e1 e2) \/
      (?e2 f'. (f = (\e1. f' e1 e2)) /\
               f' IN {COr; CAnd; CommaSep}) \/
      (?e2 e3. (f = \e1. CCond e1 e2 e3)) \/
      (?f'. f = CApUnary f') \/
      (f IN  {Addr; Deref; PostInc; RValreq}) \/
      (?e1. f = OffsetDeref e1) \/
      (?e2. f = \e1. OffsetDeref e1 e2) \/
      (?fld. f = \e. SVar e fld) \/
      (?args. f = \e. FnApp e args) \/
      (?f' pre post.
          (f = \e. FnApp f' (APPEND pre (e :: post)))) \/
      (?t. f = Cast t)
`;

(* SANITY *)
val valid_econtext_rec_expr = store_thm(
  "valid_econtext_rec_expr",
  ``!P f e.
         valid_econtext f /\ rec_expr_P (f e) P ==> rec_expr_P e P``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [valid_econtext_def, rec_expr_P_def])

(* SANITY *)
val valid_econtexts_11 = store_thm(
  "valid_econtexts_11",
  ``!f. valid_econtext f ==> !e1 e2. (f e1 = f e2) = (e1 = e2)``,
  SRW_TAC [][valid_econtext_def] THEN SRW_TAC [][])

(* an lv-context is a function defining where lvalue to rvalue reduction can
   occur *)
val valid_lvcontext_def = Define`
  valid_lvcontext f =
        (?f' e1. f = CApBinary f' e1) \/
        (?f' e2. f = \e1. CApBinary f' e1 e2) \/
        (?e2 f'. (f = (\e1. f' e1 e2)) /\
                 f' IN {COr; CAnd; CommaSep}) \/
        (?e2 e3. (f = \e1. CCond e1 e2 e3)) \/
        (?f'. f = CApUnary f') \/
        (f IN  {Deref; RValreq}) \/
        (?e1 opt. (f = Assign opt e1)) \/
        (?args. f = \e. FnApp e args) \/
        (?t. f = Cast t) \/
        (?e1. f = OffsetDeref e1) \/
        (?e2. f = \e1. OffsetDeref e1 e2)
`

val addr_nonloopy = prove(
  ``!e. ~(Addr e = e)``,
  Induct THEN SRW_TAC [][]);

(* SANITY *)
val valid_lvcontext_thm = store_thm(
  "valid_lvcontext_thm",
  ``valid_lvcontext f =
      valid_econtext f /\
      (!fopt e2. ~(f = \e1. Assign fopt e1 e2)) /\
      (!fld. ~(f = \e. SVar e fld)) /\
      ~(f = Addr) /\
      ~(f = PostInc) /\
      (!pre post fnpos. ~(f = \e. FnApp fnpos (pre ++ (e :: post)))) ``,
  SRW_TAC [][valid_lvcontext_def, valid_econtext_def] THEN EQ_TAC THEN
  SRW_TAC [][] THEN SRW_TAC [][FUN_EQ_THM] THEN
  TRY (METIS_TAC []) THENL [
    Q.EXISTS_TAC `Addr e1`,
    Q.EXISTS_TAC `Addr fnpos`
  ] THEN SRW_TAC [][addr_nonloopy])

(* SANITY (corollary) *)
val lvcontexts_are_econtexts = store_thm(
  "lvcontexts_are_econtexts",
  --`!f. valid_lvcontext f ==> valid_econtext f`--,
  SRW_TAC [][valid_lvcontext_thm])

(* an fv-context is a context where a function value can decay into a pointer
   to function (object) value - everywhere except at the head of a function
   application.  At least one of the possibilities implicit in this is
   inconceivable (a function value can never be the first argument of a
   field selection).
*)
val valid_fvcontext_def = Define`
  valid_fvcontext f =
      valid_econtext f /\
      !args. ~(f = \f'. FnApp f' args)
`

(* installing a function - generating an address for it at the same time *)
val installfn_def = Define`
  installfn s0 ftype retty fnid params body fval s =
     ~(fval IN FDOM s0.fndecode) /\ ~(fnid IN FDOM s.fnmap) /\
     sizeof T
            (sizeofmap s)
            (ftype (Function retty (MAP SND params)))
            (LENGTH fval) /\
     (s = s0 with <| fnmap updated_by
                       (\fm. fm |+ (fnid, <| body := body;
                                             return_type := retty;
                                             parameters := params |>));
                     fnencode updated_by (\fm. fm |+ (fnid, fval));
                     fndecode updated_by (\fm. fm |+ (fval, fnid)) |>)
`




(* installing a bunch of member functions *)

(* imemfn is where the real work gets done - it takes a list of function
   definitions from with a class_info and "relationally" installs them into
   the state.  It doesn't bother with constructor or destructors as these
   can be specially looked up when needed, and can't have their addresses
   taken. *)
val imemfn_defn = Hol_defn "imemfn" `
  (imemfn cnm s0 [] s = (s0 = s)) /\
  (imemfn cnm s0 ((FldDecl flnm ty, b, p) :: rest) s = imemfn cnm s0 rest s) /\
  (imemfn cnm
          s0
          ((CFnDefn virtp retty nm params (SOME(SOME body)), statp, p) :: rest)
          s
    =
     if statp then
       ?s' fval.
            installfn s0 Ptr retty (mk_member cnm nm) params body fval s' /\
            imemfn cnm s' rest s
     else
       ?s' fval. installfn s0 (MPtr cnm) retty (mk_member cnm nm) params body
                           fval
                           s' /\
                 imemfn cnm s' rest s) /\
  (imemfn cnm s0 ((CFnDefn virtp retty nm params bd, statp, p) :: rest) s =
     imemfn cnm s0 rest s) /\
  (imemfn cnm s0 ((Constructor _ _ _, _, _) :: rest) s =
     imemfn cnm s0 rest s) /\
  (imemfn cnm s0 ((Destructor _ _, b, p) :: rest) s = imemfn cnm s0 rest s) /\
  (imemfn cnm s0 ((NClass sfn (SOME ci), b, p)::rest) s =
     ?s'. imemfn (mk_member cnm sfn) s0 (ci.fields) s' /\
          imemfn cnm s' rest s)
`

val (imemfn_def, imemfn_ind) = Defn.tprove(
  imemfn_defn,
  WF_REL_TAC `measure (\ (cnm,s,celist,s'). CStmt7_size celist)` THEN
  SRW_TAC [ARITH_ss][] THEN Cases_on `ci` THEN SRW_TAC [ARITH_ss][]);
val _ = save_thm("imemfn_def", imemfn_def)
val _ = save_thm("imemfn_ind", imemfn_ind)
val _ = export_rewrites ["imemfn_def"]


val install_member_functions_def =
    overload_on ("install_member_functions", ``imemfn``)

val signed_int_def = Define`
  signed_int i = THE (REP_INT (Signed Int) i)
`

(* this appears to be needlessly recursive on the first argument (the type),
   but when one added valuations for floats, the rhs would need to
   call a float-valuation function (not INT_VAL, whose range is
   necessarily just the integers *)

(* note that this predicate is two-valued: the possibility that a value
   isn't well-defined for the type is ignored.  This is because we assume
   that possibility is dealt with elsewhere: when values are read out of
   memory or otherwise constructed. *)
val is_zero_def = Define`
  (is_zero (Signed i) v = (INT_VAL (Signed i) v = SOME 0)) /\
  (is_zero (Ptr t) v = (INT_VAL (Ptr t) v = SOME 0))
`


val copy2globals_def = Define`
  copy2globals s = (s with genv := s.env)
`;

(* true if the nth argument of f is not a reference type *)
(* TODO: deal with overloading *)
val fn_expects_rval_def = Define`
  fn_expects_rval s thisty f n =
    ?retty args.
      (expr_type s RValue f (Function retty args) \/
       expr_type s RValue f (Ptr (Function retty args))) /\
      ~ref_type (EL n args)
`;


(* TODO: deal with overloading *)
(* TODO: complete definition of constructor_expects_rval *)
val constructor_expects_rval_def = Define`
  constructor_expects_rval s cnm arglist n = T
`

(* s, cnm and args are "inputs".  *)
(* TODO: deal with overloading *)
val find_constructor_info_def = Define`
  find_constructor_info s0 cnm args params mem_inits body =
    cnm IN defined_classes s0 /\
    ?prot.
       MEM (Constructor params mem_inits (SOME body), F, prot)
           (cinfo s0 cnm).fields /\
         (* constructors can't be static *)
       (MAP SND params = MAP value_type args)
`

(* TODO: deal with overloading, which is only constness *)
val find_destructor_info_def = Define`
  find_destructor_info s0 cnm body =
    cnm IN defined_classes s0 /\
    ?virtp prot.
       MEM (Destructor virtp (SOME body), F, prot) (cinfo s0 cnm).fields
`;



(* this function returns the prefix of sub-object constructor calls that must
   precede the body of a constructor, looking up mem-initialisors as
   necessary.
*)
val construct_ctor_pfx_def = Define`
  construct_ctor_pfx s mdp a cnm (mem_inits : mem_initializer list) =
    let allccs = constituent_offsets s mdp cnm in
    let direct_bases = get_direct_bases s cnm in
    let virt_bases = get_virtual_bases s cnm in
    let data_fields = initialisable_members s cnm in
    let lookup (nm:CPP_ID) = FINDL (\ (nm',mi). nm' = nm) mem_inits in

    let do_bases (pth : CPP_ID list) =
      let a' = subobj_offset s (cnm, pth) in
      let (nm : CPP_ID) = LAST pth
      in
         (* F T records, no, not most-derived, yes, a subobject *)
         case lookup nm of
           NONE -> (* 12.6.2 p4 - default initialisation *)
             [initA_constructor_call F T nm (a + a') []]
        || SOME (nm',NONE) -> (* 12.6.2 p3 1st case - value initialisation *)
             (@inits. value_init s F T (Class nm) (a + a') inits)
        || SOME (nm',SOME args) -> (* direct initialisation, with args as
                                      initialiser *)
             [initA_constructor_call F T nm (a + a') args] in
    let bases = FLAT (MAP (\bnm. do_bases [cnm; bnm]) direct_bases) in
    let virtuals = if mdp then FLAT (MAP (\vnm. do_bases [vnm]) virt_bases)
                   else [] in
    let do_nsd (nsdname, nsdty) =
      let (c,a') = THE (FINDL (\ (c, off). c = NSD nsdname nsdty) allccs)
      in
          (* T T pairs below record: yes, most-derived, yes, a subobject *)
          case lookup (Base nsdname) of
             NONE -> (* 12.6.2 p4 - default initialisation *)
               (@inits. default_init s T T nsdty (a + a') inits)
          || SOME(nm', NONE) -> (* 12.6.2 p3 1st case - value initialisation *)
               (@inits. value_init s T T nsdty (a + a') inits)
          || SOME(nm', SOME args) -> (* direct initialisation, with args as
                                        initialiser *)
               [initA_member_call a (mk_member cnm (IDName nsdname))
                                  nsdty (a + a') args]
    in
    let nsds = FLAT (MAP do_nsd data_fields)
  in
    virtuals ++ bases ++ nsds
`;

val callterminate =
    ``FnApp (Var  (IDConstant T [IDName "std"] (IDName "terminate"))) []``

val bad_cast_name_def = Define`
  bad_cast_name = IDConstant T [IDName "std"] (IDName "bad_cast")
`;

val realise_destructor_calls_def = Define`
  (* parameters
      exp           : T iff we are leaving a block because of an exception
      s0            : starting state, where there is a non-empty list
                        of things to destroy as the first element of
                        s.blockclasses
     outputs
      destcals      : list of statements with explicit destructor
                      calls for those objects that need destroying
      s             : resulting state, with subobj constructs added
                      to new scope of exprclasses underneath current one
  *)
  realise_destructor_calls exp s0 =
    let destwrap = if exp then
                     (\s. Catch s [(NONE, Standalone
                                            (EX ^callterminate base_se))])
                   else (\s. s) in
    let cloc2call (a, cnm, pth) =
          destwrap (Standalone (EX (DestructorCall a cnm) base_se)) in
    let destroy_these = HD s0.blockclasses in
    let foldthis c (here, escape) =
          case c of
             NormalConstruct cloc -> (cloc2call cloc :: here, escape)
          || SubObjConstruct cloc -> if exp then
                                       (cloc2call cloc :: here, escape)
                                     else (here, cloc :: escape) in
    let (destcalls, escapees) = FOLDR foldthis ([],[]) destroy_these
    in
        (destcalls,
         s0 with <| blockclasses := [] :: TL s0.blockclasses ;
                    exprclasses := HD s0.exprclasses :: escapees ::
                                   TL s0.exprclasses |>)
`;


val _ = new_constant("typeid_info", ``:state -> CPP_Type -> CExpr -> bool``)

val type_info_cnm_def = Define`
  type_info_cnm = IDConstant T [IDName "std"] (IDName "type_info")
`;

val typeid_info_characterised = new_axiom(
  "typeid_info_characterised",
  ``!s ty e.
      typeid_info s ty e ==>
      (?a p id.
         (e = LVal a (Class id) p) /\
         ((id = type_info_cnm) /\ (p = [id])
               \/
          (s,{}) |- path id to type_info_cnm via p)) /\
      !ty2. ~(ty = ty2) ==> ~typeid_info s ty2 e``);
(* would be nice to have a description of the functions supported by
   ::std::type_info here *)

val return_cont_def = Define`
  return_cont se ty = if ref_type ty then LVC I se
                      else RVC I se
`

val cont_comp_def = Define`
  (cont_comp f (RVC rc se) = RVC (f o rc) se) /\
  (cont_comp f (LVC lc se) = LVC (f o lc) se)
`

val RVR_def = Define`
  (RVR (EX e se) = EX (RValreq e) se) /\
  (RVR (ST s c) = ST s c)
`


val _ = print "About to define meaning relation\n"

val valuetype_def = Define`
  (valuetype (ECompVal v t) = t) /\
  (valuetype (LVal a t p) = static_type (t,p))
`;

val unamb_public_base_def = Define`
  (* ignore public-ness constraint for the moment (TODO) *)
  unamb_public_base s ty1 ty2 =
    ?c1 c2. (ty1 = Class c1) /\ (ty2 = Class c2) /\
            (s,{}) |- path c2 to c1 unique
`;


val exception_parameter_match_def = Define`
  (* embodies 15.3 paras 2-3 *)
  exception_parameter_match s paramty0 exnty =
    let paramty = case paramty0 of (* para 2 *)
                     Function retty argtys -> Ptr (Function retty argtys)
                  || Array bt sz -> Ptr bt
                  || x -> x
    in
        (* para 3, clause 1 *)
        (strip_const paramty = strip_const exnty) \/
        (strip_const paramty = Ref (strip_const exnty)) \/

        (* para 3, clause 2 *)
        (unamb_public_base s (strip_const paramty) exnty \/
         ?pty. (strip_const paramty = Ref pty) /\
               unamb_public_base s pty exnty) \/

        (* para 3, clauses 3 *)
        ?v1 v2. nonclass_conversion s (v1,exnty) (v2,paramty)
`;

val (meaning_rules, meaning_ind, meaning_cases) = Hol_reln`

(* RULE-ID: number-literal *)
(!n bl se s.
     (REP_INT (Signed Int) n = SOME bl)
   ==>
     mng (s, EX (Cnum n) se)
         (s, EX (ECompVal bl (Signed Int)) se)
)

   /\

(* RULE-ID: char-literal *)
(!n bl se s.
     (REP_INT BChar n = SOME bl)
   ==>
     mng (s, EX (Cchar n) se) (s, EX (ECompVal bl BChar) se)
)

   /\

(* RULE-ID: null-pointer *)
(!t se s.
     T
   ==>
     mng (s, EX (Cnullptr t) se)
         (s, EX (ECompVal (THE (ptr_encode s 0 t (SND (default_path t))))
                          (Ptr t))
                se)
)

   /\

(* RULE-ID: this *)
(!se s.
     T
   ==>
     mng (s, EX This se) (s, EX (THE s.thisvalue) se)
)

   /\

(* RULE-ID: var-to-lvalue *)
(!vname cnm ty ty0 se s a p.
     (lookup_type s vname = SOME ty0) /\
     object_type ty0 /\
     (lookup_addr s vname = SOME (a,cnm,p)) /\
     (ty = if class_type ty0 then Class cnm else ty0)
   ==>
     mng (s, EX (Var vname) se) (s, EX (LVal a ty p) se)
)

   /\

(* RULE-ID: var-to-fvalue *)
(!vname se s ty.
     (lookup_type s vname = SOME ty) /\
     function_type ty /\
     vname IN FDOM s.fnencode
   ==>
     mng (s, EX (Var vname) se) (s, EX (FVal vname ty NONE) se)
)

   /\

(* RULE-ID: cast *)
(!s v t v' t' se i.
     (INT_VAL t v = SOME i) /\ (SOME v' = REP_INT t' i)
   ==>
     mng (s, EX (Cast t' (ECompVal v t)) se)
         (s, EX (ECompVal v' t') se)
)

   /\

(* RULE-ID: cast-fails-1 *)
(!v t t' se s.
     (INT_VAL t v = NONE)
   ==>
     mng (s, EX (Cast t' (ECompVal v t)) se) (s, EX UndefinedExpr se)
)

   /\

(* RULE-ID: cast-fails-2 *)
(!v t t' se s i.
     (INT_VAL t v = SOME i) /\ (REP_INT t' i = NONE)
   ==>
     mng (s, EX (Cast t' (ECompVal v t)) se)
         (s, EX UndefinedExpr se))

   /\

(* RULE-ID: dyncast-derived-base-ref *)
(* assume that base is accessible (checked by compiler) *)
(!a dty dcnm scnm s se p p'.
     (strip_const dty = Class dcnm) /\
     (s,{}) |- path (LAST p) to dcnm unique /\ (* static check *)
     (s,{}) |- path (LAST p) to dcnm via p'
   ==>
     mng (s, EX (DynCast (Ref dty) (LVal a (Class scnm) p)) se)
         (s, EX (LVal a (Class scnm) (p ^ p')) se)
)

   /\

(* RULE-ID: dyncast-derived-base-ptr *)
(* assume that base is accessible (checked by compiler) *)
(!dty dcnm srcval srcty s se p p' a newval src_dynty.
     (strip_const dty = Class dcnm) /\
     (s,{}) |- path (LAST p) to dcnm unique /\ (* static check *)
     (s,{}) |- path (LAST p) to dcnm via p' /\
     (strip_const srcty = Class (LAST p)) /\
     (ptr_encode s a src_dynty p = SOME srcval) /\
     (ptr_encode s a src_dynty (p ^ p') = SOME newval)
   ==>
     mng (s, EX (DynCast (Ptr dty) (ECompVal srcval (Ptr srcty))) se)
         (s, EX (ECompVal newval (Ptr dty)) se)
)

   /\

(* RULE-ID: dyncast-base-other-ptr *)
(!s se dcnm dty destval srcval srcty a a' p p' src_dynty.
     (strip_const dty = Class dcnm) /\
     (ptr_encode s a src_dynty p = SOME srcval) /\
     (strip_const srcty = Class (LAST p)) /\
     polymorphic s (LAST p) /\ (* statically checked *)
     (s,{}) |- path (dest_class src_dynty) to dcnm via p' /\
     (SOME destval = ptr_encode s a' src_dynty p') /\
     (a' =
      if (s,{}) |- path (dest_class src_dynty) to dcnm unique then a
        (* should also check accessible, though I think this could be
           done statically *)
      else 0)
   ==>
     mng (s, EX (DynCast (Ptr dty) (ECompVal srcval (Ptr srcty))) se)
         (s, EX (ECompVal destval (Ptr dty)) se)
)

   /\

(* RULE-ID: dyncast-base-other-ref *)
(!s se dcnm dty scnm p p' a result src_dynty.
     (strip_const dty = Class dcnm) /\
     (src_dynty = Class scnm) /\
     polymorphic s (LAST p) /\
     (s,{}) |- path scnm to dcnm via p' /\
     (result =
      if (s,{}) |- path scnm to dcnm unique then
        (* should also check accessible, though I think this could
           be done statically *)
        LVal a src_dynty p'
      else
        EThrow (SOME (New (Class bad_cast_name) NONE)))
   ==>
     mng (s, EX (DynCast (Ref dty) (LVal a src_dynty p)) se)
         (s, EX result se)
)

   /\

(* RULE-ID: econtext-expr *)
(!f e0 se0 s0 e se s.
     mng (s0, EX e0 se0) (s, EX e se) /\
     valid_econtext f
   ==>
     mng (s0, EX (f e0) se0) (s, EX (f e) se)
)

   /\

(* RULE-ID: econtext-stmt *)
(!f e se0 s0 s stmt c.
     mng (s0, EX e se0) (s, ST stmt c) /\
     valid_econtext f
   ==>
     mng (s0, EX (f e) se0) (s, ST stmt (cont_comp f c))
)

   /\

(* RULE-ID: fcontext *)
(!f fnid ty se s bytes.
     fnid IN FDOM s.fnencode /\
     (s.fnencode ' fnid = bytes) /\
     valid_fvcontext f
   ==>
     mng (s, EX (f (FVal fnid ty NONE)) se)
         (s, EX (f (ECompVal bytes (Ptr ty))) se)
)

   /\

(* RULE-ID: econtext-undefinedness *)
(!f se s.
     valid_econtext f
   ==>
     mng (s, EX (f UndefinedExpr) se) (s, EX UndefinedExpr se)
)

   /\

(* RULE-ID: lvcontext *)
(!f e0 se0 s0 s e se.
     valid_lvcontext f /\
     lval2rval (s0,e0,se0) (s,e,se)
   ==>
     mng (s0, EX (f e0) se0) (s, EX (f e) se)
)

   /\

(* RULE-ID: expression-throw-some *)
(* choice of c is irrelevant, as any enclosing ST will replace it. *)
(!e se s c.
     T
   ==>
     mng (s, EX (EThrow (SOME e)) se)
         (s, ST (Throw (SOME (EX e se))) c)
)

   /\

(* RULE-ID: expression-throw-none *)
(!c se s.
     T
   ==>
     mng (s, EX (EThrow NONE) se) (s, ST (Throw NONE) c)
)

   /\

(* RULE-ID: apply-se *)
(!e se0 s0 s se.
     apply_se (se0, s0) (se, s)
   ==>
     mng (s0, EX e se0) (s, EX e se)
)

   /\

(* RULE-ID: apply-se-fails *)
(!e se0 s0.
     (!se s. ~(apply_se (se0, s0) (se, s))) /\
     ~is_null_se se0 /\
     ~(e = UndefinedExpr)
   ==>
     mng (s0, EX e se0) (s0, EX UndefinedExpr se0)
)

   /\

(* RULE-ID: comma-progresses *)
(!e1 e2 se s0.
     final_value (EX e1 se)
   ==>
     mng (s0, EX (CommaSep e1 e2) se) (s0, EX (RValreq e2) base_se)
)

   /\

(* RULE-ID: binop-fails *)
(!f v1 type1 v2 type2 se0 s.
     (!res restype. ~binop_meaning s f v1 (strip_const type1)
                                       v2 (strip_const type2)
                                       res restype)
   ==>
     mng (s, EX (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se0)
         (s, EX UndefinedExpr se0)
)

   /\

(* RULE-ID: binop-computes *)
(!s f v1 type1 v2 type2 res restype se.
     binop_meaning s f v1 (strip_const type1)
                       v2 (strip_const type2)
                       res restype
   ==>
      mng (s, EX (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se)
          (s, EX (ECompVal res restype) se)
)

   /\

(* RULE-ID: unop-computes *)
(!s f ival t result rt se.
     unop_meaning f ival (strip_const t) result rt
   ==>
     mng (s, EX (CApUnary f (ECompVal ival t)) se)
         (s, EX (ECompVal result rt) se)
)

   /\

(* RULE-ID: unop-fails *)
(!s0 se0 f ival t.
     (!res rt. ~(unop_meaning f ival (strip_const t) res rt))
   ==>
     mng (s0, EX (CApUnary f (ECompVal ival t)) se0)
         (s0, EX UndefinedExpr se0)
)

   /\

(* RULE-ID: and-false *)
(!v t se s sub2.
     is_zero t v
   ==>
     mng (s, EX (CAnd (ECompVal v t) sub2) se)
         (s, EX (ECompVal (signed_int 0) Bool) se)
)

   /\

(* RULE-ID: and-true *)
(!v t se s sub2.
     ~is_zero t v /\ is_null_se se
   ==>
     mng (s, EX (CAnd (ECompVal v t) sub2) se)
         (s, EX (CApUnary CNot (CApUnary CNot sub2)) base_se)
)

   /\

(* RULE-ID: or-true *)
(!v t sub2 se s.
     ~is_zero t v
   ==>
     mng (s, EX (COr (ECompVal v t) sub2) se)
         (s, EX (ECompVal (signed_int 1) Bool) se)
)

   /\

(* RULE-ID: or-false *)
(!v t sub2 se s.
     is_zero t v /\ is_null_se se
   ==>
     mng (s, EX (COr (ECompVal v t) sub2) se)
         (s, EX (CApUnary CNot (CApUnary CNot sub2)) base_se)
)

   /\

(* RULE-ID: cond-false *)
(!v t e2 t2 e3 t3 resexpr result_type se s sn.
     is_null_se se /\ scalar_type t /\
     expr_type s RValue e2 t2 /\
     expr_type s RValue e3 t3 /\
     expr_type s RValue (CCond (ECompVal v t) e2 e3) result_type /\
     is_zero t v  /\
     ((t2 = Class sn) /\ (resexpr = e3) \/
      (!sn. ~(t2 = Class sn)) /\ (resexpr = Cast result_type e3))
   ==>
     mng (s, EX (CCond (ECompVal v t) e2 e3) se) (s, EX resexpr base_se)
)

   /\

(* RULE-ID: cond-true *)
(!v t e2 t2 e3 t3 resexpr result_type se s sn.
     is_null_se se /\ scalar_type t /\
     expr_type s RValue e2 t2 /\
     expr_type s RValue e3 t3 /\
     expr_type s RValue (CCond (ECompVal v t) e2 e3) result_type /\
     ~is_zero t v /\
     ((t2 = Class sn) /\ (resexpr = e2) \/
       (!sn. ~(t2 = Class sn)) /\ (resexpr = Cast result_type e2))
   ==>
     mng (s, EX (CCond (ECompVal v t) e2 e3) se)
         (s, EX resexpr base_se)
)

   /\

(* RULE-ID: deref-objptr *)
(* 5.3.1 p1 - pointer to an object type *)
(!mval t t' se s addr pth.
     object_type t /\
     (SOME mval = ptr_encode s addr t' pth) /\
     (static_type (t',pth) = t)
   ==>
     mng (s, EX (Deref (ECompVal mval (Ptr t))) se)
         (s, EX (LVal addr t' pth) se)
)

   /\

(* RULE-ID: deref-objptr-fails *)
(!mval t se s.
     object_type t /\
     ((!addr t' p. ~(SOME mval = ptr_encode s addr t' p)) \/
      (?t' p. SOME mval = ptr_encode s 0 t' p))
   ==>
     mng (s, EX (Deref (ECompVal mval (Ptr t))) se)
         (s, EX UndefinedExpr se)
)

   /\

(* RULE-ID: deref-fnptr *)
(* 5.3.1 p1 - pointer to a function type *)
(!v retty argtys se s.
     v IN FDOM s.fndecode
   ==>
     mng (s, EX (Deref (ECompVal v (Ptr (Function retty argtys)))) se)
         (s, EX (FVal (s.fndecode ' v) (Function retty argtys) NONE) se)
)

   /\

(* RULE-ID: addr-lvalue *)
(* See 5.3.1 p2-5 - taking the address of an lvalue *)
(!a t pth se s result.
     (SOME result = ptr_encode s a t pth)
   ==>
     mng (s, EX (Addr (LVal a t pth)) se)
         (s, EX (ECompVal result (Ptr (static_type (t,pth)))) se)
)

   /\

(* RULE-ID: mem-addr-static-nonfn *)
(* 5.3.1 p2 if the address is taken of a qualified-ident that is actually a
   static member, then a normal address is generated.
   As it's an object type, it must be an IDName.
*)
(!cname fldname se s addr ty prot pth ptrval.
     object_type ty /\
     MEM (FldDecl fldname ty, T, prot) (cinfo s cname).fields /\
     (lookup_addr s (mk_member cname fldname) = SOME (addr, pth)) /\
     (SOME ptrval = ptr_encode s addr ty (SND pth))
   ==>
     mng (s, EX (MemAddr cname fldname) se)
         (s, EX (ECompVal ptrval (Ptr ty)) se)
)

   /\

(* RULE-ID: mem-addr-static-function *)
(!s se cnm fldname rt args bod prot.
     MEM (CFnDefn F rt fldname args bod, T, prot) (cinfo s cnm).fields
   ==>
     mng (s, EX (MemAddr cnm fldname) se)
         (s, EX (FVal (mk_member cnm fldname)
                      (Function rt (MAP SND args))
                      NONE) se)
)

   /\

(* RULE-ID: mem-addr-nonstatic *)
(!cnm fldname bl ty s se.
     (encode_offset cnm fldname = SOME bl) /\
     ((?prot. MEM (FldDecl fldname ty, F, prot) (cinfo s cnm).fields) \/
      (?prot v rt args bod.
          MEM (CFnDefn v rt fldname args bod, F, prot)
              (cinfo s cnm).fields /\
          (ty = Function rt (MAP SND args))))
   ==>
     mng (s, EX (MemAddr cnm fldname) se)
         (s, EX (ECompVal bl (MPtr cnm ty)) se)
)

   /\

(* RULE-ID: offset-deref *)
(!cnm1 cnm2 fldname s se a p bl fld fldty.
     (encode_offset cnm2 fldname = SOME bl) /\
     (fld = if function_type fldty then
              let (r,a) = dest_function_type fldty
              in
                if is_virtual s cnm2 fldname r a then
                  IDConstant F [] fldname
                else
                  mk_member cnm2 fldname
            else
              mk_member cnm2 fldname)
   ==>
     mng (s, EX (OffsetDeref
                     (LVal a (Class cnm1) p)
                     (ECompVal bl (MPtr cnm2 fldty)))
                se)
         (s, EX (SVar (LVal a (Class cnm1) p) fld)
                se)
)

   /\

(* RULE-ID: offset-deref-fails *)
(!s se cnm1 cnm2 a p fldty.
     T
   ==>
     mng (s, EX (OffsetDeref
                   (LVal a (Class cnm1) p)
                   (ECompVal null_member_ptr (MPtr cnm2 fldty)))
                se)
         (s, EX UndefinedExpr se)
)

   /\

(* RULE-ID: assign-op-assign *)
(* This rule turns an operator-assignment into a normal assignment, which is
   possible once the LHS has been evaluated into an l-value *)
(!f n t p e se0 s0.
     T
   ==>
     mng (s0, EX (Assign (SOME f) (LVal n t p) e) se0)
         (s0, EX (Assign NONE
                         (LVal n t p)
                         (CApBinary f (LVal n t p) e)) se0)
)

   /\

(* RULE-ID: assign-completes *)
(* TODO: make an assignment rule that can cope with assignments to
   classes, perhaps by writing an auxiliary relation that does just this
*)
(!s v0 t0 v lhs_t se0 se a resv.
    ~class_type lhs_t /\
    (nonclass_conversion s (v0,t0) (v,lhs_t) /\ (* 5.17 p3 *)
     (se = add_se (a, v) se0) /\ (resv = ECompVal v lhs_t)
                          \/
     (!v. ~nonclass_conversion s (v0, t0) (v, lhs_t)) /\
     (resv = UndefinedExpr) /\ (se = se0))
   ==>
     mng (s, EX (Assign NONE (LVal a lhs_t []) (ECompVal v0 t0)) se0)
         (s, EX resv se)
)

   /\

(* RULE-ID: postinc *)
(!se0 se s t t' sz v nv nv1 a resv.
     sizeof T (sizeofmap s) t sz /\ (v = mem2val s a sz) /\
     range_set a sz SUBSET s.initmap /\ ~class_type t /\
     binop_meaning s CPlus v t (signed_int 1) (Signed Int) nv1 t' /\
     (nonclass_conversion s (nv1,t') (nv,t) /\
      (se = add_se (a, nv) se0) /\ (resv = ECompVal v t)
                \/
      (!nv. ~nonclass_conversion s (nv1, t') (nv, t)) /\
      (se = se0) /\ (resv = UndefinedExpr))
   ==>
     mng (s, EX (PostInc (LVal a t [])) se0) (s, EX resv se)
)

   /\

(* RULE-ID: postinc-fails-inc-or-initialised *)
(!a t se0 sz s v.
     sizeof T (sizeofmap s) t sz /\ ~class_type t /\
     (v = mem2val s a sz) /\
     ((!nv1 t'.
         ~binop_meaning s CPlus v t (signed_int 1) (Signed Int) nv1 t') \/
     ~(range_set a sz SUBSET s.initmap))
   ==>
     mng (s, EX (PostInc (LVal a t [])) se0) (s, EX UndefinedExpr se0)
)

   /\

(* RULE-ID: typeid-expr-polymorphic-lvalue-evaluates *)
(!e0 se0 s0 s e se cnm.
     mng (s0, EX e0 se0) (s, EX e se) /\
     expr_type s0 LValue e0 (Class cnm) /\
     polymorphic s0 cnm
   ==>
     mng (s0, EX (ExpTypeID e0) se0)
         (s, EX (ExpTypeID e) se)
)

   /\

(* RULE-ID: typeid-expr-polymorphic-lvalue-completes *)
(!s a p cnm se type_value.
     polymorphic s cnm /\
     typeid_info s (Class cnm) type_value
   ==>
     mng (s, EX (ExpTypeID (LVal a (Class cnm) p)) se)
         (s, EX type_value se)
)

   /\

(* RULE-ID: typeid-expr-non-polymorphic-lvalue-completes *)
(!s e ty se type_value.
     expr_type s LValue e ty /\
     typeid_info s ty type_value /\
     (!cnm. (ty = Class cnm) ==> ~polymorphic s cnm)
   ==>
     mng (s, EX (ExpTypeID e) se) (s, EX type_value se)
)

   /\

(* RULE-ID: typeid-expr-rvalue-completes *)
(!s e ty se type_value.
     expr_type s RValue e ty /\
     (!ty. ~expr_type s LValue e ty) /\
     typeid_info s ty type_value
   ==>
     mng (s, EX (ExpTypeID e) se) (s, EX type_value se)
)

   /\

(* RULE-ID: typeid-type-completes *)
(!s ty ty0 se type_value.
     typeid_info s ty0 type_value /\
     (ty0 = if ref_type ty then (@ty0. ty = Ref ty0) else ty)
   ==>
     mng (s, EX (TyTypeID ty) se) (s, EX type_value se)
)

   /\

(* RULE-ID: nstatic-data-field-select *)
(* Note how the path p is used:
     - to figure out the static type of the l-value (LAST p)
     - to derive the path from the most-derived class to the sub-object
       enclosing the field.  The offset is calculated with respect to
       this because the sub-object could be anywhere, and might be virtual.

   Even though the fld will have been name-resolved into an
   appropriate class :: fld reference (giving us p', as per the first
   hypothesis), work still needs to be done dynamically, because we
   don't know what the dynamic shape of the lhs of the svar is.

   Dynamically, the path concatenation p ^ p' still needs to be done,
   and we have to also determine if the class in which we are looking
   up the field is most derived (calculation of mdp below).

   The call to "has least" gets us both the field's type, and also whether
   or not it is static.  (In this case, it has to be not.)

*)
(!s cnm1 cnm2 fldid ty se offn a mdp p p'.
     (s,{}) |- path (LAST p) to cnm2 via p' /\
     (s,{}) |- LAST p' has least (IDtl fldid) -: (ty, F) via [LAST p'] /\
     object_type ty /\
     (mdp = (cnm1 = cnm2) /\ (p = [cnm1])) /\
     is_qualified fldid /\
     (class_part fldid = cnm2) /\
     (SOME offn = lookup_offset s mdp fldid)
   ==>
     mng (s, EX (SVar (LVal a (Class cnm1) p) fldid) se)
         (s, EX (LVal (a + subobj_offset s (cnm1, p ^ p') + offn) ty
                      (SND (default_path ty))) se)
)

   /\

(* RULE-ID: static-data-member-field-selection *)
(!s se cnm cnm1 p p' fldid ty0 ty a statpath.
     (s,{}) |- path (LAST p) to (class_part fldid) via p' /\
     (s,{}) |- LAST p' has least (IDtl fldid) -: (ty0, T) via [LAST p'] /\
     (lookup_addr s fldid = SOME (a, cnm, statpath)) /\
     (ty = if class_type ty0 then Class cnm else ty0)
   ==>
     mng (s, EX (SVar (LVal a (Class cnm1) p) fldid) se)
         (s, EX (LVal a ty statpath) se)
)

   /\

(* RULE-ID: nstatic-fn-member-select *)
(* this is very similar to the above, because this is a non-virtual function
   that is being looked up.  We can tell it's not virtual because the
   identifier is structured (making the call to class_part well-formed) *)
(!se s a fldid ftype Cs Ds cnm retty ps body.
     (s,{}) |- path (LAST Cs) to class_part fldid via Ds /\
     (s,{}) |- LAST Ds has least method (IDtl fldid) -: (retty,F,ps,body)
            via [LAST Ds] /\
     (ftype = Function retty (MAP SND ps)) /\
     is_qualified fldid
   ==>
     mng (s, EX (SVar (LVal a (Class cnm) Cs) fldid) se)
         (s, EX (FVal fldid ftype (SOME (LVal a (Class cnm) (Cs ^ Ds)))) se)
)

   /\

(* RULE-ID: static-fn-member-select *)
(!se s a fldid ftype Cs Ds cnm retty ps body.
     (s,{}) |- path (LAST Cs) to class_part fldid via Ds /\
     (s,{}) |- LAST Ds has least method (IDtl fldid) -: (retty,T,ps,body)
            via [LAST Ds] /\
     (ftype = Function retty (MAP SND ps)) /\
     is_qualified fldid
   ==>
     mng (s, EX (SVar (LVal a (Class cnm) Cs) fldid) se)
         (s, EX (FVal fldid ftype NONE) se)
)

   /\

(* RULE-ID: virtual-fn-member-select *)
(* looking up a function member *)
(* This is the equivalent of most of Wasserab's rule BS10.  *)
(* As the FVal has its last component with path = Cs', the method call will
   jump into the method body with the right value for this *)

(* the IDConstant reflects the fact that a call to a virtual function will
   be via an unadorned name (the provision of a class qualification would
   force a particular function to be called).  Virtual functions can not
   be templates (14.5.2 p3), so the function name must just be a string.

   Similarly, the F in the "least method" call is the static-ness predicate,
   which must be false as this is a virtual method
 *)
(!a C Cs Cs' Ds fld dyn_retty se s static_retty body0 args0 args body.
     (s,{}) |- LAST Cs has least method
             (IDName fld) -: (static_retty,F,args0,body0) via Ds /\
     (s,{}) |- (C,Cs ^ Ds) selects (IDName fld) -: (dyn_retty,F,args,body)
         via Cs'
   ==>
     mng (s, EX (SVar (LVal a (Class C) Cs)
                      (IDConstant F [] (IDName fld))) se)
         (s, EX (FVal (mk_member (LAST Cs') (IDName fld))
                      (Function dyn_retty (MAP SND args))
                      (SOME (LVal a (Class C) Cs')))
                se)
)

   /\

(* RULE-ID: function-call-sqpt *)
(!fnid fty retty argtys eopt params se s.
     (fty = Function retty argtys) /\
     EVERYi (\i e. if ref_type (EL i argtys) then ?a t p. e = LVal a t p
                   else ?v t. e = ECompVal v t)
            params /\
     is_null_se se
   ==>
     mng (s, EX (FnApp (FVal fnid fty eopt) params) se)
         (s, EX (FnApp_sqpt (FVal fnid fty eopt) params) base_se)
)

   /\

(* RULE-ID: new-nonclass *)
(!ty s0 s se a sz result_ty ptrval.
     ~class_type (strip_array ty) /\ malloc s0 ty a /\
     (result_ty = case strip_const ty of
                     Array bty n -> bty
                  || somety -> ty) /\
     sizeof T (sizeofmap s0) ty sz /\
     (s = s0 with <| hallocmap updated_by (UNION) (range_set a sz) ;
                     constmap := if const_type ty then
                                   s0.constmap UNION range_set a sz
                                 else s0.constmap DIFF range_set a sz|>) /\
     (SOME ptrval = ptr_encode s0 a result_ty [])
   ==>
     mng (s0, EX (New ty NONE) se)
         (s, EX (ECompVal ptrval (Ptr result_ty)) se)
)

   /\

(* RULE-ID: new-simple-class *)
(* TODO: handle other forms in 5.3.4 para 15 *)
(* The T F parameters to the ConstructorFVal constructor indicate
    1. the object produced is most-derived, and
    2. it is not a sub-object (neither base, nor member) of some other
       object
*)
(!cnm s0 se s ty a sz args ptrval.
     (Class cnm = strip_const ty) /\ malloc s0 ty a /\
     sizeof T (sizeofmap s0) ty sz /\
     (s = s0 with <| hallocmap updated_by (UNION) (range_set a sz) ;
                     constmap := if const_type ty then
                                   s0.constmap UNION range_set a sz
                                 else s0.constmap DIFF range_set a sz|>) /\
     (SOME ptrval = ptr_encode s0 a ty [cnm])
   ==>
     mng (s0, EX (New ty (SOME args)) se)
         (s, EX (CommaSep (FnApp (ConstructorFVal T F a cnm) args)
                          (ECompVal ptrval (Ptr ty)))
                se)
)

   /\

(* RULE-ID: constructor-call-sqpt *)
(!mdp subp a cnm params se s.
     EVERYi (\i e. if constructor_expects_rval s cnm params i then
                     ?v t. e = ECompVal v t
                   else
                     ?a t p. e = LVal a t p)
            params /\
     is_null_se se
   ==>
     mng (s, EX (FnApp (ConstructorFVal mdp subp a cnm) params) se)
         (s, EX (FnApp_sqpt (ConstructorFVal mdp subp a cnm) params) base_se)
)

   /\

(* RULE-ID: function-ptr-to-function-lval *)
(* 5.2.2 p1 - this rule handles the situation where the postfix-expression
   is a pointer to a function value *)
(!v retty argtys args se s.
     v IN FDOM s.fndecode
   ==>
     mng (s, EX (FnApp (ECompVal v (Ptr (Function retty argtys))) args) se)
         (s, EX (FnApp (FVal (s.fndecode ' v)
                             (Function retty argtys)
                             NONE)
                       args) se)
)

   /\

(* RULE-ID: global-function-call *)
(* the NONE as FVal's third argument means this is a global function *)
(* TODO: handle return type casting *)
(!ftype args pdecls params se s0 fnid rtype body.
     (find_best_fnmatch s0 fnid (MAP valuetype args) rtype params body) /\
     (pdecls = MAP (\ ((n,ty),a). VDecInit ty
                                           (Base n)
                                           (CopyInit (EX a base_se)))
                   (ZIP (params, args)))
   ==>
     mng (s0, EX (FnApp_sqpt (FVal fnid ftype NONE) args) se)
         (s0 with <| stack updated_by 
                        (CONS (s0.env, s0.thisvalue, s0.allocmap));
                     thisvalue := NONE;
                     blockclasses updated_by stackenv_newscope ;
                     exprclasses updated_by stackenv_newscope ;
                     env := empty_env |>,
          ST (Block T pdecls [body]) (return_cont se rtype))
)

   /\

(* RULE-ID: member-function-call *)
(*   by the time this call is made, we have already figured out which
     function we will be jumping into

     NOTE: the block is "manually" entered, hence its flag being T, so that
     its internal thisvalue can be set correctly.
*)
(!fnid ftype a cname args rtype se0 s0 p params pdecls body this.
     (find_best_fnmatch s0 fnid (MAP valuetype args) rtype params body) /\
     (pdecls = MAP (\ ((n,ty),a). VDecInit ty
                                           (Base n)
                                           (CopyInit (EX a base_se)))
                   (ZIP (params, args))) /\
     (SOME this = ptr_encode s0 a (Class cname) p)
   ==>
     mng (s0, EX (FnApp_sqpt (FVal fnid ftype (SOME (LVal a (Class cname) p)))
                             args) se0)
         (s0 with <| stack updated_by 
                       (CONS (s0.env, s0.thisvalue, s0.allocmap));
                     thisvalue := SOME (ECompVal this (Ptr (Class cname)));
                     blockclasses updated_by stackenv_newscope ;
                     exprclasses updated_by stackenv_newscope ;
                     env := empty_env
                  |>,
          ST (Block T pdecls [body]) (return_cont se0 rtype))
)

   /\

(* RULE-ID: constructor-function-call *)
(!cnm mdp subp pdecls a args se0 params s0 mem_inits this body newstmt cpfx.
     find_constructor_info s0 cnm args params mem_inits body /\
     (pdecls = MAP (\ ((n,ty),a). VDecInit ty
                                           (Base n)
                                           (CopyInit (EX a base_se)))
                   (ZIP (params, args))) /\
     (SOME this = ptr_encode s0 a (Class cnm) [cnm]) /\
     (cpfx = construct_ctor_pfx s0 mdp a cnm mem_inits) /\
     (newstmt =
        if is_catch body then
          let (bod,handlers) = dest_catch body
          in
            Block T pdecls [Catch (Block F cpfx [bod])
                                  (MAP (\ (e,st).
                                          (e, Block F [] [st; Throw NONE]))
                                       handlers)]
        else Block T (pdecls ++ cpfx) [body])
   ==>
     mng (s0, EX (FnApp_sqpt (ConstructorFVal mdp subp a cnm) args) se0)
         (s0 with <| thisvalue := SOME (ECompVal this (Ptr (Class cnm))) ;
                     stack updated_by 
                       (CONS (s0.env, s0.thisvalue, s0.allocmap)) ;
                     blockclasses updated_by stackenv_newscope ;
                     exprclasses updated_by stackenv_newscope ;
                     env := empty_env |>,
          ST newstmt (RVC (\e. ConstructedVal subp a cnm) se0))
)

   /\

(* RULE-ID: fnapp-lval2rval *)
(!f pfx e0 e sfx se0 se s0 s.
     lval2rval (s0,e0,se0) (s,e,se) /\
     fn_expects_rval s0
                     (case s0.thisvalue of
                         SOME (ECompVal bytes (Ptr ty)) -> SOME ty
                      || _ -> NONE)
                     f
                     (LENGTH pfx)
   ==>
     mng (s0, EX (FnApp f (pfx ++ (e0 :: sfx))) se0)
         (s, EX (FnApp f (pfx ++ (e :: sfx))) se)
)

   /\

(* RULE-ID: return-eval-under *)
(!exte0 exte s1 s2 c.
     mng (s1, exte0) (s2, exte)
   ==>
     mng (s1, ST (Ret exte0) c) (s2, ST (Ret exte) c)
)

   /\

(* RULE-ID: return-lval2rval *)
(!e0 se0 s0 e se ret_se s c.
     lval2rval (s0,e,se0) (s,e,se)
   ==>
     mng (s0, ST (Ret (EX e0 se0)) (RVC c ret_se))
         (s, ST (Ret (EX e se)) (RVC c ret_se))
)

   /\

(* RULE-ID: return-rvalue *)
(* all recursive stmt rules require RHS of reduction to still be
   an ST, preventing this rule from firing at depth.  Note that
   class r-values can't be returned from this rule as class values are
   never represented with ECompVals. *)
(!v t s se0 se c.
     is_null_se se0
   ==>
     mng (s, ST (Ret (EX (ECompVal v t) se0)) (RVC c se))
         (s, EX (c (ECompVal v t)) se)
)

   /\

(* RULE-ID: return-lvalue *)
(!a t p se0 se c s.
     is_null_se se0
   ==>
     mng (s, ST (Ret (EX (LVal a t p) se0)) (LVC c se))
         (s, EX (c (LVal a t p)) se)
)

   /\

(* RULE-ID: return-exception *)
(!e c s.
     is_exnval e
   ==>
     mng (s, ST (Ret e) c) (s, mk_exn e c)
)

   /\

(* RULE-ID: empty-ret *)
(!s c.
     T
   ==>
     mng (s, ST EmptyRet c)
         (s, ST (Ret (EX (ECompVal [] Void) base_se)) c)
)

   /\

(* RULE-ID: empty-stmt-empty-ret *)
(!s c se.
     T
   ==>
     mng (s, ST EmptyStmt (RVC c se))
         (s, EX (c (ECompVal [] Void)) se)
)

   /\

(* RULE-ID: trap-stmt-evaluation *)
(* statements evaluate as normal under Traps *)
(!tt st st' c s0 s.
     mng (s0, ST st c) (s, ST st' c)
   ==>
     mng (s0, ST (Trap tt st) c) (s, ST (Trap tt st') c)
)

   /\

(* RULE-ID: catch-stmt-evaluation *)
(* statements evaluate normally under catch *)
(!st c s0 s st' hnds.
     mng (s0, ST st c) (s, ST st' c)
   ==>
     mng (s0, ST (Catch st hnds) c) (s, ST (Catch st' hnds) c)
)

   /\

(* RULE-ID: throw-expr-evaluation *)
(* expressions evaluate under throw *)
(!e0 e s0 s c.
     mng (s0, RVR e0) (s, RVR e)
   ==>
     mng (s0, ST (Throw (SOME e0)) c) (s, ST (Throw (SOME e)) c)
)

   /\

(* RULE-ID: throw-expr-exception *)
(* the expression being evaluated may itself cause an exception *)
(!e c s.
     is_exnval e
   ==>
     mng (s, ST (Throw (SOME e)) c) (s, mk_exn e c)
)

   /\

(* RULE-ID: bare-throw-succeeds *)
(!s0 e es c.
     (s0.current_exns = e::es)
   ==>
     mng (s0, ST (Throw NONE) c)
         (s0 with current_exns := es,
          ST (Throw (SOME (EX e base_se))) c)
)

   /\

(* RULE-ID: bare-throw-fails *)
(!s0 ct.
     (s0.current_exns = [])
   ==>
     mng (s0, ST (Throw NONE) ct)
         (s0, ST (Standalone (EX ^callterminate base_se)) ct)
)

   /\

(* RULE-ID: clear-exn *)
(!s0 c e es.
     (s0.current_exns = e::es)
   ==>
     mng (s0, ST ClearExn c)
         (s0 with current_exns := es, ST EmptyStmt c)
)

   /\

(* RULE-ID: catch-stmt-empty-hnds *)
(* you wouldn't expect to see this form input (in fact, it is syntactically
   impossible), but it can arise as syntax evolves (successive handlers are
   tried and found not to match the type of the exception value)
*)
(!st c s0.
     T
   ==>
     mng (s0, ST (Catch st []) c) (s0, ST st c)
)

   /\

(* RULE-ID: catch-normal-stmt-passes *)
(!st hnds c s0.
     final_stmt st c /\
     ~exception_stmt st
   ==>
     mng (s0, ST (Catch st hnds) c) (s0, ST st c)
)

   /\

(* RULE-ID: catch-all *)
(!exn e hnd_body rest c s0.
     (exn = SOME (EX e base_se))
   ==>
     mng (s0, ST (Catch (Throw exn) ((NONE, hnd_body) :: rest)) c)
         (s0 with current_exns updated_by (CONS e),
          ST (Block F [] [hnd_body; ClearExn]) c)
)

   /\

(* RULE-ID: catch-specific-type-matches *)
(* NOTE: relying on the fact that no user program can generate " no name " as
   the name of an identifier *)
(!exn e hnd_body rest c s0 pty pnameopt pname.
     (exn = SOME (EX e base_se)) /\
     exception_parameter_match s0 pty (value_type e) /\
     (pname = case pnameopt of SOME s -> Base s
                            || NONE -> (Base " no name "))
   ==>
     mng (s0, ST (Catch (Throw exn)
                        ((SOME(pnameopt, pty), hnd_body) :: rest)) c)
         (s0 with current_exns updated_by (CONS e),
          ST (Block F [VDecInit pty pname
                                    (CopyInit (EX e base_se))]
                      [hnd_body; ClearExn]) c)
)

   /\

(* RULE-ID: catch-specific-type-nomatch *)
(!exn e hnd_body rest c s0 pty pnameopt.
     (exn = SOME (EX e base_se)) /\
     ~exception_parameter_match s0 pty (value_type e)
   ==>
     mng (s0, ST (Catch (Throw exn)
                        ((SOME(pnameopt, pty), hnd_body) :: rest)) c)
         (s0, ST (Catch (Throw exn) rest) c)
)

   /\


(* final cases for Traps.  *)
(* RULE-ID: trap-break-catches *)
(!c s.
     T
   ==>
     mng (s, ST (Trap BreakTrap Break) c) (s, ST EmptyStmt c)
)

   /\

(* RULE-ID: trap-continue-catches *)
(!c s.
     T
   ==>
     mng (s, ST (Trap ContTrap Cont) c) (s, ST EmptyStmt c)
)

   /\

(* RULE-ID: trap-continue-passes-break *)
(!c s.
     T
   ==>
     mng (s, ST (Trap ContTrap Break) c) (s, ST Break c)
)

   /\

(* RULE-ID: trap-break-passes-continue *)
(!c s.
     T
   ==>
     mng (s, ST (Trap BreakTrap Cont) c) (s, ST Cont c)
)

   /\

(* RULE-ID: trap-emptystmt-passes *)
(!c tt s0.
     T
   ==>
     mng (s0, ST (Trap tt EmptyStmt) c) (s0, ST EmptyStmt c)
)

   /\

(* RULE-ID: trap-ret-passes *)
(!c tt e s.
     final_value e
   ==>
     mng (s, ST (Trap tt (Ret e)) c) (s, ST (Ret e) c)
)

   /\

(* RULE-ID: trap-exn-passes *)
(!tt exn c s.
     exception_stmt exn
   ==>
     mng (s, ST (Trap tt exn) c) (s, ST exn c)
)

   /\

(* RULE-ID: standalone-evaluates *)
(!exte c s1 s2 exte'.
     mng (s1, exte) (s2, exte')
   ==>
     mng (s1, ST (Standalone exte) c) (s2, ST (Standalone exte') c)
)

   /\

(* RULE-ID: standalone-finishes *)
(!e se c s.
     is_null_se se /\
     final_value e
   ==>
     mng (s, ST (Standalone e) c) (s, ST EmptyStmt c)
)

   /\

(* RULE-ID: standalone-exception *)
(!e c s.
     is_exnval e
   ==>
     mng (s, ST (Standalone e) c) (s, mk_exn e c)
)

   /\

(* RULE-ID: if-eval-guard *)
(!guard guard' c t e s0 s.
     mng (s0, RVR guard) (s, RVR guard')
   ==>
     mng (s0, ST (CIf guard t e) c) (s, ST (CIf guard' t e) c)
)

   /\

(* RULE-ID: if-true *)
(!v t se thenstmt elsestmt c s.
     scalar_type t /\ is_null_se se /\ ~is_zero t v
   ==>
     mng (s, ST (CIf (EX (ECompVal v t) se) thenstmt elsestmt) c)
         (s, ST thenstmt c)
)

   /\

(* RULE-ID: if-false *)
(!v t se thenstmt elsestmt c s.
     scalar_type t /\ is_null_se se /\ is_zero t v
   ==>
     mng (s, ST (CIf (EX (ECompVal v t) se) thenstmt elsestmt) c)
         (s, ST elsestmt c)
)

   /\

(* RULE-ID: if-exception *)
(!guard thenstmt elsestmt c s.
     is_exnval guard
   ==>
     mng (s, ST (CIf guard thenstmt elsestmt) c)
         (s, mk_exn guard c)
)

   /\

(* RULE-ID: loop *)
(* somewhat ugly that a bunch of blocks will accumulate around every
   iteration of the loop... *)
(!guard bdy c s.
     T
   ==>
     mng (s, ST (CLoop guard bdy) c)
         (s, ST (CIf guard (Block F [] [bdy; CLoop guard bdy])
                           EmptyStmt) c)
)

   /\

(* RULE-ID: block-entry *)
(!vds sts s c.
     T
   ==>
     mng (s, ST (Block F vds sts) c)
         (s with <| stack updated_by 
                      (CONS (s.env, s.thisvalue, s.allocmap));
                    blockclasses updated_by stackenv_newscope ;
                    exprclasses updated_by stackenv_newscope |>,
          ST (Block T vds sts) c)
)

   /\

(* RULE-ID: block-exit-destructors-to-call *)
(* normally constructed objects at this level are always destroyed here *)
(!s0 s c st  bcs destroy_these destcalls.
     (s0.blockclasses = destroy_these :: bcs) /\ ~(destroy_these = []) /\
     final_stmt st c /\
     ((destcalls, s) = realise_destructor_calls (exception_stmt st) s0)
   ==>
     mng (s0, ST (Block T [] [st]) c)
         (s, ST (Block T [] (destcalls ++ [st])) c)
)

   /\

(* RULE-ID: destructor-call *)
(!a p se0 s0 this cnm body.
     (cnm = LAST p) /\
     is_null_se se0 /\
     (SOME this = ptr_encode s0 a (Class cnm) [cnm]) /\
     find_destructor_info s0 cnm body
   ==>
     mng (s0, EX (DestructorCall a cnm) se0)
         (s0 with <| stack updated_by 
                        (CONS (s0.env, s0.thisvalue,s0.allocmap));
                     env := empty_env;
                     thisvalue := SOME (ECompVal this (Ptr (Class cnm)));
                     blockclasses updated_by stackenv_newscope ;
                     exprclasses updated_by stackenv_newscope |>,
          ST (Block T [] [body]) (return_cont se0 Void))
)

   /\

(* RULE-ID: block-exit *)
(!st s c env stk' this amap bcs ecs.
     (s.stack = (env,this,amap) :: stk') /\
     final_stmt st c /\
     (s.blockclasses = []::bcs) /\
     (s.exprclasses = []::ecs)
   ==>
     mng (s, ST (Block T [] [st]) c)
         (s with <| stack := stk';
                    allocmap := amap;
                    env := env;
                    thisvalue := this;
                    blockclasses := bcs;
                    exprclasses := ecs |>,
          ST st c)
)

   /\

(* RULE-ID: block-emptystmt *)
(!sts s c.
     ~(sts = [])
   ==>
     mng (s, ST (Block T [] (EmptyStmt::sts)) c)
         (s, ST (Block T [] sts) c)
)

   /\

(* RULE-ID: block-interrupted *)
(!sts exstmt s c.
     final_stmt exstmt c /\ ~(exstmt = EmptyStmt) /\ ~(sts = [])
   ==>
     mng (s, ST (Block T [] (exstmt::sts)) c)
         (s, ST (Block T [] [exstmt]) c)
)

   /\

(* RULE-ID: block-stmt-evaluate *)
(!st st' sts c s0 s.
     mng (s0, ST st c) (s, ST st' c)
   ==>
     mng (s0, ST (Block T [] (st :: sts)) c)
         (s, ST (Block T [] (st' :: sts)) c)
)

   /\

(* RULE-ID: block-declmng *)
(!s0 s d0 ds vds sts c.
     declmng mng (d0, s0) (ds, s)
   ==>
     mng (s0, ST (Block T (d0 :: vds) sts) c)
         (s, ST (Block T (ds ++ vds) sts) c)
)

   /\

(* RULE-ID: block-declmng-exception *)
(!d0 s0 s f e ex ty loc c c' sts vds.
     ((f = CopyInit) \/ (f = DirectInit)) /\
     declmng mng (d0, s0) ([VDecInitA ty loc (f e)], s) /\
     is_exnval e /\
     (e = ST (Throw (SOME ex)) c')
   ==>
     mng (s0, ST (Block T (d0 :: vds) sts) c)
         (s, ST (Block T [] [Throw (SOME ex)]) c)
)

   /\

(* RULE-ID: block-vstrdec-forward *)
(* this kind of declaration is made only so that a subsequent definition
   that refers to the name links to the right sort of class.  This is all
   handled by name resolution, so the dynamics can just ignore these *)
(!name vds sts c s0.
     T
   ==>
     mng (s0, ST (Block T (VStrDec name NONE :: vds) sts) c)
         (s0, ST (Block T vds sts) c)
)

   /\

(* RULE-ID: block-vstrdec *)
(* this is the declaration of a local class *)
(!name info0 info userdefs s0 s vds sts c env' lclasses.
     ((info,userdefs) = define_default_specials info0) /\
     install_member_functions name s0 info.fields s /\
     ~is_abs_id name /\
     (SOME env' = update_class name (info,userdefs) s.env)
   ==>
     mng (s0, ST (Block T (VStrDec name (SOME info0) :: vds) sts) c)
         (s with env := env', ST (Block T (lclasses ++ vds) sts) c))
`
val _ = overload_on ("meaning", ``mng``)

val _ = export_theory();



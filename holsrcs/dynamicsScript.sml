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
        (?t. f = Cast t)
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
val mk_member_def = Define`
  mk_member (IDConstant b sfs sf1) sf2 = IDConstant b (sfs ++ [sf1]) sf2
`;


(* imemfn is where the real work gets done - it takes a list of function
   definitions from with a class_info and "relationally" installs them into
   the state.  It doesn't bother with constructor or destructors as these
   can be specially looked up when needed, and can't have their addresses
   taken. *)
val imemfn_def = Define`
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
  (imemfn cnm s0 ((Destructor _ _, b, p) :: rest) s = imemfn cnm s0 rest s)
`

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
    let data_fields = THE (nsdmembers s cnm) in
    let lookup nm = FINDL (\ (nm',mi). nm' = nm) mem_inits in
           (* TODO: replace equality with a name comparison functionality
                    that copes with the example in notes/12.6.2p1.cpp *)

    let do_bases pth =
      let a' = subobj_offset s (cnm, pth) in
      let nm = LAST pth
      in
         (* F T records, no, not most-derived, yes, a subobject *)
         case lookup (MI_C nm) of
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
          case lookup (MI_fld nsdname) of
             NONE -> (* 12.6.2 p4 - default initialisation *)
               (@inits. default_init s T T nsdty (a + a') inits)
          || SOME(nm', NONE) -> (* 12.6.2 p3 1st case - value initialisation *)
               (@inits. value_init s T T nsdty (a + a') inits)
          || SOME(nm', SOME args) -> (* direct initialisation, with args as
                                        initialiser *)
               [initA_member_call nsdty (a + a') args]
    in
    let nsds = FLAT (MAP do_nsd data_fields)
  in
    virtuals ++ bases ++ nsds
`;

val callterminate =
    ``FnApp (Var  (IDConstant T [SFName "std"] (SFName "terminate"))) []``

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
                                            (mExpr ^callterminate base_se))])
                   else (\s. s) in
    let cloc2call (a, cnm, pth) =
          destwrap (Standalone (mExpr (DestructorCall a cnm) base_se)) in
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






val return_cont_def = Define`
  return_cont se ty = if ref_type ty then LVC I se
                      else RVC I se
`

val cont_comp_def = Define`
  (cont_comp f (RVC rc se) = RVC (f o rc) se) /\
  (cont_comp f (LVC lc se) = LVC (f o lc) se)
`

val RVR_def = Define`
  (RVR (mExpr e se) = mExpr (RValreq e) se) /\
  (RVR (mStmt s c) = mStmt s c)
`

val _ = print "About to define meaning relation\n"
val mng  =
    mk_var("meaning", ``:ExtE -> CState -> (CState # ExtE) -> bool``)
val _ = temp_overload_on("ev", ``mExpr``)

val valuetype_def = Define`
  (valuetype (ECompVal v t) = t) /\
  (valuetype (LVal a t p) = static_type (t,p))
`;

val unamb_public_base_def = Define`
  (* ignore public-ness constraint for the moment (TODO) *)
  unamb_public_base s ty1 ty2 =
    ?c1 c2. (ty1 = Class c1) /\ (ty2 = Class c2) /\
            s |- path c2 to c1 unique
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
(!n se s.
     T
   ==>
     ^mng (mExpr (Cnum n) se) s
          (s, ev (ECompVal (signed_int n) (Signed Int)) se))

   /\

(* RULE-ID: char-literal *)
(!n se s.
     T
   ==>
     ^mng (mExpr (Cchar n) se) s
          (s, ev (ECompVal (signed_int n) BChar) se))

   /\

(* RULE-ID: null-pointer *)
(!t se s.
     T
   ==>
     ^mng (mExpr (Cnullptr t) se) s
          (s, ev (ECompVal (THE (ptr_encode s 0 t (default_path t)))
                           (Ptr t))
                 se))

   /\

(* RULE-ID: this *)
(!se s.
     T
   ==>
     ^mng (mExpr This se) s (s, ev (THE s.thisvalue) se))

   /\

(* RULE-ID: var-to-lvalue *)
(!vname ty se s a p.
     (lookup_type s vname = SOME ty) /\
     object_type ty /\
     (lookup_addr s vname = SOME (a,p))
   ==>
     ^mng (mExpr (Var vname) se) s
          (s, ev (LVal a ty p) se))

   /\

(* RULE-ID: var-to-fvalue *)
(!vname se s ty.
     (lookup_type s vname = SOME ty) /\
     function_type ty /\
     vname IN FDOM s.fnencode
   ==>
     ^mng (mExpr (Var vname) se) s (s, ev (FVal vname ty NONE) se))

   /\

(* RULE-ID: cast *)
(!s v t v' t' se i.
     (INT_VAL t v = SOME i) /\ (SOME v' = REP_INT t' i)
   ==>
     ^mng (mExpr (Cast t' (ECompVal v t)) se) s
          (s, ev (ECompVal v' t') se))

   /\

(* RULE-ID: cast-fails-1 *)
(!v t t' se s.
     (INT_VAL t v = NONE)
   ==>
     ^mng (mExpr (Cast t' (ECompVal v t)) se) s (s, ev UndefinedExpr se))

   /\

(* RULE-ID: cast-fails-2 *)
(!v t t' se s i.
     (INT_VAL t v = SOME i) /\ (REP_INT t' i = NONE)
   ==>
     ^mng (mExpr (Cast t' (ECompVal v t)) se) s (s, ev UndefinedExpr se))

   /\

(* RULE-ID: econtext-expr *)
(!f e se0 s0 e' se s.
     ^mng (mExpr e se0) s0 (s, ev e' se) /\
     valid_econtext f
   ==>
     ^mng (mExpr ((f:CExpr->CExpr) e) se0) s0 (s, ev (f e') se))

   /\

(* RULE-ID: econtext-stmt *)
(!f e se0 s0 s stmt c.
     ^mng (mExpr e se0) s0 (s, mStmt stmt c) /\
     valid_econtext f
   ==>
     ^mng (mExpr (f e) se0) s0 (s, mStmt stmt (cont_comp f c)))

   /\

(* RULE-ID: fcontext *)
(!f fnid ty se s bytes.
     fnid IN FDOM s.fnencode /\ (s.fnencode ' fnid = bytes) /\
     valid_fvcontext f
   ==>
     ^mng (mExpr (f (FVal fnid ty NONE)) se) s
          (s, ev (f (ECompVal bytes (Ptr ty))) se))

   /\

(* RULE-ID: econtext-propagates-undefinedness *)
(!f se s.
     valid_econtext f
   ==>
     ^mng (mExpr (f UndefinedExpr) se) s (s, ev UndefinedExpr se))

   /\

(* RULE-ID: lvcontext *)
(!f e0 se0 s0 s e se.
     valid_lvcontext f /\ lval2rval (s0,e0,se0) (s,e,se)
   ==>
     ^mng (mExpr ((f:CExpr->CExpr) e0) se0) s0 (s, ev (f e) se))

   /\

(* RULE-ID: expression-throw-some *)
(* choice of c is irrelevant, as any enclosing mStmt will replace it. *)
(!e se s c.
     T
   ==>
     ^mng (mExpr (EThrow (SOME e)) se) s
          (s, mStmt (Throw (SOME (mExpr e se))) c))

   /\

(* RULE-ID: expression-throw-none *)
(!c se s.
     T
   ==>
     ^mng (mExpr (EThrow NONE) se) s (s, mStmt (Throw NONE) c))

   /\

(* RULE-ID: apply-se *)
(!e se0 s0 s se.
     apply_se (se0, s0) (se, s)
   ==>
     ^mng (mExpr e se0) s0 (s, ev e se))

   /\

(* RULE-ID: apply-se-fails *)
(!e se0 s0.
     (!se s. ~(apply_se (se0, s0) (se, s))) /\
     ~is_null_se se0 /\ ~(e = UndefinedExpr)
   ==>
     ^mng (mExpr e se0) s0 (s0, ev UndefinedExpr se0))

   /\

(* RULE-ID: comma-progresses *)
(!e1 e2 se s0.
     final_value (mExpr e1 se)
   ==>
     ^mng (mExpr (CommaSep e1 e2) se) s0 (s0, ev (RValreq e2) base_se))

   /\

(* RULE-ID: binop-fails *)
(!f v1 type1 v2 type2 se0 s.
     (!res restype. ~binop_meaning s f v1 (strip_const type1)
                                       v2 (strip_const type2)
                                       res restype)
   ==>
     ^mng (mExpr (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se0) s
          (s, ev UndefinedExpr se0))

   /\

(* RULE-ID: binop-computes *)
(!s f v1 type1 v2 type2 res restype se.
     binop_meaning s f v1 (strip_const type1)
                       v2 (strip_const type2)
                       res restype
   ==>
      ^mng (mExpr (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se) s
           (s, ev (ECompVal res restype) se))

   /\

(* RULE-ID: unop-computes *)
(!s f ival t result rt se.
     unop_meaning f ival (strip_const t) result rt
   ==>
     ^mng (mExpr (CApUnary f (ECompVal ival t)) se) s
          (s, ev (ECompVal result rt) se))

   /\

(* RULE-ID: unop-fails *)
(!s0 se0 f ival t.
     (!res rt. ~(unop_meaning f ival (strip_const t) res rt))
   ==>
     ^mng (mExpr (CApUnary f (ECompVal ival t)) se0) s0
          (s0, ev UndefinedExpr se0))

   /\

(* RULE-ID: and-false *)
(!v t se s sub2.
     is_zero t v
   ==>
     ^mng (mExpr (CAnd (ECompVal v t) sub2) se) s
          (s, ev (ECompVal (signed_int 0) (Signed Int)) se))

   /\

(* RULE-ID: and-true *)
(!v t se s sub2.
     ~is_zero t v /\ is_null_se se
   ==>
     ^mng (mExpr (CAnd (ECompVal v t) sub2) se) s
          (s, ev (CApUnary CNot (CApUnary CNot sub2)) base_se))

   /\

(* RULE-ID: or-true *)
(!v t sub2 se s.
     ~is_zero t v
   ==>
     ^mng (mExpr (COr (ECompVal v t) sub2) se) s
          (s, ev (ECompVal (signed_int 1) (Signed Int)) se))

   /\

(* RULE-ID: or-false *)
(!v t sub2 se s.
     is_zero t v /\ is_null_se se
   ==>
     ^mng (mExpr (COr (ECompVal v t) sub2) se) s
          (s, ev (CApUnary CNot (CApUnary CNot sub2)) base_se))

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
     ^mng (mExpr (CCond (ECompVal v t) e2 e3) se) s (s, ev resexpr base_se))

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
     ^mng (mExpr (CCond (ECompVal v t) e2 e3) se) s
          (s, ev resexpr base_se))

   /\

(* RULE-ID: deref-objptr *)
(* 5.3.1 p1 - pointer to an object type *)
(!mval t t' se s addr pth.
     object_type t /\ (SOME mval = ptr_encode s addr t' pth) /\
     (static_type (t',pth) = t)
   ==>
     ^mng (mExpr (Deref (ECompVal mval (Ptr t))) se) s
          (s, ev (LVal addr t' pth) se))

   /\

(* RULE-ID: deref-objptr-fails *)
(!mval t se s.
     object_type t /\
     ((!addr t' p. ~(SOME mval = ptr_encode s addr t' p)) \/
      (?t' p. SOME mval = ptr_encode s 0 t' p))
   ==>
     ^mng (mExpr (Deref (ECompVal mval (Ptr t))) se) s
          (s, ev UndefinedExpr se))

   /\

(* RULE-ID: deref-fnptr *)
(* 5.3.1 p1 - pointer to a function type *)
(!v retty argtys se s.
     v IN FDOM s.fndecode
   ==>
     ^mng (mExpr (Deref (ECompVal v (Ptr (Function retty argtys)))) se) s
          (s, ev (FVal (s.fndecode ' v) (Function retty argtys) NONE) se))

   /\

(* RULE-ID: addr-lvalue *)
(* See 5.3.1 p2-5 - taking the address of an lvalue *)
(*   TODO: taking the address of a qualified-id, thereby generating
                a pointer to member *)
(!a t pth se s result.
     (SOME result = ptr_encode s a t pth)
   ==>
     ^mng (mExpr (Addr (LVal a t pth)) se) s
           (s, ev (ECompVal result (Ptr (static_type (t,pth)))) se))

   /\

(* RULE-ID: mem-addr-static-nonfn *)
(* 5.3.1 p2 if the address is taken of a qualified-ident that is actually a
   static member, then a normal address is generated.
   As it's an object type, it must be an SFName.
*)
(!cname cenv fldname se s addr ty cinfo prot pth ptrval userdefs.
     cname IN defined_classes s /\
     object_type ty /\
     (lookup_class s cname = SOME cenv) /\
     ((item cenv).info = SOME (cinfo, userdefs)) /\
     MEM (FldDecl fldname ty, T, prot) cinfo.fields /\
     (lookup_addr s (mk_member cname (SFName fldname)) = SOME (addr, pth)) /\
     (SOME ptrval = ptr_encode s addr ty pth)
   ==>
     ^mng (mExpr (MemAddr cname (SFName fldname)) se) s
          (s, ev (ECompVal ptrval (Ptr ty)) se))

   /\

(* RULE-ID: assign-op-assign *)
(* This rule turns an operator-assignment into a normal assignment, which is
   possible once the LHS has been evaluated into an l-value *)
(!f n t p e se0 s0.
     T
   ==>
     ^mng (mExpr (Assign (SOME f) (LVal n t p) e) se0) s0
          (s0, ev (Assign NONE
                          (LVal n t p)
                          (CApBinary f (LVal n t p) e)) se0))

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
     ^mng (mExpr (Assign NONE (LVal a lhs_t []) (ECompVal v0 t0)) se0)
          s (s, ev resv se))

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
     ^mng (mExpr (PostInc (LVal a t [])) se0) s (s, ev resv se))

   /\

(* RULE-ID: postinc-fails-inc-or-initialised *)
(!a t se0 sz s v.
     sizeof T (sizeofmap s) t sz /\ ~class_type t /\
     (v = mem2val s a sz) /\
     ((!nv1 t'.
         ~binop_meaning s CPlus v t (signed_int 1) (Signed Int) nv1 t') \/
     ~(range_set a sz SUBSET s.initmap))
   ==>
     ^mng (mExpr (PostInc (LVal a t [])) se0) s (s, ev UndefinedExpr se0))

   /\

(* RULE-ID: non-static-data-member-field-selection *)
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
     s |- path (LAST p) to cnm2 via p' /\
     s |- LAST p' has least (IDtl fldid) -: (ty, F) via [LAST p'] /\
     object_type ty /\
     (mdp = (cnm1 = cnm2) /\ (p = [cnm1])) /\
     is_qualified fldid /\
     (class_part fldid = cnm2) /\
     (SOME offn = lookup_offset s mdp fldid)
   ==>
     ^mng (mExpr (SVar (LVal a (Class cnm1) p) fldid) se) s
          (s, ev (LVal (a + subobj_offset s (cnm1, p ^ p') + offn) ty
                       (default_path ty)) se))

   /\

(* RULE-ID: static-data-member-field-selection *)
(!s se cnm1 p p' fldid ty a statpath.
     s |- path (LAST p) to (class_part fldid) via p' /\
     s |- LAST p' has least (IDtl fldid) -: (ty, T) via [LAST p'] /\
     (lookup_addr s fldid = SOME (a, statpath))
   ==>
     ^mng (mExpr (SVar (LVal a (Class cnm1) p) fldid) se) s
          (s, ev (LVal a ty statpath) se))

   /\

(* RULE-ID: nonstatic-function-member-select *)
(* this is very similar to the above, because this is a non-virtual function
   that is being looked up.  We can tell it's not virtual because the
   identifier is structured (making the call to class_part well-formed) *)
(!se s a fldid ftype Cs Ds cnm retty ps body.
     s |- path (LAST Cs) to class_part fldid via Ds /\
     s |- LAST Ds has least method (IDtl fldid) -: (retty,F,ps,body)
            via [LAST Ds] /\
     (ftype = Function retty (MAP SND ps)) /\
     is_qualified fldid
   ==>
     ^mng (mExpr (SVar (LVal a (Class cnm) Cs) fldid) se) s
          (s, ev (FVal fldid ftype (SOME (LVal a (Class cnm) (Cs ^ Ds)))) se))

   /\

(* RULE-ID: static-function-member-select *)
(!se s a fldid ftype Cs Ds cnm retty ps body.
     s |- path (LAST Cs) to class_part fldid via Ds /\
     s |- LAST Ds has least method (IDtl fldid) -: (retty,T,ps,body)
            via [LAST Ds] /\
     (ftype = Function retty (MAP SND ps)) /\
     is_qualified fldid
   ==>
     ^mng (mExpr (SVar (LVal a (Class cnm) Cs) fldid) se) s
          (s, ev (FVal fldid ftype NONE) se))

   /\

(* RULE-ID: virtual-function-member-select *)
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
     s |- LAST Cs has least method
             (SFName fld) -: (static_retty,F,args0,body0) via Ds /\
     s |- (C,Cs ^ Ds) selects (SFName fld) -: (dyn_retty,F,args,body) via Cs'
   ==>
     ^mng (mExpr (SVar (LVal a (Class C) Cs)
                       (IDConstant F [] (SFName fld))) se) s
          (s, ev (FVal (mk_member (LAST Cs') (SFName fld))
                       (Function dyn_retty (MAP SND args))
                       (SOME (LVal a (Class C) Cs')))
                 se))

   /\

(* RULE-ID: function-call-sqpt *)
(!fnid fty retty argtys eopt params se s.
     (fty = Function retty argtys) /\
     EVERYi (\i e. if ref_type (EL i argtys) then ?a t p. e = LVal a t p
                   else ?v t. e = ECompVal v t)
            params /\
     is_null_se se
   ==>
     ^mng (mExpr (FnApp (FVal fnid fty eopt) params) se) s
          (s, ev (FnApp_sqpt (FVal fnid fty eopt) params) base_se))

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
     ^mng (mExpr (New ty NONE) se) s0
          (s, mExpr (ECompVal ptrval (Ptr result_ty)) se))

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
     ^mng (mExpr (New ty (SOME args)) se) s0
          (s, mExpr (CommaSep (FnApp (ConstructorFVal T F a cnm) args)
                              (ECompVal ptrval (Ptr ty)))
                    se))

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
     ^mng (mExpr (FnApp (ConstructorFVal mdp subp a cnm) params) se) s
          (s, ev (FnApp_sqpt (ConstructorFVal mdp subp a cnm) params) base_se))

   /\

(* RULE-ID: function-ptr-to-function-lval *)
(* 5.2.2 p1 - this rule handles the situation where the postfix-expression
   is a pointer to a function value *)
(!v retty argtys args se s.
     v IN FDOM s.fndecode
   ==>
     ^mng (mExpr (FnApp (ECompVal v (Ptr (Function retty argtys))) args) se) s
          (s, ev (FnApp (FVal (s.fndecode ' v)
                               (Function retty argtys)
                               NONE)
                         args) se))

   /\

(* RULE-ID: global-function-call *)
(* the NONE as FVal's third argument means this is a global function *)
(* TODO: handle return type casting *)
(!ftype args pdecls params se s0 fnid rtype body.
     (find_best_fnmatch s0 fnid (MAP valuetype args) rtype params body) /\
     (pdecls = MAP (\ ((n,ty),a). VDecInit ty
                                           (Base n)
                                           (CopyInit (mExpr a base_se)))
                   (ZIP (params, args)))
   ==>
     ^mng (mExpr (FnApp_sqpt (FVal fnid ftype NONE) args) se) s0
          (s0, EStmt (Block F pdecls [body]) (return_cont se rtype)))

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
                                           (CopyInit (mExpr a base_se)))
                   (ZIP (params, args))) /\
     (SOME this = ptr_encode s0 a (Class cname) p)
   ==>
     ^mng (mExpr (FnApp_sqpt (FVal fnid ftype (SOME (LVal a (Class cname) p)))
                             args) se0)
          s0
          (s0 with <| stack updated_by (CONS (s0.env, s0.thisvalue));
                      thisvalue := SOME (ECompVal this (Ptr (Class cname)));
                      blockclasses updated_by stackenv_newscope ;
                      exprclasses updated_by stackenv_newscope
                   |>,
           EStmt (Block T pdecls [body]) (return_cont se0 rtype)))

   /\

(* RULE-ID: constructor-function-call *)
(!cnm mdp subp pdecls a args se0 params s0 mem_inits this body cpfx.
     find_constructor_info s0 cnm args params mem_inits body /\
     (pdecls = MAP (\ ((n,ty),a). VDecInit ty
                                           (Base n)
                                           (CopyInit (mExpr a base_se)))
                   (ZIP (params, args))) /\
     (SOME this = ptr_encode s0 a (Class cnm) [cnm]) /\
     (cpfx = construct_ctor_pfx s0 mdp a cnm mem_inits)
   ==>
     ^mng (mExpr (FnApp_sqpt (ConstructorFVal mdp subp a cnm) args) se0)
          s0
          (s0 with <| thisvalue := SOME (ECompVal this (Ptr (Class cnm))) ;
                      stack updated_by (CONS (s0.env, s0.thisvalue)) ;
                      blockclasses updated_by stackenv_newscope ;
                      exprclasses updated_by stackenv_newscope |>,
           EStmt (Block T (pdecls ++ cpfx) [body])
                 (RVC (\e. ConstructedVal subp a cnm) se0)))

   /\

(* RULE-ID: function-application-lval2rval *)
(!f pfx e0 e sfx se0 se s0 s.
     lval2rval (s0,e0,se0) (s,e,se) /\
     fn_expects_rval s0
                     (case s0.thisvalue of
                         SOME (ECompVal bytes (Ptr ty)) -> SOME ty
                      || _ -> NONE)
                     f
                     (LENGTH pfx)
   ==>
     ^mng (mExpr (FnApp f (pfx ++ (e0 :: sfx))) se0) s0
          (s, mExpr (FnApp f (pfx ++ (e :: sfx))) se))

   /\

(* RULE-ID: return-eval-under *)
(!exte0 exte s1 s2 c.
     ^mng exte0 s1 (s2, exte)
   ==>
     ^mng (mStmt (Ret exte0) c) s1 (s2, mStmt (Ret exte) c))

   /\

(* RULE-ID: return-lval2rval *)
(!e0 se0 s0 e se ret_se s c.
     lval2rval (s0,e,se0) (s,e,se)
   ==>
     ^mng (mStmt (Ret (NormE e0 se0)) (RVC c ret_se)) s0
          (s, mStmt (Ret (NormE e se)) (RVC c ret_se)))

   /\

(* RULE-ID: return-rvalue *)
(* all recursive stmt rules require RHS of reduction to still be
   an mStmt, preventing this rule from firing at depth.  Note that
   class r-values can't be returned from this rule as class values are
   never represented with ECompVals. *)
(!v t s se0 se c.
     is_null_se se0
   ==>
     ^mng (mStmt (Ret (NormE (ECompVal v t) se0)) (RVC c se)) s
          (s, mExpr (c (ECompVal v t)) se))

   /\

(* RULE-ID: return-lvalue *)
(!a t p se0 se c s.
     is_null_se se0
   ==>
     ^mng (mStmt (Ret (NormE (LVal a t p) se0)) (LVC c se)) s
          (s, mExpr (c (LVal a t p)) se))

   /\

(* RULE-ID: return-exception *)
(!e c s.
     is_exnval e
   ==>
     ^mng (mStmt (Ret e) c) s (s, mk_exn e c))

   /\

(* RULE-ID: empty-ret *)
(!s c.
     T
   ==>
     ^mng (mStmt EmptyRet c) s
          (s, mStmt (Ret (NormE (ECompVal [] Void) base_se)) c))

   /\

(* RULE-ID: empty-stmt-empty-ret *)
(!s c se.
     T
   ==>
     ^mng (mStmt EmptyStmt (RVC c se)) s
          (s, mExpr (c (ECompVal [] Void)) se))

   /\

(* RULE-ID: trap-stmt-evaluation *)
(* statements evaluate as normal under Traps *)
(!tt st st' c s0 s.
     ^mng (mStmt st c) s0 (s, mStmt st' c)
   ==>
     ^mng (mStmt (Trap tt st) c) s0 (s, mStmt (Trap tt st') c))

   /\

(* RULE-ID: catch-stmt-evaluation *)
(* statements evaluate normally under catch *)
(!st c s0 s st' hnds.
     ^mng (mStmt st c) s0 (s, mStmt st' c)
   ==>
     ^mng (mStmt (Catch st hnds) c) s0 (s, mStmt (Catch st' hnds) c))

   /\

(* RULE-ID: throw-expr-evaluation *)
(* expressions evaluate under throw *)
(!e0 e s0 s c.
     ^mng (RVR e0) s0 (s, RVR e)
   ==>
     ^mng (mStmt (Throw (SOME e0)) c) s0 (s, mStmt (Throw (SOME e)) c))

   /\

(* RULE-ID: throw-expr-exception *)
(* the expression being evaluated may itself cause an exception *)
(!e c s.
     is_exnval e
   ==>
     ^mng (mStmt (Throw (SOME e)) c) s (s, mk_exn e c))

   /\

(* RULE-ID: bare-throw-succeeds *)
(!s0 e es c.
     (s0.current_exns = e::es)
   ==>
     ^mng (mStmt (Throw NONE) c) s0
          (s0 with current_exns := es,
           mStmt (Throw (SOME (mExpr e base_se))) c))

   /\

(* RULE-ID: bare-throw-fails *)
(!s0 ct.
     (s0.current_exns = [])
   ==>
     ^mng (mStmt (Throw NONE) ct) s0
          (s0, mStmt (Standalone (mExpr ^callterminate base_se)) ct))

   /\

(* RULE-ID: clear-exn *)
(!s0 c e es.
     (s0.current_exns = e::es)
   ==>
     ^mng (mStmt ClearExn c) s0
          (s0 with current_exns := es, mStmt EmptyStmt c))

   /\

(* RULE-ID: catch-stmt-empty-hnds *)
(* you wouldn't expect to see this form input (in fact, it is syntactically
   impossible), but it can arise as syntax evolves (successive handlers are
   tried and found not to match the type of the exception value)
*)
(!st c s0.
     T
   ==>
     ^mng (mStmt (Catch st []) c) s0 (s0, mStmt st c))

   /\

(* RULE-ID: catch-normal-stmt-passes *)
(!st hnds c s0.
     final_stmt st c /\
     ~exception_stmt st
   ==>
     ^mng (mStmt (Catch st hnds) c) s0 (s0, mStmt st c))

   /\

(* RULE-ID: catch-all *)
(!exn e hnd_body rest c s0.
     (exn = SOME (mExpr e base_se))
   ==>
     ^mng (mStmt (Catch (Throw exn) ((NONE, hnd_body) :: rest)) c) s0
          (s0 with current_exns updated_by (CONS e),
           mStmt (Block F [] [hnd_body; ClearExn]) c))

   /\

(* RULE-ID: catch-specific-type-matches *)
(* NOTE: relying on the fact that no user program can generate " no name " as
   the name of an identifier *)
(!exn e hnd_body rest c s0 pty pnameopt pname.
     (exn = SOME (mExpr e base_se)) /\
     exception_parameter_match s0 pty (value_type e) /\
     (pname = case pnameopt of SOME s -> Base s || NONE -> (Base " no name "))
   ==>
     ^mng (mStmt (Catch (Throw exn) ((SOME(pnameopt, pty), hnd_body) :: rest)) c)
          s0
          (s0 with current_exns updated_by (CONS e),
           mStmt (Block F [VDecInit pty
                                    pname
                                    (CopyInit (mExpr e base_se))]
                          [hnd_body; ClearExn]) c))

   /\

(* RULE-ID: catch-specific-type-nomatch *)
(!exn e hnd_body rest c s0 pty pnameopt.
     (exn = SOME (mExpr e base_se)) /\
     ~exception_parameter_match s0 pty (value_type e)
   ==>
     ^mng (mStmt (Catch (Throw exn) ((SOME(pnameopt, pty), hnd_body) :: rest)) c)
          s0
          (s0, mStmt (Catch (Throw exn) rest) c))

   /\


(* final cases for Traps.  *)
(* RULE-ID: trap-break-catches *)
(!c s0.
     T
   ==>
     ^mng (mStmt (Trap BreakTrap Break) c) s0 (s0, mStmt EmptyStmt c))

   /\

(* RULE-ID: trap-continue-catches *)
(!c s0.
     ^mng (mStmt (Trap ContTrap Cont) c) s0 (s0, mStmt EmptyStmt c))

   /\

(* RULE-ID: trap-continue-passes-break *)
(!c s0.
     T
   ==>
     ^mng (mStmt (Trap ContTrap Break) c) s0 (s0, mStmt Break c))

   /\

(* RULE-ID: trap-break-passes-continue *)
(!c s0.
     T
   ==>
     ^mng (mStmt (Trap BreakTrap Cont) c) s0 (s0, mStmt Cont c))

   /\

(* RULE-ID: trap-emptystmt-passes *)
(!c tt s0.
     T
   ==>
     ^mng (mStmt (Trap tt EmptyStmt) c) s0 (s0, mStmt EmptyStmt c))

   /\

(* RULE-ID: trap-ret-passes *)
(!c tt v t se s0.
     is_null_se se
   ==>
     ^mng (mStmt (Trap tt (Ret (NormE (ECompVal v t) se))) c) s0
          (s0, mStmt (Ret (NormE (ECompVal v t) se)) c))

   /\

(* RULE-ID: trap-exn-passes *)
(!tt exn c s.
     exception_stmt exn
   ==>
     ^mng (mStmt (Trap tt exn) c) s (s, mStmt exn c))

   /\

(* RULE-ID: standalone-evaluates *)
(!exte c s1 s2 exte'.
     ^mng (RVR exte) s1 (s2, RVR exte')
   ==>
     ^mng (mStmt (Standalone exte) c) s1 (s2, mStmt (Standalone exte') c))

   /\

(* RULE-ID: standalone-finishes *)
(!v t se c s.
     is_null_se se
   ==>
     ^mng (mStmt (Standalone (NormE (ECompVal v t) se)) c) s
          (s, mStmt EmptyStmt c)) /\

(* RULE-ID: standalone-exception *)
(!e c s.
     is_exnval e
   ==>
     ^mng (mStmt (Standalone e) c) s (s, mk_exn e c))

   /\

(* RULE-ID: if-eval-guard *)
(!guard guard' c t e s0 s.
     ^mng (RVR guard) s0 (s, RVR guard')
   ==>
     ^mng (mStmt (CIf guard t e) c) s0 (s, mStmt (CIf guard' t e) c))

   /\

(* RULE-ID: if-true *)
(!v t se thenstmt elsestmt c s.
     scalar_type t /\ is_null_se se /\ ~is_zero t v
   ==>
     ^mng (mStmt (CIf (NormE (ECompVal v t) se) thenstmt elsestmt) c) s
          (s, mStmt thenstmt c))

   /\

(* RULE-ID: if-false *)
(!v t se thenstmt elsestmt c s.
     scalar_type t /\ is_null_se se /\ is_zero t v
   ==>
     ^mng (mStmt (CIf (NormE (ECompVal v t) se) thenstmt elsestmt) c) s
          (s, mStmt elsestmt c))

   /\

(* RULE-ID: if-exception *)
(!guard thenstmt elsestmt c s.
     is_exnval guard
   ==>
     ^mng (mStmt (CIf guard thenstmt elsestmt) c) s
          (s, mk_exn guard c))

   /\

(* RULE-ID: loop *)
(* somewhat ugly that a bunch of blocks will accumulate around every
   iteration of the loop... *)
(!guard bdy c s.
     T
   ==>
     ^mng (mStmt (CLoop guard bdy) c) s
          (s, mStmt (CIf guard (Block F [] [bdy; CLoop guard bdy])
                               EmptyStmt) c))

   /\

(* RULE-ID: block-entry *)
(!vds sts s c.
     T
   ==>
     ^mng (mStmt (Block F vds sts) c) s
          (s with <| stack updated_by (CONS (s.env, s.thisvalue));
                     blockclasses updated_by stackenv_newscope ;
                     exprclasses updated_by stackenv_newscope |>,
           mStmt (Block T vds sts) c))

   /\

(* RULE-ID: block-exit-destructors-to-call *)
(* normally constructed objects at this level are always destroyed here *)
(!s0 s c st  bcs destroy_these destcalls.
     (s0.blockclasses = destroy_these :: bcs) /\ ~(destroy_these = []) /\
     final_stmt st c /\
     ((destcalls, s) = realise_destructor_calls (exception_stmt st) s0)
   ==>
     ^mng (mStmt (Block T [] [st]) c) s0
          (s, mStmt (Block T [] (destcalls ++ [st])) c))

   /\

(* RULE-ID: destructor-call *)
(!a p se0 s0 this cnm body.
     (cnm = LAST p) /\ is_null_se se0 /\
     (SOME this = ptr_encode s0 a (Class cnm) [cnm]) /\
     find_destructor_info s0 cnm body
   ==>
     ^mng (mExpr (DestructorCall a cnm) se0)
          s0
          (s0 with <| stack updated_by (CONS (s0.env, s0.thisvalue));
                      thisvalue := SOME (ECompVal this (Ptr (Class cnm)))
                   |>,
           EStmt body (return_cont se0 Void)))

   /\

(* RULE-ID: block-exit *)
(!st s c env stk' this bcs ecs.
     (s.stack = (env,this) :: stk') /\ final_stmt st c /\
     (s.blockclasses = []::bcs) /\
     (s.exprclasses = []::ecs)
   ==>
     ^mng (mStmt (Block T [] [st]) c) s
          (s with <| stack := stk';
                     env := env;
                     thisvalue := this;
                     blockclasses := bcs;
                     exprclasses := ecs |>,
           mStmt st c))

   /\

(* RULE-ID: block-emptystmt *)
(!sts s c.
     ~(sts = [])
   ==>
     ^mng (mStmt (Block T [] (EmptyStmt::sts)) c) s
          (s, mStmt (Block T [] sts) c))

   /\

(* RULE-ID: block-interrupted *)
(!sts exstmt s c.
     final_stmt exstmt c /\ ~(exstmt = EmptyStmt) /\ ~(sts = [])
   ==>
     ^mng (mStmt (Block T [] (exstmt::sts)) c) s
          (s, mStmt (Block T [] [exstmt]) c))

   /\

(* RULE-ID: block-stmt-evaluate *)
(!st st' sts c s0 s.
     ^mng (mStmt st c) s0 (s, mStmt st' c)
   ==>
     ^mng (mStmt (Block T [] (st :: sts)) c) s0
          (s, mStmt (Block T [] (st' :: sts)) c))

   /\

(* RULE-ID: block-declmng *)
(!s0 s d0 ds vds sts c.
     declmng ^mng (d0, s0) (ds, s)
   ==>
     ^mng (mStmt (Block T (d0 :: vds) sts) c) s0
          (s, mStmt (Block T (ds ++ vds) sts) c))

   /\

(* RULE-ID: block-declmng-exception *)
(!d0 s0 s f e ex ty loc c c' sts vds.
     ((f = CopyInit) \/ (f = DirectInit)) /\
     declmng ^mng (d0, s0) ([VDecInitA ty loc (f e)], s) /\
     is_exnval e /\
     (e = mStmt (Throw (SOME ex)) c')
   ==>
     ^mng (mStmt (Block T (d0 :: vds) sts) c) s0
          (s, mStmt (Block T [] [Throw (SOME ex)]) c))

   /\

(* RULE-ID: block-vstrdec *)
(* this is the declaration of a local class *)
(!name info0 info userdefs s0 s vds sts c env'.
     ((info,userdefs) = define_default_specials info0) /\
     install_member_functions name s0 info.fields s /\
     ~is_abs_id name /\
     (SOME env' = update_class name (info,userdefs) s.env)
   ==>
     ^mng (mStmt (Block T (VStrDec name (SOME info0) :: vds) sts) c) s0
          (s with env := env', mStmt (Block T vds sts) c))
`


val _ = export_theory();



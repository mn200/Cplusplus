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
open aggregatesTheory
local open side_effectsTheory statesTheory operatorsTheory in end

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
      (f IN  {Addr; Deref; CAndOr_sqpt; PostInc; RValreq}) \/
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

(* mark_ref checks whether or not we're trying to read something that has been
   updated *)
(* class objects don't turn into rvalues - this changes the way that
   things happen when class/struct values are returned from objects, but
   shouldn't make much difference otherwise. *)
val lval2rval_def = Define`
  lval2rval (s0,e0,se0) (s,e,se) =
       (s0 = s) /\
       ?n t p.
          (e0 = LVal n t p) /\
             (~array_type t /\ (!cn. ~(t = Class cn)) /\
              (?sz. sizeof T (sizeofmap s0) t sz /\
                    (mark_ref n sz se0 se /\
                     range_set n sz SUBSET s0.initmap /\
                     (e = ECompVal (mem2val s0 n sz) t) \/
                     (~(range_set n sz SUBSET s0.initmap) \/
                      (!se'. ~(mark_ref n sz se0 se'))) /\
                     (se = se0) /\ (e = UndefinedExpr)))
          \/
              (?sz t' bytes.
                  (t = Array t' sz) /\ (se0 = se) /\
                  (SOME bytes = ptr_encode (s,t') (n, default_path t')) /\
                  (e = ECompVal bytes (Ptr t'))))
`

(* SANITY *)
val lval2rval_states_equal = store_thm(
  "lval2rval_states_equal",
  ``!s0 ese0 s ese. lval2rval (s0,ese0) (s,ese) ==> (s0 = s)``,
  SIMP_TAC (srw_ss()) [lval2rval_def,pairTheory.FORALL_PROD]);

(* SANITY *)
val update_map_over_lval2rval = store_thm(
  "update_map_over_lval2rval",
  --`!s0 e0 se0 s e se. lval2rval (s0,e0,se0) (s,e,se) ==>
                        (se0.update_map = se.update_map)`--,
  SRW_TAC [][lval2rval_def] THEN
  FULL_SIMP_TAC (srw_ss()) [side_effectsTheory.mark_ref_def])

(* SANITY *)
val lval2rval_det = store_thm(
  "lval2rval_det",
  ``!se0 s0 e0 se s e.
       lval2rval (s0, e0, se0) (s, e, se) ==>
       !se' s' e'.
          lval2rval (s0, e0, se0) (s', e', se') ==>
          (s' = s) /\ (e' = e) /\ (se' = se)``,
  SRW_TAC [][lval2rval_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [sizeof_det, TypeBase.one_one_of ``:'a option``,
             side_effectsTheory.mark_ref_det])

(* SANITY *)
val lval2rval_is_lval = store_thm(
  "lval2rval_is_lval",
  ``!s0 e0 se0 X.
      lval2rval (s0, e0, se0) X ==> ?n t p. e0 = LVal n t p``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [lval2rval_def, pairTheory.FORALL_PROD])

(* SANITY *)
val lval2rval_ecompval = store_thm(
  "lval2rval_ecompval",
  ``!s0 v t se0 X. ~(lval2rval (s0, ECompVal v t, se0) X)``,
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, CExpr_distinct,
                       lval2rval_def]);

(* SANITY *)
val lval2rval_results = store_thm(
  "lval2rval_results",
  ``!X s e se. lval2rval X (s,e,se) ==>
               (?v t. e = ECompVal v t) \/ (e = UndefinedExpr)``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [pairTheory.FORALL_PROD, lval2rval_def])

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
        (f IN  {Deref; CAndOr_sqpt; RValreq}) \/
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

(* malloc s0 ty a is true if a is a valid address for a value of type ty,
   and is currently unallocated.

   If you are malloc-ing space for a class, then it will be for a most-derived
   class, which is they there are T's passed to sizeof and align. *)
val malloc_def = Define`
  malloc s0 ty a =
     ?sz aln. sizeof T (sizeofmap s0) ty sz /\
              align (sizeofmap s0) T ty aln /\
              DISJOINT s0.allocmap (range_set a sz) /\
              ~(a = 0) /\ (a MOD aln = 0) /\
              a + sz <= 2 EXP (CHAR_BIT * ptr_size ty)
`

val parameter_coerce_def = Define`
  parameter_coerce (v1,ty1) (v2,ty2) =
    (integral_type ty1 /\ integral_type ty2 \/
     (?ty0. {ty1; ty2} = {Ptr Void; Ptr ty0})) /\
    (?i. (INT_VAL ty1 v1 = SOME i) /\
         (SOME v2 = REP_INT ty2 i))
       \/
    (ty1 = ty2) /\ (v1 = v2)
`;


(* installs values into memory *)
val rec_i_params_def = Define`
    (rec_i_params s0 [] vallist s = (vallist = []) /\ (s0 = s)) /\
    (rec_i_params s0 ((pname, ptype) :: ptl) vallist s =
       (?a n vval vtype newval vtl rs.
          ~ref_type ptype /\
          (vallist = ECompVal vval vtype :: vtl) /\
          parameter_coerce (vval, vtype) (newval, ptype) /\
          sizeof T (sizeofmap s0) ptype n /\ malloc s0 ptype a /\
          (rs = range_set a n) /\
          rec_i_params
            (val2mem (s0 with
                        <| varmap updated_by
                              (\v. v |+ (Base pname,
                                         (a, default_path ptype))) ;
                           typemap updated_by (\t. t |+ (Base pname, ptype));
                           allocmap updated_by ((UNION) rs);
                           initmap updated_by ((UNION) rs) |>)
                     a
                     newval)
            ptl vtl s) \/
       (?a ty p vtl.
          (vallist = LVal a ty p :: vtl) /\ (ptype = Ref ty) /\
          rec_i_params
            (s0 with <| varmap updated_by (\v. v |+ (Base pname, (a, p)));
                        typemap updated_by (\t. t |+ (Base pname, ty)) |>)
            ptl vtl s))
`;

val pass_parameters_def = Define`
  pass_parameters s0 fnid pv s =
      rec_i_params s0 ((s0.fnmap ' fnid).parameters) pv s
`;

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
val imemfn_def = Define`
  (imemfn cnm s0 [] s = (s0 = s)) /\
  (imemfn cnm s0 ((FldDecl nm ty, b, p) :: rest) s = imemfn cnm s0 rest s) /\
  (imemfn cnm s0 ((CFnDefn retty nm params body, statp, p) :: rest) s =
     if statp then
       ?s' fval. installfn s0 Ptr retty (Member cnm nm) params body fval s' /\
                 imemfn cnm s' rest s
     else
       ?s' fval. installfn s0 (MPtr cnm) retty (Member cnm nm) params body
                           fval
                           s' /\
                 imemfn cnm s' rest s) /\
  (imemfn cnm s0 ((Constructor _ _ _, _, _) :: rest) s =
     imemfn cnm s0 rest s) /\
  (imemfn cnm s0 ((Destructor _, b, p) :: rest) s = imemfn cnm s0 rest s)
`

val install_member_functions_def =
    overload_on ("install_member_functions", ``imemfn``)

(* declaration only.  See
     - 12.1 p5 for constructors
     - 12.8 p4-5 for copy constructors
     - 12.8 p10 for copy assignment constructors
     - 12.4 p3 for destructors
             - AMBIGUITY: no spec in standard of what body of implicitly
                          defined destructor should do
*)
(* this declares default special members too *)
val declare_default_specials_def = Define`
  define_default_specials info0 =
    let constructor (i0,set) =
      if (?ps mems bdy statp prot.
            MEM (Constructor ps mems bdy, statp, prot) i0.fields)
      then (i0, DefaultConstructor INSERT set)
      else (i0 with fields updated_by
                      CONS (Constructor [] [] NONE, F, Public),
            set) in
    let destructor (i0,set) =
      if (?bdy statp prot. MEM (Destructor bdy, statp, prot) i0.fields) then
        (i0,Destructor INSERT set)
      else (i0 with fields updated_by CONS (Destructor NONE, F, Public),
            set)
    in
      constructor (destructor (info0, {}))
`




val _ = overload_on ("mExpr", ``statements$NormE``)
val _ = overload_on ("mStmt", ``statements$EStmt``)

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

val final_stmt_def = Define`
  (final_stmt EmptyStmt = T) /\
  (final_stmt Break = T) /\
  (final_stmt Cont = T) /\
  (final_stmt (Ret e) =
     ?v t se. (e = NormE (ECompVal v t) se) /\ is_null_se se) /\
  (final_stmt _ = F)
`;

val final_value_def = Define`
  (final_value (mExpr e se) = ?v t. (e = ECompVal v t) /\ is_null_se se) /\
  (final_value (mStmt s c) = F)
`;

val vdeclare_def = Define`
  vdeclare s0 ty nm s =
     (?a sz rs.
         (rs = range_set a sz) /\
         object_type ty /\ malloc s0 ty a /\ sizeof T (sizeofmap s) ty sz /\
         (s = s0 with <| allocmap updated_by (UNION) rs;
                          varmap updated_by
                             (\vm. vm |+ (nm,(a,default_path ty)));
                          typemap updated_by (\tm. tm |+ (nm,ty)) |>))
        \/
     (function_type ty /\
      (s = s0 with typemap updated_by (\tm. tm |+ (nm, ty))))
        \/
     (?ty0.
        (ty = Ref ty0) /\
        (* before the reference gets initialised, what should its value be?
           Or, what does an uninitialised reference what look like?
           Certainly, references must be initialised by valid objects, so
           attempting
              int &y = y ;
           must be bad.  So, let's make it a reference to a guaranteed bad
           address, 0.  We can't just leave the varmap unchanged as
           the declaration of a variable masks other variables of the same
           name.  See notes/ref001.cpp *)
        (s = s0 with
             <| varmap updated_by (\vm. vm |+ (nm, (0, default_path ty0)));
                typemap updated_by (\tm. tm |+ (nm, ty0)) |>))

`;

val copy2globals_def = Define`
  copy2globals s = (s with <| gclassmap := s.classmap;
                              gtypemap := s.typemap;
                              gvarmap := s.varmap |>)
`;

(* true if the nth argument of f is not a reference type *)
(* TODO: deal with overloading *)
val fn_expects_rval_def = Define`
  fn_expects_rval s f n =
    ?retty args.
      (expr_type (expr_type_comps s) RValue f (Function retty args) \/
       expr_type (expr_type_comps s) RValue f (Ptr (Function retty args))) /\
      ~ref_type (EL n args)
`;

(* true if the nth argument of the constructor for cnm is not a reference
   type - the actual arguments are passed so that we have a hope of figuring
   out which actual constructor is going to get called *)
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
    ?prot.
       MEM (Destructor (SOME body), F, prot) (cinfo s0 cnm).fields
`;



val initA_constructor_call_def = Define`
  initA_constructor_call mdp cnm addr args =
      VDecInitA (Class cnm)
                (ObjPlace addr)
                (DirectInit
                   (mExpr (FnApp (ConstructorFVal mdp addr cnm) args) base_se))
`;


(* 8.5 p5 : zero-initialisation *)
(* TODO: handle unions *)
val (zero_init_rules, zero_init_ind, zero_init_cases) = Hol_reln`
   (!s mdp ty a.
     scalar_type ty
   ==>
     zero_init s mdp ty a [VDecInitA ty
                                     (ObjPlace a)
                                     (DirectInit (mExpr (Cnum 0) base_se))])

   /\

   (!s mdp ty a.
     ref_type ty
   ==>
     zero_init s mdp ty a [])

   /\

   (!s mdp cnm a sub_inits.
     listRel (\(cc,off) l. zero_init s (nsdp cc) (cc_type cc) (a + off) l)
             (init_order_offsets s mdp cnm)
             sub_inits
   ==>
     zero_init s mdp (Class cnm) a (FLAT sub_inits))

   /\

   (!s mdp ty n a sz sub_inits.
     sizeof T (sizeofmap s) ty sz /\
     listRel (\m l. zero_init s mdp ty (a + m * sz) l)
             (GENLIST I n)
             sub_inits
   ==>
     zero_init s mdp (Array ty n) a (FLAT sub_inits))
`;

(* 8.5 p5 : default-initialisation *)
(* TODO: handle unions *)
val (default_init_rules, default_init_ind, default_init_cases) = Hol_reln`
   (!s mdp cnm a.
     ~PODstruct s cnm
   ==>
     default_init s mdp (Class cnm) a [initA_constructor_call mdp cnm a []])

   /\

   (!s mdp ty n a sz sub_inits.
     sizeof T (sizeofmap s) ty sz /\
     listRel (\m l. default_init s mdp ty (a + m * sz) l)
             (GENLIST I n)
             sub_inits
   ==>
     default_init s mdp (Array ty n) a (FLAT sub_inits))

   /\

   (!s mdp ty a inits.
     ~array_type ty /\
     (!cnm. (ty = Class cnm) ==> PODstruct s cnm) /\
     zero_init s mdp ty a inits
   ==>
     default_init s mdp ty a inits)
`;

(* 8.5 p5 : value-initialisation *)
(* AMBIGUITY: (??)
    What is the order that the non-static data members and base-class
    components are initialised in?  It looks to be (literally) unspecified.
    Or should 12.6.2 p5 take precedence, though it is about
    the situation where we are inside a constructor call and looking at
    mem-initializers.  Think so.

    Similarly, it is not specified that arrays should be
    value-initialised in index order.  BUT, 12.6 does say that arrays
    of (and presumably, arrays of arrays of) class objects should be
    initialised in index order.  It is only initialisation of classes
    that can make any difference (through calls to constructors, so we
    can value-initialise all arrays in index order).

    Used in initialisation of aggregates: 8.5.1 p7 (see also 12.6.1)
    Used when a mem-initializer mentions a constituent, but doesn't pass any
    paramters (12.6.2 p3)
*)
(* TODO: handle unions *)
val (value_init_rules, value_init_ind, value_init_cases) = Hol_reln`
   (!s mdp cnm addr.
     has_user_constructor s cnm
   ==>
     value_init s mdp (Class cnm) addr
                [initA_constructor_call mdp cnm addr []])

   /\

   (!s mdp cnm a sub_inits.
     ~has_user_constructor s cnm /\
     listRel (\(cc,off) l.
                value_init s (nsdp cc) (cc_type cc) (a + off) l)
             (init_order_offsets s mdp cnm)
             sub_inits
   ==>
     value_init s mdp (Class cnm) a (FLAT sub_inits))

   /\

   (!s mdp ty n addr sz sub_inits.
     sizeof T (sizeofmap s) ty sz /\
     listRel (\n l. value_init s T ty (addr + n * sz) l)
             (GENLIST I n)
             sub_inits
   ==>
     value_init s mdp (Array ty n) addr (FLAT sub_inits))

   /\

   (!s mdp a ty inits.
     (!ty0. ~(ty = Class ty0)) /\ ~array_type ty /\
     zero_init s mdp ty a inits
   ==>
     value_init s mdp ty a inits)
`;


(* this function returns the prefix of sub-object constructor calls that must
   precede the body of a constructor, looking up mem-initialisors as
   necessary.
*)
val construct_ctor_pfx_def = Define`
  construct_ctor_pfx s mdp a cnm (mem_inits : mem_initializer list) body =
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
         case lookup nm of
           NONE -> (* 12.6.2 p4 - default initialisation *)
             [initA_constructor_call F nm (a + a') []]
        || SOME (nm',NONE) -> (* 12.6.2 p3 1st case - value initialisation *)
             (@inits. value_init s F (Class nm) (a + a') inits)
        || SOME (nm',SOME args) -> (* direct initialisation, with args as
                                      initialiser *)
             [initA_constructor_call F nm (a + a') args] in
    let bases = FLAT (MAP (\bnm. do_bases [cnm; bnm]) direct_bases) in
    let virtuals = if mdp then FLAT (MAP (\vnm. do_bases [vnm]) virt_bases)
                   else [] in
    let do_nsd (nsdname, nsdty) =
      let (c,a') = THE (FINDL (\ (c, off). c = NSD nsdname nsdty) allccs)
      in
          case lookup (Base nsdname) of
             NONE -> (* 12.6.2 p4 - default initialisation *)
               (@inits. default_init s T nsdty (a + a') inits)
          || SOME(nm', NONE) -> (* 12.6.2 p3 1st case - value initialisation *)
               (@inits. value_init s T nsdty (a + a') inits)
          || SOME(nm', SOME args) -> (* direct initialisation, with args as
                                        initialiser *)
               [initA_constructor_call T (Base nsdname) (a + a') args] in
    let nsds = FLAT (MAP do_nsd data_fields)
  in
    virtuals ++ bases ++ nsds
`;

val return_cont_def = Define`
  return_cont se ty = if ref_type ty then LVC LVal se
                      else RVC ECompVal se
`

val cont_comp_def = Define`
  (cont_comp f (RVC rc se) = RVC (\v rt. f (rc v rt)) se) /\
  (cont_comp f (LVC lc se) = LVC (\a t p. f (lc a t p)) se)
`

val RVR_def = Define`
  (RVR (mExpr e se) = mExpr (RValreq e) se) /\
  (RVR (mStmt s c) = mStmt s c)
`

val _ = print "Defining (utility) declaration relation\n"
(* this relation performs the various manipulations on declaration syntax
   that are independent of the rest of the meaning relation *)
(* TODO: handle construction of arrays of objects, which happens in order
   of increasing subscripts (see 12.6 p3) *)
val (declmng_rules, declmng_ind, declmng_cases) = Hol_reln`

(* RULE-ID: decl-vdec-nonclass *)
(!s0 ty name s.
     vdeclare s0 ty name s /\ object_type ty /\ (!cnm. ~(ty = Class cnm))
   ==>
     declmng mng vdf (VDec ty name, s0) ([], vdf s))

   /\

(* RULE-ID: decl-vdec-class *)
(* if called on to declare a class variable, then the default, argument-less
   constructor gets called *)
(!s0 name cnm.
     T
   ==>
     declmng mng vdf (VDec (Class cnm) name, s0)
             ([VDecInit (Class cnm) name (DirectInit0 [])], s0))

   /\


(* decl-vdecinit-start-evaluate rules switche from VDecInit to
   VDecInitA, reflecting allocation of space for the "object".  The
   vdeclare relation handles functions and references as well.
   Functions can't be initialised, so they won't appear here.
   References must be initialised, and the behaviour of vdeclare on
   references is to put them into the typemap, but to allocate no
   space, and to put them into the varmap at address 0.

   This is also the point where the class construction has to be recorded
   in the blockclasses stack so that destructors will get called in the
   appropriate reverse order.
*)


(* RULE-ID: decl-vdecinit-start-evaluate-direct-class *)
(!s0 ty cnm name args s1 s2 a pth.
     (ty = Class cnm) /\
     vdeclare s0 ty name s1 /\
     ((a,pth) = s1.varmap ' name) /\
     update_blockclasses s1 a cnm s2
   ==>
     declmng mng
             vdf
             (VDecInit ty name (DirectInit0 args), s0)
             ([VDecInitA ty
                         (ObjPlace a)
                         (DirectInit (mExpr
                                        (FnApp (ConstructorFVal T a cnm) args)
                                        base_se))], vdf s2))

   /\

(* RULE-ID: decl-vdecinit-start-evaluate-direct-nonclass *)
(* A direct initialisation of a non-class object is the same as a
   copy-initialisation *)
(!s0 ty name arg s a pth loc.
     (!cnm. ~(ty = Class cnm)) /\
     vdeclare s0 ty name s /\
     ((a,pth) = s.varmap ' name) /\
     (loc = if ref_type ty then RefPlace NONE name else ObjPlace a)
   ==>
     declmng mng
             vdf
             (VDecInit ty name (DirectInit0 [arg]), s0)
             ([VDecInitA ty loc (CopyInit (mExpr arg base_se))], vdf s))

   /\

(* RULE-ID: decl-vdecinit-start-evaluate-copy *)
(!s0 ty name arg s a pth loc.
     vdeclare s0 ty name s /\
     ((a,pth) = s.varmap ' name) /\
     (loc = if ref_type ty then RefPlace NONE name else ObjPlace a)
   ==>
     declmng mng
             vdf
             (VDecInit ty name (CopyInit arg), s0)
             ([VDecInitA ty loc (CopyInit arg)], vdf s))

   /\


(* RULE-ID: decl-vdecinit-evaluation *)
(!s0 ty loc exte exte' s f.
     mng exte s0 (s, exte') /\
     ((f = CopyInit) \/ (f = DirectInit))
   ==>
     declmng mng vdf (VDecInitA ty loc (f exte), s0)
                     ([VDecInitA ty loc (f exte')], s))

   /\

(* RULE-ID: decl-vdecinit-lval2rval *)
(!ty loc e0 se0 s0 s e se f.
     lval2rval (s0,e0,se0) (s,e,se) /\ ~ref_type ty /\
     ((f = CopyInit) \/ (f = DirectInit))
   ==>
     declmng mng vdf (VDecInitA ty loc (f (NormE e0 se0)), s0)
                     ([VDecInitA ty loc (f (NormE e se))], s))

   /\

(* RULE-ID: decl-vdecinit-finish *)
(* for non-class, non-reference types *)
(!s0 s v ty dty v' se a rs f.
     parameter_coerce (v,ty) (v',dty) /\
     is_null_se se /\
     (!cnm. ~(dty = Class cnm)) /\
     (s = val2mem (s0 with initmap updated_by (UNION) rs) a v') /\
     (rs = range_set a (LENGTH v')) /\
     ((f = CopyInit) \/ (f = DirectInit))
   ==>
     declmng mng vdf (VDecInitA dty
                                (ObjPlace a)
                                (f (NormE (ECompVal v ty) se)), s0)
                     ([], s))

   /\

(* RULE-ID: decl-vdecinit-finish-ref *)
(* a0 is bogus, NULL even. - assume for the moment that aopt doesn't matter *)
(!s0 ty1 nm a aopt ty2 p s se f.
     is_null_se se /\
     ((f = CopyInit) \/ (f = DirectInit)) /\
     (s = s0 with varmap updated_by (\fm. fm |+ (nm, (a,p))))
   ==>
     declmng mng
             vdf
             (VDecInitA (Ref ty1)
                        (RefPlace aopt nm)
                        (f (NormE (LVal a ty2 p) se)), s0)
             ([], s))

   /\

(* RULE-ID: decl-vdecinit-direct-class-finish *)
(* differences with decl-vdecinit-finish:
     * no need to update memory, or init_map as this will have all been
       done by the constructor
*)
(!cnm a ty se0 s0.
     is_null_se se0
   ==>
     declmng mng vdf
             (VDecInitA (Class cnm)
                        (ObjPlace a)
                        (DirectInit (NormE (ECompVal [] ty) se0)), s0)
             ([], s0))

(* TODO: add a rule for performing class based CopyInit updates *)
`

val declmng_MONO = store_thm(
  "declmng_MONO",
  ``(!x y z. P x y z ==> Q x y z) ==>
    (declmng P f s1 s2 ==> declmng Q f s1 s2)``,
  STRIP_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`s2`, `s1`] THEN
  HO_MATCH_MP_TAC declmng_ind THEN SIMP_TAC (srw_ss()) [declmng_rules] THEN
  REPEAT STRIP_TAC THEN
  FIRST (map (fn th => MATCH_MP_TAC th THEN SRW_TAC [][] THEN METIS_TAC [])
             (CONJUNCTS
                (SIMP_RULE pure_ss [FORALL_AND_THM] declmng_rules))));
val _ = export_mono "declmng_MONO"

val _ = print "About to define meaning relation\n"
val mng  =
    mk_var("meaning", ``:ExtE -> CState -> (CState # ExtE) -> bool``)
val _ = temp_overload_on("ev", ``mExpr``)


val (meaning_rules, meaning_ind, meaning_cases) = Hol_reln`

(* RULE-ID: number-literal *)
(!n se s.
     T
   ==>
     ^mng (mExpr (Cnum n) se) s
          (s, ev (ECompVal (signed_int (&n)) (Signed Int)) se))

   /\

(* RULE-ID: char-literal *)
(!n se s.
     T
   ==>
     ^mng (mExpr (Cchar n) se) s
          (s, ev (ECompVal (signed_int (&n)) BChar) se))

   /\

(* RULE-ID: null-pointer *)
(!t se s.
     T
   ==>
     ^mng (mExpr (Cnullptr t) se) s
          (s, ev (ECompVal (THE (ptr_encode (s,t) (0, default_path t)))
                            (Ptr t)) se))

   /\

(* RULE-ID: this *)
(!se s.
     T
   ==>
     ^mng (mExpr This se) s (s, ev (THE s.thisvalue) se))

   /\

(* RULE-ID: var-to-lvalue *)
(!vname se s a p.
     object_type (s.typemap ' vname) /\ vname IN FDOM s.typemap /\
     (s.varmap ' vname = (a,p))
   ==>
     ^mng (mExpr (Var vname) se) s
          (s, ev (LVal a (s.typemap ' vname) p) se))

   /\

(* RULE-ID: var-to-fvalue *)
(* BAD_ASSUMPTION: need to add treatment of member functions that are
     called without explicitly using structure dereference operation,
     which can happen in the body of member functions *)
(!vname se s ty.
     vname IN FDOM s.typemap /\ (ty = s.typemap ' vname) /\
     function_type ty /\ vname IN FDOM s.fnencode
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

(* RULE-ID: econtext-propagates-failure *)
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
     (!res restype. ~binop_meaning s f v1 type1 v2 type2 res restype)
   ==>
     ^mng (mExpr (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se0) s
          (s, ev UndefinedExpr se0))

   /\

(* RULE-ID: binop-computes *)
(!s f v1 type1 v2 type2 res restype se.
     binop_meaning s f v1 type1 v2 type2 res restype
   ==>
      ^mng (mExpr (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se) s
           (s, ev (ECompVal res restype) se))

   /\

(* RULE-ID: unop-computes *)
(!s f ival t result rt se.
     unop_meaning f ival t result rt
   ==>
     ^mng (mExpr (CApUnary f (ECompVal ival t)) se) s
          (s, ev (ECompVal result rt) se))

   /\

(* RULE-ID: unop-fails *)
(!s0 se0 f ival t.
     (!res rt. ~(unop_meaning f ival t res rt))
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
     expr_type (expr_type_comps s) RValue e2 t2 /\
     expr_type (expr_type_comps s) RValue e3 t3 /\
     expr_type (expr_type_comps s) RValue
               (CCond (ECompVal v t) e2 e3)
               result_type /\
     is_zero t v  /\
     ((t2 = Class sn) /\ (resexpr = e3) \/
      (!sn. ~(t2 = Class sn)) /\ (resexpr = Cast result_type e3))
   ==>
     ^mng (mExpr (CCond (ECompVal v t) e2 e3) se) s (s, ev resexpr base_se))

   /\

(* RULE-ID: cond-true *)
(!v t e2 t2 e3 t3 resexpr result_type se s sn.
     is_null_se se /\ scalar_type t /\
     expr_type (expr_type_comps s) RValue e2 t2 /\
     expr_type (expr_type_comps s) RValue e3 t3 /\
     expr_type (expr_type_comps s) RValue
               (CCond (ECompVal v t) e2 e3)
               result_type /\
     ~is_zero t v /\
     ((t2 = Class sn) /\ (resexpr = e2) \/
       (!sn. ~(t2 = Class sn)) /\ (resexpr = Cast result_type e2))
   ==>
     ^mng (mExpr (CCond (ECompVal v t) e2 e3) se) s
          (s, ev resexpr base_se))

   /\

(* RULE-ID: deref-objptr *)
(* 5.3.1 p1 - pointer to an object type *)
(!mval t se s addr pth.
     object_type t /\ (SOME (addr,pth) = ptr_decode(s,t) mval)
   ==>
     ^mng (mExpr (Deref (ECompVal mval (Ptr t))) se) s
          (s, ev (LVal addr t pth) se))

   /\

(* RULE-ID: deref-objptr-fails *)
(!mval t se s.
     object_type t /\ (ptr_decode(s,t) mval = NONE)
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
     (SOME result = ptr_encode (s,t) (a,pth))
   ==>
     ^mng (mExpr (Addr (LVal a t pth)) se) s
           (s, ev (ECompVal result (Ptr (static_type (t,pth)))) se))

   /\

(* RULE-ID: mem-addr-static-nonfn *)
(* 5.3.1 p2 if the address is taken of a qualified-ident that is actually a
   static member, then a normal address is generated *)
(!cname fldname se s addr ty cinfo prot pth ptrval userdefs.
     cname IN FDOM s.classmap /\
     (s.classmap ' cname = SOME (cinfo, userdefs)) /\
     MEM (FldDecl fldname ty, T, prot) cinfo.fields /\
     (s.varmap ' (Member cname fldname) = (addr, pth)) /\
     (SOME ptrval = ptr_encode (s,ty) (addr,pth))
   ==>
     ^mng (mExpr (MemAddr cname fldname) se) s
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
    parameter_coerce (v0,t0) (v,lhs_t) /\
    (se = add_se (a, v) se0) /\ (resv = ECompVal v lhs_t)
                          \/
    (!v. ~parameter_coerce (v0, t0) (v, lhs_t)) /\
    (resv = UndefinedExpr) /\ (se = se0)
   ==>
     ^mng (mExpr (Assign NONE (LVal a lhs_t []) (ECompVal v0 t0)) se0)
          s (s, ev resv se))

   /\

(* RULE-ID: postinc *)
(!se0 se s t t' sz v nv nv1 a resv.
     sizeof T (sizeofmap s) t sz /\ (v = mem2val s a sz) /\
     range_set a sz SUBSET s.initmap /\
     binop_meaning s CPlus v t (signed_int 1) (Signed Int) nv1 t' /\
     parameter_coerce (nv1,t') (nv,t) /\
     (se = add_se (a, nv) se0) /\ (resv = ECompVal v t)
                \/
     (!nv. ~parameter_coerce (nv1, t') (nv, t)) /\
     (se = se0) /\ (resv = UndefinedExpr)
   ==>
     ^mng (mExpr (PostInc (LVal a t [])) se0) s (s, ev resv se))

   /\

(* RULE-ID: postinc-fails-inc-or-initialised *)
(!a t se0 sz s v.
     sizeof T (sizeofmap s) t sz /\
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


       subobject of the original LVal is ignored.  This is because
   only functions can get a "virtual" treatment.
   This doesn't mean that a field reference can't be to an ancestor's field.

*)
(!s cnm fld ftype Cflds se offn i a p p'.
     s |- LAST p has least fld -: ftype via p' /\
     (Cflds = THE (nsdmembers s (LAST p'))) /\
     object_type ftype /\
     lookup_field_info Cflds fld (i,ftype) /\
     offset (sizeofmap s) (MAP (UNCURRY NSD) Cflds) i offn
   ==>
     ^mng (mExpr (SVar (LVal a (Class cnm) p) fld) se) s
          (s, ev (LVal (a + subobj_offset s (cnm, p ^ p') + offn) ftype
                       (default_path ftype)) se))

   /\

(* RULE-ID: function-member-select *)
(* looking up a function member *)
(* This is the equivalent of most of Wasserab's rule BS10.  *)
(* As the FVal has its last component with path = Cs', the method call will
   jump into the method body with the right value for this *)
(!a C Cs Cs' Ds fld dyn_retty se s static_retty body0 args0 args body.
     s |- LAST Cs has least method fld -: (static_retty,args0,body0) via Ds /\
     s |- (C,Cs ^ Ds) selects fld -: (dyn_retty,args,body) via Cs'
   ==>
     ^mng (mExpr (SVar (LVal a (Class C) Cs) fld) se) s
          (s, ev (FVal (Member (LAST Cs') fld)
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

(* RULE-ID: constructor-call-sqpt *)
(!mdp a cnm params se s.
     EVERYi (\i e. if constructor_expects_rval s cnm params i then
                     ?v t. e = ECompVal v t
                   else
                     ?a t p. e = LVal a t p)
            params /\
     is_null_se se
   ==>
     ^mng (mExpr (FnApp (ConstructorFVal mdp a cnm) params) se) s
          (s, ev (FnApp_sqpt (ConstructorFVal mdp a cnm) params) base_se))

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
(!ftype params se s0 s1 fnid rt vs body.
     (ftype = Function rt vs) /\
     pass_parameters
       (s0 with <| classmap := s0.gclassmap ;
                   typemap := s0.gtypemap ;
                   varmap := s0.varmap |>)
       fnid params s1 /\
     ((s0.fnmap ' fnid).body = body)
   ==>
     ^mng (mExpr (FnApp_sqpt (FVal fnid ftype NONE) params) se) s0
          (s1 with
            stack updated_by
                  (CONS (s0.classmap, s0.typemap, s0.varmap, s0.thisvalue)),
           EStmt body (return_cont se rt)))

   /\

(* RULE-ID: function-call-fails *)
(* works for both global and member function calls *)
(!ftype params se s0 fnid copt.
    (!s. ~pass_parameters s0 fnid params s)
   ==>
    ^mng (mExpr (FnApp_sqpt (FVal fnid ftype copt) params) se) s0
         (s0, ev UndefinedExpr se))

   /\

(* RULE-ID: member-function-call *)
(*   by the time this call is made, we have already figured out which
     function we will be jumping into

     TODO: set up class member values as "locals".  I.e., if class C
       has a member x, then x can be directly referred to in the
       class's member functions
*)
(!fnid ftype a cname args rt se0 s0 s1 p body this.
     pass_parameters
       (s0 with <| classmap := s0.gclassmap ;
                   typemap := s0.gtypemap ;
                   varmap := s0.varmap |>)
       fnid args s1 /\
     ((s0.fnmap ' fnid).body = body) /\
     (SOME this = ptr_encode (s0, Class cname) (a,p))
   ==>
     ^mng (mExpr (FnApp_sqpt (FVal fnid ftype (SOME (LVal a (Class cname) p)))
                             args) se0)
          s0
          (s1 with <| stack updated_by
                        (CONS (s0.classmap,s0.typemap,s0.varmap,s0.thisvalue));
                      thisvalue := SOME (ECompVal this (Ptr (Class cname)));
                      blockclasses updated_by stackenv_newscope
                   |>,
           EStmt body (return_cont se0 rt)))

   /\

(* RULE-ID: constructor-function-call *)
(!cnm mdp a args se0 params s0 s1 mem_inits this body cpfx.
     find_constructor_info s0 cnm args params mem_inits body /\
     rec_i_params
       (s0 with <| classmap := s0.gclassmap ;
                   typemap := s0.gtypemap ;
                   varmap := s0.varmap |>)
       params
       args
       s1 /\
     (SOME this = ptr_encode (s0, Class cnm) (a, [cnm])) /\
     (cpfx = construct_ctor_pfx s0 mdp a cnm mem_inits body)
   ==>
     ^mng (mExpr (FnApp_sqpt (ConstructorFVal mdp a cnm) args) se0)
          s0
          (s1 with <| stack updated_by
                        (CONS (s0.classmap,s0.typemap,s0.varmap,s0.thisvalue));
                      thisvalue := SOME (ECompVal this (Ptr (Class cnm)));
                      blockclasses updated_by stackenv_newscope
                   |>,
           EStmt (Block T cpfx [body]) (return_cont se0 Void)))

   /\

(* RULE-ID: function-application-lval2rval *)
(!f pfx e0 e sfx se0 se s0 s.
     lval2rval (s0,e0,se0) (s,e,se) /\
     fn_expects_rval s0 f (LENGTH pfx)
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
(!v t s se0 se c smap tmap vmap thisval stack'.
     is_null_se se0 /\ (s.stack = (smap,tmap,vmap,thisval)::stack')
   ==>
     ^mng (mStmt (Ret (NormE (ECompVal v t) se0)) (RVC c se)) s
          (s with <| stack := stack'; classmap := smap; typemap := tmap;
                     varmap := vmap; thisvalue := thisval |>,
           mExpr (c v t) se))

   /\

(* RULE-ID: return-lvalue *)
(!a t p se0 se c s cmap tmap vmap thisval stack'.
     is_null_se se0 /\ (s.stack = (cmap,tmap,vmap,thisval)::stack')
   ==>
     ^mng (mStmt (Ret (NormE (LVal a t p) se0)) (LVC c se)) s
          (s with <| stack := stack'; classmap := cmap; typemap := tmap;
                     varmap := vmap; thisvalue := thisval |>,
           mExpr (c a t p) se))

   /\

(* RULE-ID: empty-ret *)
(!s c.
     T
   ==>
     ^mng (mStmt EmptyRet c) s
          (s, mStmt (Ret (NormE (ECompVal [] Void) base_se)) c))

   /\


(* statements evaluate as normal under Traps *)
(!tt st st' c s0 s.
     ^mng (mStmt st c) s0 (s, mStmt st' c)
   ==>
     ^mng (mStmt (Trap tt st) c) s0 (s, mStmt (Trap tt st') c))

   /\

(* final cases for Traps.  This will need generalisation for exceptions  *)
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
          (s with stack updated_by (CONS (s.classmap,s.typemap,s.varmap,NONE)),
           mStmt (Block T vds sts) c))

   /\

(* RULE-ID: block-exit-destructor-call *)
(!s c st a cnm p rest bcs.
     (s.blockclasses = ((a,Class cnm,p) :: rest) :: bcs) /\ final_stmt st
   ==>
     ^mng (mStmt (Block T [] [st]) c) s
          (s with blockclasses := rest :: bcs,
           mStmt
             (Block T [] [Standalone (mExpr (DestructorCall a cnm) base_se);
                          st]) c))

   /\

(* RULE-ID: destructor-call *)
(!a p se0 s0 this cnm body.
     (cnm = LAST p) /\ is_null_se se0 /\
     (SOME this = ptr_encode (s0, Class cnm) (a, [cnm])) /\
     find_destructor_info s0 cnm body
   ==>
     ^mng (mExpr (DestructorCall a cnm) se0)
          s0
          (s0 with <| stack updated_by
                        (CONS (s0.classmap,s0.typemap,s0.varmap,s0.thisvalue));
                      thisvalue := SOME (ECompVal this (Ptr (Class cnm)))
                   |>,
           EStmt body (return_cont se0 Void)))

   /\

(* RULE-ID: block-exit *)
(!st s c stm tym vrm stk' bcs.
     (s.stack = (stm,tym,vrm,NONE) :: stk') /\ final_stmt st /\
     (s.blockclasses = []::bcs)
   ==>
     ^mng (mStmt (Block T [] [st]) c) s
          (s with <| stack := stk'; classmap := stm; typemap := tym;
                     varmap := vrm; blockclasses := bcs |>,
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
     final_stmt exstmt /\ ~(exstmt = EmptyStmt) /\ ~(sts = [])
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
     declmng ^mng I (d0, s0) (ds, s)
   ==>
     ^mng (mStmt (Block T (d0 :: vds) sts) c) s0
          (s, mStmt (Block T (ds ++ vds) sts) c))

   /\

(* RULE-ID: block-vstrdec *)
(* TODO: handle local classes *)
(!name info s vds sts c.
     T
   ==>
     ^mng (mStmt (Block T (VStrDec name info :: vds) sts) c) s
          (s with classmap
           updated_by (\sm. sm |+ (Base name,
                                   case info of NONE -> NONE
                                             || SOME i -> SOME (i,{}))),
           mStmt (Block T vds sts) c))

`


(* ----------------------------------------------------------------------
    how to evaluate a sequence of external declarations
   ---------------------------------------------------------------------- *)

(* if the evaluation can't get the list of external declarations to the
   empty list, this is (implicitly) an occurrence of undefined behaviour *)
val (emeaning_rules, emeaning_ind, emeaning_cases) = Hol_reln`

(* RULE-ID: global-fndefn *)
(!s0 s fval name rettype params body ftype edecls.
     installfn s0 Ptr rettype name params body fval s /\
     ~(name IN FDOM s.typemap) /\ ~is_class_name name /\
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
(!rettype userdefs name params body edecls s0 s cinfo staticp prot.
     is_class_name name /\
     (SOME (cinfo, userdefs) = s0.classmap ' (class_part name)) /\
     MEM (FldDecl name.base (Function rettype (MAP SND params)),
          staticp, prot)
         cinfo.fields /\
     (!bdy' rettype' statp prot pms'.
         MEM (CFnDefn rettype' name.base pms' bdy', statp, prot) cinfo.fields
           ==>
         ~(MAP SND pms' = MAP SND params)) /\
     install_member_functions (class_part name) s0
                              [(CFnDefn rettype name.base params body,
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
           (s0 with classmap updated_by (\sm. sm |+ (Base name, NONE))),
         edecls))

   /\

(* RULE-ID: global-class-definition *)
(!s0 s name info0 userdefs info edecls.
     ((info,userdefs) = define_default_specials info0) /\
     install_member_functions (Base name) s0 info.fields s
   ==>
     emeaning (Decl (VStrDec name (SOME info0)) :: edecls) s0
              (copy2globals
                  (s with <| classmap updated_by
                                      (\sm. sm |+ (Base name,
                                                   SOME (info, userdefs))) |>),
               edecls))
`;



val _ = export_theory();



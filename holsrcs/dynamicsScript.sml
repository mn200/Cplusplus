(* Dynamic Semantics of C(++) forms *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open typesTheory memoryTheory expressionsTheory staticsTheory class_infoTheory
local open side_effectsTheory statesTheory operatorsTheory in end

val _ = new_theory "dynamics";


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
              (?sz. sizeof (sizeofmap s0) t sz /\
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
   and is currently unallocated *)
val malloc_def = Define`
  malloc s0 ty a =
     ?sz aln. sizeof (sizeofmap s0) ty sz /\
              align (sizeofmap s0) ty aln /\
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
          sizeof (sizeofmap s0) ptype n /\ malloc s0 ptype a /\
          (rs = range_set a n) /\
          rec_i_params
            (val2mem (s0 with
                        <| varmap updated_by
                              (\v. v |+ (pname, (a, default_path ptype))) ;
                           typemap updated_by (\t. t |+ (pname, ptype));
                           allocmap updated_by ((UNION) rs);
                           initmap updated_by ((UNION) rs) |>)
                     a
                     newval)
            ptl vtl s) \/
       (?a ty p vtl.
          (vallist = LVal a ty p :: vtl) /\ (ptype = Ref ty) /\
          rec_i_params
            (s0 with <| varmap updated_by (\v. v |+ (pname, (a, p)));
                        typemap updated_by (\t. t |+ (pname, ty)) |>)
            ptl vtl s))
`;

val pass_parameters_def = Define`
  pass_parameters s0 fnid pv s =
      rec_i_params s0 ((s0.fnmap ' fnid).parameters) pv s
`;

val _ = overload_on ("mExpr", ``statements$NormE``)
val _ = overload_on ("mStmt", ``statements$EStmt``)

val is_mExprish_def = Define`
    (is_mExprish (mExpr e se) = T) /\
    (is_mExprish _ = F)
`;

val out_mExpr_def = Define`
  (out_mExpr (mExpr e se) = (e, se))
`

val signed_int_def = Define`
  signed_int i = THE (REP_INT (Signed Int) i)
`

(* this appears to be needlessly recursive on the first argument (the type),
   but when one added valuations for floats, the rhs would need to
   call a float-valuation function (not INT_VAL, whose range is
   necessarily just the integers *)

(* note that this predicate is two-valued: the possibility that a value
   isn't well-defined for the type is ignored.  This is because we assume
   that possibility is dealt with elsewher: when values are read out of
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
  vdeclare s0 ty nm optval s =
     (?a sz s' rs.
         (rs = range_set a sz) /\
         object_type ty /\ malloc s0 ty a /\ sizeof (sizeofmap s) ty sz /\
         (s' = s0 with <| allocmap updated_by (UNION) rs;
                           varmap updated_by
                              (\vm. vm |+ (nm,(a,default_path ty)));
                           typemap updated_by (\tm. tm |+ (nm,ty)) |>) /\
         (case optval of
             NONE -> (s = s')
          || SOME (ECompVal v ty') ->
                (s = val2mem (s' with initmap updated_by (UNION) rs) a v)
          || SOME other -> F))
        \/
     (function_type ty /\
      (s = s0 with typemap updated_by (\tm. tm |+ (nm, ty))))
        \/
     (?a t ty0 p.
        (ty = Ref ty0) /\ (optval = SOME (LVal a t p)) /\
        (s = s0 with <| varmap updated_by (\vm. vm |+ (nm, (a, p)));
                        typemap updated_by (\tm. tm |+ (nm, ty)) |>))

`;

val copy2globals_def = Define`
  copy2globals s = (s with <| gclassmap := s.classmap;
                              gtypemap := s.typemap;
                              gvarmap := s.varmap |>)
`;

(* true if the nth argument of f is not a reference type *)
val fn_expects_rval_def = Define`
  fn_expects_rval s f n =
    ?retty args.
      (expr_type (expr_type_comps s) RValue f (Function retty args) \/
       expr_type (expr_type_comps s) RValue f (Ptr (Function retty args))) /\
      ~ref_type (EL n args)
`;

val return_cont_def = Define`
  return_cont ty = if ref_type ty then LVC LVal
                   else RVC ECompVal
`

val cont_comp_def = Define`
  (cont_comp f (RVC rc) = RVC (\v rt. f (rc v rt))) /\
  (cont_comp f (LVC lc) = LVC (\a t p. f (lc a t p)))
`

val RVR_def = Define`
  (RVR (mExpr e se) = mExpr (RValreq e) se) /\
  (RVR (mStmt s c) = mStmt s c)
`

val _ = print "About to define meaning relation\n"
val mng  =
    mk_var("meaning", ``:ExtE -> CState -> (CState # ExtE) -> bool``)
val _ = temp_overload_on("ev", ``mExpr``)
val _ = set_trace "inddef strict" 1

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

(* BAD_ASSUMPTION: need to add treatment of member functions that are
     called without explicitly using structure dereference operation,
     which can happen in the body of member functions *)
(!vname se s ty.
     vname IN FDOM s.typemap /\ (ty = s.typemap ' vname) /\
     function_type ty /\ GlobalFn vname IN FDOM s.fnencode
   ==>
     ^mng (mExpr (Var vname) se) s
          (s, ev (FVal (GlobalFn vname) ty NONE) se))

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

(* 5.3.1 p1 - pointer to an object type *)
(!mval t se s addr pth.
     object_type t /\ (SOME (addr,pth) = ptr_decode(s,t) mval)
   ==>
     ^mng (mExpr (Deref (ECompVal mval (Ptr t))) se) s
          (s, ev (LVal addr t pth) se))

   /\

(!mval t se s.
     object_type t /\ (ptr_decode(s,t) mval = NONE)
   ==>
     ^mng (mExpr (Deref (ECompVal mval (Ptr t))) se) s
          (s, ev UndefinedExpr se))

   /\

(* 5.3.1 p1 - pointer to a function type *)
(!v retty argtys se s.
     v IN FDOM s.fndecode
   ==>
     ^mng (mExpr (Deref (ECompVal v (Ptr (Function retty argtys)))) se) s
          (s, ev (FVal (s.fndecode ' v) (Function retty argtys) NONE) se))

   /\

(* 5.3.1 p2-5 - taking the address of an lvalue
                TODO: taking the address of a qualified-id, thereby generating
                a pointer to member *)
(!a t pth se s result.
     (SOME result = ptr_encode (s,t) (a,pth))
   ==>
     ^mng (mExpr (Addr (LVal a t pth)) se) s
           (s, ev (ECompVal result (Ptr t)) se))

   /\

(* RULE-ID: mem-addr-static-nonfn *)
(* 5.3.1 p2 if the address is taken of a qualified-ident that is actually a
   static member, then a normal address is generated *)
(!cname fldname se s addr ty cinfo prot pth ptrval.
     cname IN FDOM s.classmap /\ (s.classmap ' cname = SOME cinfo) /\
     MEM (FldDecl fldname ty, T, prot) cinfo.fields /\
     (cname, fldname) IN FDOM s.statics /\
     (s.statics ' (cname, fldname) = (addr, pth)) /\
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
     sizeof (sizeofmap s) t sz /\ (v = mem2val s a sz) /\
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
     sizeof (sizeofmap s) t sz /\
     (v = mem2val s a sz) /\
     ((!nv1 t'.
         ~binop_meaning s CPlus v t (signed_int 1) (Signed Int) nv1 t') \/
     ~(range_set a sz SUBSET s.initmap))
   ==>
     ^mng (mExpr (PostInc (LVal a t [])) se0) s (s, ev UndefinedExpr se0))

   /\

(* RULE-ID: non-static-data-member-field-selection *)
(!s C fld ftype Cflds se offn i a p p'.
     s |- C has least fld -: ftype via p' /\
     (Cflds = THE (nsdmembers s (LAST p'))) /\
     object_type ftype /\
     lookup_field_info Cflds fld (i,ftype) /\
     offset (sizeofmap s) (MAP SND Cflds) i offn
   ==>
     ^mng (mExpr (SVar (LVal a (Class C) p) fld) se) s
          (s, ev (LVal (a + THE (subobj_offset s C p') + offn) ftype
                       (default_path ftype)) se))

   /\

(* RULE-ID: function-member-select *)
(* looking up a function member *)
(* This is the equivalent of most of Wasserab's rule BS10.  Because we're
   not yet doing multiple inheritance (TODO), we can be sure that the head
   of p is the enclosing, most-derived class, and that there will be a unique
   lowest function in the hierarchy for it to call.
*)
(!a C p p' fld retty argtys se s.
     s |- HD p has least fld -: Function retty argtys via p'
       (* recall that C will be the last element of p (INVARIANT) *)
   ==>
     ^mng (mExpr (SVar (LVal a (Class C) p) fld) se) s
          (s, ev (FVal (MFn (LAST p') fld)
                       (Function retty argtys)
                       (SOME (LVal a (Class (LAST p')) p')))
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
           EStmt body (return_cont rt)))

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
                      thisvalue := SOME (ECompVal this (Ptr (Class cname)))
                   |>,
           EStmt body (return_cont rt)))

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
(!e0 se0 s0 e se s c.
     lval2rval (s0,e,se0) (s,e,se)
   ==>
     ^mng (mStmt (Ret (NormE e0 se0)) (RVC c)) s0
          (s, mStmt (Ret (NormE e se)) (RVC c)))

   /\

(* RULE-ID: return-rvalue *)
(* all recursive stmt rules require RHS of reduction to still be
   an mStmt, preventing this rule from firing at depth *)
(!v t s se c smap tmap vmap thisval stack'.
     is_null_se se /\ (s.stack = (smap,tmap,vmap,thisval)::stack')
   ==>
     ^mng (mStmt (Ret (NormE (ECompVal v t) se)) (RVC c)) s
          (s with <| stack := stack'; classmap := smap; typemap := tmap;
                     varmap := vmap; thisvalue := thisval |>,
           mExpr (c v t) base_se))

   /\

(* RULE-ID: return-lvalue *)
(!a t p se c s cmap tmap vmap thisval stack'.
     is_null_se se /\ (s.stack = (cmap,tmap,vmap,thisval)::stack')
   ==>
     ^mng (mStmt (Ret (NormE (LVal a t p) se)) (LVC c)) s
          (s with <| stack := stack'; classmap := cmap; typemap := tmap;
                     varmap := vmap; thisvalue := thisval |>,
           mExpr (c a t p) base_se))

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
     ^mng (mStmt (Trap tt st) c) s0 (s, mStmt (Trap tt st') c)) /\

(* final cases for Traps.  This will need generalisation for exceptions  *)
(!c s0.
     ^mng (mStmt (Trap BreakTrap Break) c) s0 (s0, mStmt EmptyStmt c)) /\

(!c s0.
     ^mng (mStmt (Trap ContTrap Cont) c) s0 (s0, mStmt EmptyStmt c)) /\

(!c s0.
     ^mng (mStmt (Trap ContTrap Break) c) s0 (s0, mStmt Break c)) /\

(!c s0.
     ^mng (mStmt (Trap BreakTrap Cont) c) s0 (s0, mStmt Cont c)) /\

(* RULE-ID: trap-emptystmt *)
(!c tt s0.
     T
   ==>
     ^mng (mStmt (Trap tt EmptyStmt) c) s0 (s0, mStmt EmptyStmt c))

   /\

(* RULE-ID: trap-ret *)
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

(* RULE-ID: block-exit *)
(!st s c stm tym vrm stk'.
     (s.stack = (stm,tym,vrm,NONE) :: stk') /\ final_stmt st
   ==>
     ^mng (mStmt (Block T [] [st]) c) s
          (s with <| stack := stk'; classmap := stm; typemap := tym;
                     varmap := vrm |>,
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

(* RULE-ID: block-vdec *)
(!s0 s ty name vds sts c.
     vdeclare s0 ty name NONE s
   ==>
     ^mng (mStmt (Block T (VDec ty name :: vds) sts) c) s0
          (s, mStmt (Block T vds sts) c))

   /\

(* RULE-ID: block-vdecinit-evaluate *)
(!ty name exte exte' s0 s vds sts c.
     ^mng exte s0 (s, exte')
   ==>
     ^mng (mStmt (Block T (VDecInit ty name exte::vds) sts) c) s0
          (s, mStmt (Block T (VDecInit ty name exte'::vds) sts) c))

   /\

(* RULE-ID: block-vdecinit-lval2rval *)
(!s0 e0 se0 s e se ty name vds sts c.
     lval2rval (s0,e0,se0) (s,e,se) /\ ~ref_type ty
   ==>
     ^mng (mStmt (Block T (VDecInit ty name (mExpr e0 se0) :: vds) sts) c) s0
          (s, mStmt (Block T (VDecInit ty name (mExpr e se) :: vds) sts) c))

   /\

(* RULE-ID: block-vdecinit-finish-nonref *)
(!dty name v ty v' se vds sts c s0 s.
     is_null_se se /\ vdeclare s0 dty name (SOME (ECompVal v' dty)) s /\
     parameter_coerce (v,ty) (v',dty)
   ==>
     ^mng (mStmt (Block T (VDecInit dty name (NormE (ECompVal v ty) se) :: vds)
                          sts) c)
          s0
          (s, mStmt (Block T vds sts) c))

   /\

(* RULE-ID: block-vdecinit-finish-ref *)
(!se s0 ty name a t p s vds sts c.
     is_null_se se /\ vdeclare s0 ty name (SOME (LVal a t p)) s
   ==>
     ^mng (mStmt (Block T (VDecInit ty name (NormE (LVal a t p) se) :: vds)
                        sts) c)
          s0
          (s, mStmt (Block T vds sts) c))

   /\

(* RULE-ID: block-vstrdec *)
(* TODO: handle local classes *)
(!name info s vds sts c.
     T
   ==>
     ^mng (mStmt (Block T (VStrDec name info :: vds) sts) c) s
          (s with classmap updated_by (\sm. sm |+ (name,info)),
           mStmt (Block T vds sts) c))

`

(* installing a function *)
val installfn_def = Define`
  installfn s0 retty fnid params body fval s =
     ~(fval IN FDOM s0.fndecode) /\ ~(fnid IN FDOM s.fnmap) /\
     (s = s0 with <| fnmap updated_by
                       (\fm. fm |+ (fnid, <| body := body;
                                             return_type := retty;
                                             parameters := params |>));
                     fnencode updated_by (\fm. fm |+ (fnid, fval));
                     fndecode updated_by (\fm. fm |+ (fval, fnid)) |>)
`




(* installing a bunch of member functions *)

(* imemfn is where the real work gets done - it takes a list of fields
   and "relationally" installs them into the state *)
val imemfn_def = Define`
  (imemfn cnm s0 [] s = (s0 = s)) /\
  (imemfn cnm s0 ((FldDecl nm ty, b, p) :: rest) s = imemfn cnm s0 rest s) /\
  (imemfn cnm s0 ((CFnDefn retty nm params body, b, p) :: rest) s =
     ?fval s'. installfn s0 retty (MFn cnm nm) params body fval s' /\
               sizeof (sizeofmap s0)
                      (MPtr cnm (Function retty (MAP SND params)))
                      (LENGTH fval) /\
               imemfn cnm s' rest s) /\
  (imemfn cnm s0 ((Constructor params meminits body, b, p) :: rest) s =
     (s0 = s)) /\
  (imemfn cnm s0 ((Destructor body, b, p) :: rest) s = (s0 = s))
`

val install_member_functions_def = Define`
  install_member_functions cname s0 flds_opt s =
    case flds_opt of
       NONE -> (s = s0)
    || SOME entries -> imemfn cname s0 entries s
`

(* ----------------------------------------------------------------------
    how to evaluate a sequence of external declarations
   ---------------------------------------------------------------------- *)

val (emeaning_rules, emeaning_ind, emeaning_cases) = Hol_reln`

(!s0 s fval name rettype params body ftype edecls.
     installfn s0 rettype (GlobalFn name) params body fval s /\
     ~(name IN FDOM s.typemap) /\
     (LENGTH fval = ptr_size ftype) /\
     (ftype = Function rettype (MAP SND params))
   ==>
     emeaning
       (FnDefn rettype name params body :: edecls) s
       (s with <| typemap updated_by (\tm. tm |+ (name, ftype)) |>,
        edecls)) /\

(!s0 ty name s edecls.
     vdeclare s0 ty name NONE s
   ==>
     emeaning (Decl (VDec ty name) :: edecls) s0 (copy2globals s, edecls)) /\

(!s0 ty name exte exte' edecls s.
     meaning exte s0 (s, exte')
   ==>
     emeaning (Decl (VDecInit ty name exte) :: edecls) s0
              (s, Decl (VDecInit ty name exte') :: edecls))

   /\

(!ty name e0 se0 edecls s0 s e se.
     lval2rval (s0,e0,se0) (s,e,se) /\ ~ref_type ty
   ==>
     emeaning (Decl (VDecInit ty name (mExpr e0 se0)) :: edecls) s0
              (s, Decl (VDecInit ty name (mExpr e se)) :: edecls))

   /\

(!s0 s name v ty dty v' edecls se.
     vdeclare s0 dty name (SOME (ECompVal v' dty)) s /\
     parameter_coerce (v,ty) (v',dty) /\
     is_null_se se /\ ~ref_type dty
   ==>
     emeaning (Decl (VDecInit dty name (NormE (ECompVal v ty) se)) :: edecls)
              s0
              (copy2globals s, edecls))

   /\

(!s0 ty name a t p s se edecls.
     vdeclare s0 ty name (SOME (LVal a t p)) s /\ is_null_se se /\
     ref_type ty
   ==>
     emeaning (Decl (VDecInit ty name (NormE (LVal a t p) se)) :: edecls)
              s0
              (copy2globals s, edecls))

   /\

(!s0 s name info edecls.
     install_member_functions name s0 (OPTION_MAP class_info_fields info) s
   ==>
     emeaning (Decl (VStrDec name info) :: edecls) s0
              (copy2globals
                  (s with <| classmap updated_by
                                      (\sm. sm |+ (name,info)) |>),
               edecls))
`;



val _ = export_theory();



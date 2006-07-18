(* Dynamic Semantics of C(++) forms *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open typesTheory memoryTheory expressionsTheory staticsTheory
local open side_effectsTheory statesTheory operatorsTheory in end

val _ = new_theory "dynamics";


(* an e-context is a function defining contexts where expression evaluation
   can occur *)
val valid_econtext_def = Define`
  valid_econtext f =
      (?f' e1. f = CApBinary f' e1) \/
      (?f' e2. f = \e1. CApBinary f' e1 e2) \/
      (?f' e2 b. f = \e1. Assign f' e1 e2 b) \/
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

val lval2rval_def = Define`
  lval2rval (s0,e0,se0) (s,e,se) =
       (s0 = s) /\
       ?n t. (e0 = LVal n t) /\
             (~(array_type t) /\
              (?sz. sizeof (sizeofmap s0) t sz /\
                    (mark_ref n sz se0 se /\
                     (range_set n sz) SUBSET s0.initmap /\
                     (e = ECompVal (mem2val s0 n sz) t) \/
                     (~(range_set n sz SUBSET s0.initmap) \/
                      (!se'. ~(mark_ref n sz se0 se'))) /\
                     (se = se0) /\ (e = UndefinedExpr))) \/
              (?sz t' bytes.
                  (t = Array t' sz) /\ (se0 = se) /\
                  (SOME bytes = REP_INT (Ptr t') (&n)) /\
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
      lval2rval (s0, e0, se0) X ==> ?n t. e0 = LVal n t``,
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
        (?args. f = \e. FnApp e args) \/
        (?f' pre post.
              (f = \e. FnApp f' (APPEND pre (e :: post)))) \/
        (?t. f = Cast t)
`

(* SANITY *)
val lvcontexts_are_econtexts = store_thm(
  "lvcontexts_are_econtexts",
  --`!f. valid_lvcontext f ==> valid_econtext f`--,
  SRW_TAC [][valid_lvcontext_def, valid_econtext_def, FUN_EQ_THM] THEN
  SRW_TAC [][] THEN METIS_TAC [])

(* malloc s0 ty a is true if a is a valid address for a value of type ty,
   and is currently unallocated *)
val malloc_def = Define`
  malloc s0 ty a =
     ?sz aln. sizeof (sizeofmap s0) ty sz /\
              align (sizeofmap s0) ty aln /\
              DISJOINT s0.allocmap (range_set a sz) /\
              ~(a = 0) /\ (a MOD aln = 0) /\
              a + sz < 2 EXP (CHAR_BIT * ptr_size ty)
`

(* rec_i_vars installs a list variables, updating varmap, typemap and allocmap
*)
val rec_i_vars_def = Define`
  (rec_i_vars st1 [] st2 = (st1 = st2)) /\
  (rec_i_vars st1 ((nm, ty) :: tail) st2 =
      ?a n.
         sizeof (sizeofmap st1) ty n /\
         malloc st1 ty a /\
         rec_i_vars
            (st1 with
                <| varmap updated_by (\v. v |+ (nm, a)) ;
                   typemap updated_by (\t. t |+ (nm, ty));
                   allocmap updated_by ((UNION) (range_set a n))
                |>)
            tail
            st2)
`

(* install_vars installs the parameter information for a particular function *)
val install_vars_def = Define`
  install_vars st1 fn st2 =
        fn IN FDOM st1.fnmap /\
        rec_i_vars (st1 with <| varmap := st1.gvarmap ;
                                typemap := st1.gtypemap ;
                                classmap := st1.gclassmap |>)
                   ((st1.fnmap ' fn).parameters)
                   st2
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
val rec_i_vals_def = Define`
    (rec_i_vals st1 [] vallist st2 = (vallist = []) /\ (st1 = st2)) /\
    (rec_i_vals s0 ((pname, ptype) :: ptl) vallist s =
       ?vval vtype vtl.
          (vallist = ECompVal vval vtype :: vtl) /\
          ?s1 newval rs.
             parameter_coerce (vval, vtype) (newval, ptype) /\
             (rs = range_set (s0.varmap ' pname) (LENGTH newval)) /\
             (s1 = val2mem s0 (s0.varmap ' pname) newval
                   with <| initmap updated_by ((UNION) rs) ;
                           allocmap updated_by ((UNION) rs) |>) /\
             rec_i_vals s1 ptl vtl s)
`

val install_values_def = Define`
  install_values s0 fn pvl s1 = rec_i_vals s0 (s0.fnmap ' fn).parameters pvl s1
`

val pass_parameters_def = Define`
  pass_parameters s0 fnid pv s =
      ?s1. install_vars s0 fnid s1 /\ install_values s1 fnid pv s
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
  vdeclare s0 ty nm s =
     (?a sz. object_type ty /\ malloc s0 ty a /\ sizeof (sizeofmap s) ty sz /\
             (s = s0 with <| allocmap updated_by (UNION) (range_set a sz);
                             varmap updated_by (\vm. vm |+ (nm,a));
                             typemap updated_by (\tm. tm |+ (nm,ty)) |>)) \/
     (function_type ty /\
      (s = s0 with typemap updated_by (\tm. tm |+ (nm, ty))))
`;

val copy2globals_def = Define`
  copy2globals s = (s with <| gclassmap := s.classmap;
                              gtypemap := s.typemap;
                              gvarmap := s.varmap |>)
`;


local
  val _ = print "About to define meaning relation\n";
  val mng  =
    mk_var("meaning", ``:ExtE -> CState -> (CState # ExtE) -> bool``)
  val ev = ``mExpr``
  val _ = set_trace "inddef strict" 1
in
  val (meaning_rules, meaning_ind, meaning_cases) = Hol_reln`

(!n se s.
   ^mng (mExpr (Cnum n) se) s
        (s, ^ev (ECompVal (signed_int (&n)) (Signed Int)) se)) /\

(!n se s.
    ^mng (mExpr (Cchar n) se) s
         (s, ^ev (ECompVal (signed_int (&n)) (Signed Int)) se)) /\

(!t se s.
    ^mng (mExpr (Cnullptr t) se) s
         (s, ^ev (ECompVal (THE (REP_INT (Ptr t) 0)) (Ptr t)) se)) /\

(!vname se s.
    object_type (s.typemap ' vname) /\ vname IN FDOM s.typemap ==>
    ^mng (mExpr (Var vname) se) s
         (s, ^ev (LVal (s.varmap ' vname) (s.typemap ' vname)) se)) /\

(!vname se s ty.
    vname IN FDOM s.typemap /\ (ty = s.typemap ' vname) /\
    function_type ty /\ vname IN FDOM s.fnvals ==>
    ^mng (mExpr (Var vname) se) s
            (s, ^ev (ECompVal (s.fnvals ' vname) (Ptr ty)) se)) /\

(!s v t v' t' se i.
    (INT_VAL t v = SOME i) /\ (SOME v' = REP_INT t' i) ==>
    ^mng (mExpr (Cast t' (ECompVal v t)) se) s
         (s, ^ev (ECompVal v' t') se)) /\

(!v t t' se s.
    (INT_VAL t v = NONE) ==>
    ^mng (mExpr (Cast t' (ECompVal v t)) se) s (s, ^ev UndefinedExpr se)) /\

(!v t t' se s i.
    (INT_VAL t v = SOME i) /\ (REP_INT t' i = NONE) ==>
    ^mng (mExpr (Cast t' (ECompVal v t)) se) s (s, ^ev UndefinedExpr se)) /\


(!f e se0 s0 e' se s.
    ^mng (mExpr e se0) s0 (s, ^ev e' se) /\
    valid_econtext f ==>
    ^mng (mExpr ((f:CExpr->CExpr) e) se0) s0 (s, ^ev (f e') se)) /\

(!f e se0 s0 s stmt c.
    ^mng (mExpr e se0) s0 (s, mStmt stmt c) /\
    valid_econtext f ==>
    ^mng (mExpr (f e) se0) s0 (s, mStmt stmt (\v rt. f (c v rt)))) /\


(!f se s.
    valid_econtext f \/ (?asfn lhs b. f = \e. Assign asfn lhs e b) ==>
    ^mng (mExpr (f UndefinedExpr) se) s (s, ^ev UndefinedExpr se)) /\

(!f e0 se0 s0 s e se.
   valid_lvcontext f /\ lval2rval (s0,e0,se0) (s,e,se) ==>
   ^mng (mExpr ((f:CExpr->CExpr) e0) se0) s0 (s, ^ev (f e) se)) /\

(!e se0 s0 s se.
    apply_se (se0, s0) (se, s) ==>
    ^mng (mExpr e se0) s0 (s, ^ev e se)) /\

(!e se0 s0.
    (!se s. ~(apply_se (se0, s0) (se, s))) /\
    ~is_null_se se0 /\ ~(e = UndefinedExpr) ==>
    ^mng (mExpr e se0) s0 (s0, ^ev UndefinedExpr se0)) /\

(!e1 e2 se s0.
    final_value (mExpr e1 se) ==>
    ^mng (mExpr (CommaSep e1 e2) se) s0
         (s0, ^ev (RValreq e2) base_se)) /\

(!v t se s. ^mng (mExpr (RValreq (ECompVal v t)) se) s
                 (s, ^ev (ECompVal v t) se)) /\

(!f v1 type1 v2 type2 se0 s.
   (!res restype. ~binop_meaning s f v1 type1 v2 type2 res restype) ==>
   ^mng (mExpr (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se0) s
        (s, ^ev UndefinedExpr se0)) /\

(!s f v1 type1 v2 type2 res restype se.
    binop_meaning s f v1 type1 v2 type2 res restype ==>
    ^mng (mExpr (CApBinary f (ECompVal v1 type1) (ECompVal v2 type2)) se) s
         (s, ^ev (ECompVal res restype) se)) /\

(!s f ival t result rt se.
   unop_meaning f ival t result rt ==>
   ^mng (mExpr (CApUnary f (ECompVal ival t)) se) s
        (s, ^ev (ECompVal result rt) se)) /\

(!s0 se0 f ival t.
     (!res rt. ~(unop_meaning f ival t res rt)) ==>
     ^mng (mExpr (CApUnary f (ECompVal ival t)) se0) s0
          (s0, ^ev UndefinedExpr se0)) /\

(!v t se s sub2.
    is_zero t v ==>
    ^mng (mExpr (CAnd (ECompVal v t) sub2) se) s
         (s, ^ev (ECompVal (signed_int 0) (Signed Int)) se)) /\

(!v t se s sub2.
    ~is_zero t v /\ is_null_se se ==>
    ^mng (mExpr (CAnd (ECompVal v t) sub2) se) s
         (s, ^ev (CAndOr_sqpt sub2) base_se)) /\
(!v t se s.
   scalar_type t ==>
   ^mng (mExpr (CAndOr_sqpt (ECompVal v t)) se) s
        (s, ^ev (ECompVal (if INT_VAL t v = SOME 0 then signed_int 0
                           else signed_int 1) (Signed Int))
                se)) /\

(!v t sub2 se s.
   ~is_zero t v  ==>
   ^mng (mExpr (COr (ECompVal v t) sub2) se) s
        (s, ^ev (ECompVal (signed_int 1) (Signed Int)) se)) /\

(!v t sub2 se s.
    is_zero t v /\ is_null_se se ==>
    ^mng (mExpr (COr (ECompVal v t) sub2) se) s
         (s, ^ev (CAndOr_sqpt sub2) base_se)) /\

(!v t e2 t2 e3 t3 resexpr result_type se s sn.
  is_null_se se /\ scalar_type t /\
  expr_type (expr_type_comps s) RValue e2 t2 /\
  expr_type (expr_type_comps s) RValue e3 t3 /\
  expr_type (expr_type_comps s) RValue
            (CCond (ECompVal v t) e2 e3)
            result_type /\
  is_zero t v  /\
  ((t2 = Class sn) /\ (resexpr = RValreq e3) \/
   (!sn. ~(t2 = Class sn)) /\ (resexpr = Cast result_type e3)) ==>
  ^mng (mExpr (CCond (ECompVal v t) e2 e3) se) s (s, ^ev resexpr base_se))

           /\

(!v t e2 t2 e3 t3 resexpr result_type se s sn.

   is_null_se se /\ scalar_type t /\
   expr_type (expr_type_comps s) RValue e2 t2 /\
   expr_type (expr_type_comps s) RValue e3 t3 /\
   expr_type (expr_type_comps s) RValue
             (CCond (ECompVal v t) e2 e3)
             result_type /\
   ~is_zero t v /\
   ((t2 = Class sn) /\ (resexpr = RValreq e2) \/
     (!sn. ~(t2 = Class sn)) /\ (resexpr = Cast result_type e2))
           ==>
   ^mng (mExpr (CCond (ECompVal v t) e2 e3) se) s (s, ^ev resexpr base_se)) /\

(!mval t se s addr.
    ~(t = Void) /\ (SOME addr = INT_VAL (Ptr t) mval) ==>
    ^mng (mExpr (Deref (ECompVal mval (Ptr t))) se) s
         (s, ^ev (LVal (Num addr) t) se)) /\

(!a t se s.
    ^mng (mExpr (Addr (LVal a t)) se) s
          (s, ^ev (ECompVal (THE (REP_INT (Ptr t) (&a))) (Ptr t)) se)) /\

(!se0 s0 s e se mb mb' f a RHS.
    ^mng (mExpr RHS se0) s0 (s, ^ev e se) /\
    (mb' = BAG_delta (se0.ref_map, se.ref_map) mb) ==>
    ^mng (mExpr (Assign f a RHS mb) se0) s0
         (s, ^ev (Assign f a e mb') se)) /\

(!se0 s0 s f a RHS mb st c.
    ^mng (mExpr RHS se0) s0 (s, mStmt st c) ==>
    ^mng (mExpr (Assign f a RHS mb) se0) s0
         (s, mStmt st (\v t. Assign f a (c v t) mb))) /\

(!f n t e mb se0 s0.
     ^mng (mExpr (Assign (SOME f) (LVal n t) e mb) se0) s0
          (s0, ^ev (Assign NONE (LVal n t)
                         (CApBinary f (LVal n t) e)
                         mb)
                       se0)) /\

(!s v0 t0 v lhs_t ok_refs se0 se' se a resv mb.
     parameter_coerce (v0,t0) (v,lhs_t) /\
     (ok_refs = \x. x IN (se_affects (a, v)) => mb x | 0) /\
     (se' = se0 with ref_map updated_by (\rm. BAG_DIFF rm ok_refs)) /\
     (se = add_se (a, v) se') /\ (resv = ECompVal v lhs_t)
                          \/
     (!v. ~parameter_coerce (v0, t0) (v, lhs_t)) /\
     (resv = UndefinedExpr) /\ (se = se0) ==>
     ^mng (mExpr (Assign NONE (LVal a lhs_t) (ECompVal v0 t0) mb) se0)
          s (s, ^ev resv se)) /\

(!se0 se s t t' sz v nv nv1 a resv.
   sizeof (sizeofmap s) t sz /\ (v = mem2val s a sz) /\
   range_set a sz SUBSET s.initmap /\
   binop_meaning s CPlus v t (signed_int 1) (Signed Int) nv1 t' /\
   parameter_coerce (nv1,t') (nv,t) /\
   (se = add_se (a, nv) se0) /\ (resv = ECompVal v t)
              \/
   (!nv. ~parameter_coerce (nv1, t') (nv, t)) /\
   (se = se0) /\ (resv = UndefinedExpr) ==>
   ^mng (mExpr (PostInc (LVal a t)) se0) s (s, ^ev resv se)) /\

(!a t se0 sz s v.
   sizeof (sizeofmap s) t sz /\
   (v = mem2val s a sz) /\
   ((!nv1 t'.
       ~binop_meaning s CPlus v t (signed_int 1) (Signed Int) nv1 t') \/
   ~(range_set a sz SUBSET s.initmap)) ==>
   ^mng (mExpr (PostInc (LVal a t)) se0) s (s, ^ev UndefinedExpr se0)) /\

(!s st fld ftype se offn i a.
     offset (sizeofmap s) (sizeofmap s ' st) i offn /\
     st IN FDOM (lfimap s) /\
     lookup_field_info (lfimap s ' st) fld (i,ftype) ==>
     ^mng (mExpr (SVar (LVal a (Class st)) fld) se) s
          (s, ^ev (LVal (a + offn) ftype) se)) /\

(!s st fld ftype fsz v fv se i offn.
   offset (sizeofmap s) (sizeofmap s ' st) i offn /\
   st IN FDOM (lfimap s) /\
   lookup_field_info (lfimap s ' st) fld (i, ftype) /\
   sizeof (sizeofmap s) ftype fsz /\
   (fv = GENLIST (\n. EL (n + offn) v) fsz) ==>
   ^mng (mExpr (SVar (ECompVal v (Class st)) fld) se) s
        (s, ^ev (ECompVal fv ftype) se)) /\

(!f params se s.
    EVERY (\e. ?v t. e = ECompVal v t) (f :: params) /\
    is_null_se se ==>
    ^mng (mExpr (FnApp f params) se) s
         (s, ^ev (FnApp_sqpt f params) base_se)) /\

(!fnval ftype params se s0 s1 fnid rt vs body.
    (fnid = s0.fndecode ' fnval) /\ fnval IN FDOM s0.fndecode /\
    (ftype = Function rt vs) /\
    pass_parameters s0 fnid params s1 /\
    ((s0.fnmap ' fnid).body = body)
   ==>
    ^mng (mExpr (FnApp_sqpt (ECompVal fnval (Ptr ftype)) params) se) s0
         (s1 with stack updated_by (CONS (s0.classmap, s0.typemap, s0.varmap)),
          EStmt body (\rv rt'. Cast rt (ECompVal rv rt')))) /\

(!fnval ftype params se s0 fnid.
    (fnid = s0.fndecode ' fnval) /\ fnval IN FDOM s0.fndecode /\
    (!s. ~pass_parameters s0 fnid params s)
   ==>
    ^mng (mExpr (FnApp_sqpt (ECompVal fnval (Ptr ftype)) params) se) s0
         (s0, ^ev UndefinedExpr se)) /\

(!exte0 exte s1 s2 c.
   ^mng exte0 s1 (s2, exte) ==>
   ^mng (mStmt (Ret exte0) c) s1 (s2, mStmt (Ret exte) c)) /\

(* all recursive stmt rules require RHS of reduction to still be
   an mStmt, preventing this rule from firing at depth *)
(!v t s se c smap tmap vmap stack'.
   is_null_se se /\ (s.stack = (smap,tmap,vmap)::stack') ==>
   ^mng (mStmt (Ret (NormE (ECompVal v t) se)) c) s
        (s with <| stack := stack'; classmap := smap; typemap := tmap;
                   varmap := vmap |>,
         mExpr (c v t) base_se)) /\

(!s c. ^mng (mStmt EmptyRet c) s
            (s, mStmt (Ret (NormE (ECompVal [] Void) base_se)) c)) /\

(* statements evaluate as normal under Traps *)
(!tt st st' c s0 s.
     ^mng (mStmt st c) s0 (s, mStmt st' c)  ==>
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

(!c tt s0.
     ^mng (mStmt (Trap tt EmptyStmt) c) s0 (s0, mStmt EmptyStmt c)) /\

(!c tt v t se s0.
     is_null_se se ==>
     ^mng (mStmt (Trap tt (Ret (NormE (ECompVal v t) se))) c) s0
          (s0, mStmt (Ret (NormE (ECompVal v t) se)) c)) /\

(!exte c s1 s2 exte'.
     ^mng exte s1 (s2, exte') ==>
     ^mng (mStmt (Standalone exte) c) s1 (s2, mStmt (Standalone exte') c)) /\

(!v t se c s.
     is_null_se se ==>
     ^mng (mStmt (Standalone (NormE (ECompVal v t) se)) c) s
          (s, mStmt EmptyStmt c)) /\

(!guard guard' c t e s0 s.
    ^mng guard s0 (s, guard') ==>
    ^mng (mStmt (CIf guard t e) c) s0 (s, mStmt (CIf guard' t e) c)) /\

(!v t se thenstmt elsestmt c s.
    scalar_type t /\ is_null_se se /\ ~is_zero t v ==>
    ^mng (mStmt (CIf (NormE (ECompVal v t) se) thenstmt elsestmt) c) s
         (s, mStmt thenstmt c)) /\

(!v t se thenstmt elsestmt c s.
    scalar_type t /\ is_null_se se /\ is_zero t v ==>
    ^mng (mStmt (CIf (NormE (ECompVal v t) se) thenstmt elsestmt) c) s
         (s, mStmt elsestmt c)) /\

(* somewhat ugly that a bunch of blocks will accumulate around every
   iteration of the loop... *)
(!guard bdy c s.
     ^mng (mStmt (CLoop guard bdy) c) s
          (s, mStmt (CIf guard (Block F [] [bdy; CLoop guard bdy])
                               EmptyStmt) c)) /\

(!vds sts s c.
     ^mng (mStmt (Block F vds sts) c) s
          (s with stack updated_by (CONS (s.classmap,s.typemap,s.varmap)),
           mStmt (Block T vds sts) c)) /\

(!st s c stm tym vrm stk'.
     (s.stack = (stm,tym,vrm) :: stk') /\ final_stmt st ==>
     ^mng (mStmt (Block T [] [st]) c) s
          (s with <| stack := stk'; classmap := stm; typemap := tym;
                     varmap := vrm |>,
           mStmt st c)) /\

(!sts s c.
     ~(sts = []) ==>
     ^mng (mStmt (Block T [] (EmptyStmt::sts)) c) s
          (s, mStmt (Block T [] sts) c)) /\

(!sts exstmt s c.
     final_stmt exstmt /\ ~(exstmt = EmptyStmt) /\ ~(sts = []) ==>
     ^mng (mStmt (Block T [] (exstmt::sts)) c) s
          (s, mStmt (Block T [] [exstmt]) c)) /\

(!s0 s ty name vds sts c.
   vdeclare s0 ty name s ==>
   ^mng (mStmt (Block T (VDec ty name :: vds) sts) c) s0
        (s, mStmt (Block T vds sts) c)) /\

(!ty name exte exte' s0 s vds sts c.
   ^mng exte s0 (s, exte') ==>
   ^mng (mStmt (Block T (VDecInit ty name exte::vds) sts) c) s0
        (s, mStmt (Block T (VDecInit ty name exte'::vds) sts) c)) /\


(!dty name v ty v' se vds sts c s0 s.
   is_null_se se /\ vdeclare s0 dty name s /\
   parameter_coerce (v,ty) (v',dty) ==>
   ^mng (mStmt (Block T (VDecInit dty name (NormE (ECompVal v ty) se) :: vds)
                        sts) c) s
        (val2mem s (s.varmap ' name) v', mStmt (Block T vds sts) c)) /\

(!name info s vds sts c.
    ^mng (mStmt (Block T (VStrDec name info :: vds) sts) c) s
         (s with classmap updated_by (\sm. sm |+ (name,info)),
          mStmt (Block T vds sts) c)) `
end;


(* ----------------------------------------------------------------------
    how to evaluate a sequence of external declarations
   ---------------------------------------------------------------------- *)

val (emeaning_rules, emeaning_ind, emeaning_cases) = Hol_reln`
  (!s fval name rettype params body ftype edecls.
       ~(fval IN FDOM s.fndecode) /\ ~(name IN FDOM s.fnmap) /\
       ~(name IN FDOM s.typemap) /\
       (LENGTH fval = ptr_size ftype) /\
       (ftype = Function rettype (MAP SND params))
    ==>
       emeaning (FnDefn rettype name params body :: edecls) s
          (s with
            <| fnmap updated_by
                       (\fm. fm |+ (name, <| body := body;
                                             return_type := rettype;
                                             parameters := params |>));
               fnvals updated_by (\fm. fm |+ (name, fval));
               fndecode updated_by (\fm. fm |+ (fval, name));
               typemap updated_by (\tm. tm |+ (name, ftype)) |>,
           edecls)) /\

  (!s0 ty name s edecls.
     vdeclare s0 ty name s ==>
     emeaning (Decl (VDec ty name) :: edecls) s0 (copy2globals s, edecls)) /\

  (!s0 ty name exte exte' edecls s.
     meaning exte s0 (s, exte') ==>
     emeaning (Decl (VDecInit ty name exte) :: edecls) s0
              (s, Decl (VDecInit ty name exte') :: edecls)) /\

  (!s0 s name v ty dty v' edecls se.
     vdeclare s0 dty name s /\ parameter_coerce (v,ty) (v',dty) /\
     is_null_se se ==>
     emeaning (Decl (VDecInit dty name (NormE (ECompVal v ty) se)) :: edecls)
              s0
              (val2mem (copy2globals s) (s.varmap ' name) v',
               edecls)) /\

  (!s name info edecls.
     emeaning (Decl (VStrDec name info) :: edecls) s
              (copy2globals
                  (s with <| classmap updated_by
                                      (\sm. sm |+ (name,info)) |>),
               edecls))
`;



val _ = export_theory();



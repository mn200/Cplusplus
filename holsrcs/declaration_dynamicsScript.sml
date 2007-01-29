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
local
  open side_effectsTheory statesTheory operatorsTheory overloadingTheory
in end

val _ = new_theory "declaration_dynamics";

val _ = set_trace "inddef strict" 1

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
                  (SOME bytes = ptr_encode s n t' (default_path t')) /\
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

(* malloc s0 ty a is true if a is a valid address for a value of type ty,
   and is currently unallocated.

   If you are malloc-ing space for a class, then it will be for a most-derived
   class, which is they there are T's passed to sizeof and align. *)
val malloc_def = Define`
  malloc s0 ty a =
     ?sz aln. sizeof T (sizeofmap s0) ty sz /\
              align (sizeofmap s0) T ty aln /\
              DISJOINT (s0.allocmap UNION s0.hallocmap) (range_set a sz) /\
              ~(a = 0) /\ (a MOD aln = 0) /\
              a + sz <= 2 EXP (CHAR_BIT * ptr_size ty)
`

(* ----------------------------------------------------------------------
    clause 4's conversions
      referenced in 8.5 para 14 and elsewhere
   ---------------------------------------------------------------------- *)


(* - doesn't include lvalue-to-rvalue conversion - this is handled
     specially elsewhere because of the restrictions on accessing and
     reading memory at the same time.
   - doesn't worry about outer constness (assumes that it is being called
     in an initialisation setting, where consts can be initialised by non-
     consts and vice-versa).
   - OMITS (preventative) rules of 4.4 - these are checked statically
*)
val nonclass_conversion_def = Define`
  nonclass_conversion s (v1,ty1) (v2,ty2) =
    let ty1 = strip_const ty1
    and ty2 = strip_const ty2
    in
      (integral_type ty1 /\ integral_type ty2 \/
       ?ty0. (ty1 = Ptr ty0) /\ (ty2 = Ptr Void)) /\
      (?i. (INT_VAL ty1 v1 = SOME i) /\
           (SOME v2 = REP_INT ty2 i))
         \/
      (strip_ptr_const ty1 = strip_ptr_const ty2) /\ (v1 = v2)
         \/
      (?c1 c2 addr pth1 pth2.  (* this is an upcast *)
          (ty1 = Ptr (Class (LAST pth1))) /\ (ty2 = Ptr (Class c2)) /\
          (SOME v1 = ptr_encode s addr (Class c1) pth1) /\
          s |- c2 casts pth1 into pth2 /\
          (SOME v2 = ptr_encode s addr (Class c1) pth2))
`;


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

val vdeclare_def = Define`
  vdeclare s0 ty nm s =
     (?a sz rs.
         (rs = range_set a sz) /\
         object_type ty /\ malloc s0 ty a /\ sizeof T (sizeofmap s) ty sz /\
         (s = s0 with <| constmap :=
                            if const_type ty then s0.constmap UNION rs
                            else s0.constmap DIFF rs;
                         allocmap updated_by (UNION) rs;
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


val initA_constructor_call_def = Define`
  initA_constructor_call mdp cnm addr args =
      VDecInitA (Class cnm)
                (ObjPlace addr)
                (DirectInit
                   (mExpr (FnApp (ConstructorFVal mdp addr cnm) args) base_se))
`;

val initA_member_call_def = Define`
  initA_member_call ty addr args =
    case ty of
       Class cnm -> initA_constructor_call T cnm addr args
    || _ -> VDecInitA ty (ObjPlace addr) (CopyInit (mExpr (HD args) base_se))
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
     nonclass_conversion s0 (v,ty) (v',dty) /\
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
(!s0 ty1 nm a aopt ty2 p p' s se f.
     is_null_se se /\
     ((f = CopyInit) \/ (f = DirectInit)) /\
     (if class_type ty1 then
        s0 |- dest_class ty1 casts p into p'
      else (p' = p)) /\
     (s = s0 with varmap updated_by (\fm. fm |+ (nm, (a,p'))))
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

val _ = export_theory();



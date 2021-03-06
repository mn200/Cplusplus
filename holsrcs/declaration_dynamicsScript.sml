(* Dynamic Semantics of C++ declarations *)

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

val upd4_def = Define`
  upd4 f (a,b,c,d) = (a,b,c,f d)
`;
val sel4_def = Define`
  sel4 (a,b,c,d) = d
`;


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
                  (SOME bytes = ptr_encode s n t' (SND (default_path t'))) /\
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
    pointers to member, including the null member pointer
   ---------------------------------------------------------------------- *)

val encode_offset_def = new_specification(
  "encode_offset_def",
  ["encode_offset", "null_member_ptr"],
  prove(``?(f:CPP_ID -> IDComp -> byte list option) null.
              (!cnm1 sf1 cnm2 sf2 bl.
                  (f cnm1 sf1 = SOME bl) /\ (f cnm2 sf2 = SOME bl) ==>
                  (cnm1 = cnm2) /\ (sf1 = sf2)) /\
              (!cnm sf bl. (f cnm sf = SOME bl) ==>
                           (LENGTH bl = ptr_size Void) /\
                           ~(bl = null)) /\
              (LENGTH null = ptr_size Void)``,
        Q.EXISTS_TAC `\x y. NONE` THEN SRW_TAC [][] THEN
        Q.EXISTS_TAC `GENLIST (\n. ARB) (ptr_size Void)` THEN
        SRW_TAC [][rich_listTheory.LENGTH_GENLIST]));

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
           (SOME v2 = REP_INT ty2 i)) (* includes null pointer conversion *)
         \/
      (strip_ptr_const ty1 = strip_ptr_const ty2) /\ (v1 = v2)
         \/
      (?c1 c2 addr pth1 pth2.  (* this is an upcast *)
          (ty1 = Ptr (Class (LAST pth1))) /\ (ty2 = Ptr (Class c2)) /\
          (SOME v1 = ptr_encode s addr (Class c1) pth1) /\
          (s,{}) |- c2 casts pth1 into pth2 /\
          (SOME v2 = ptr_encode s addr (Class c1) pth2))
         \/
      (?ty0 base derived p fld.
          (ty1 = MPtr base ty0) /\ (ty2 = MPtr derived ty0) /\
          (s,{}) |- path derived to base unique /\
          (derived, p) IN rsubobjs (s,{}) /\ (* ensures no virtual base *)
          (LAST p = base) /\
          (v2 = v1) /\
          ((SOME v1 = encode_offset base fld) \/ (v1 = null_member_ptr)))
         \/
      (?ty0 c. (* null pointer conversion for pointers to member *)
          (ty1 = Signed Int) /\ (SOME v1 = REP_INT (Signed Int) 0) /\
          (ty2 = MPtr c ty0) /\ (v2 = null_member_ptr))
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
      if (?virtp bdy statp prot.
             MEM (Destructor virtp bdy, statp, prot) i0.fields)
      then
        (i0,Destructor INSERT set)
      else (i0 with fields updated_by CONS (Destructor F NONE, F, Public),
            set)
    in
      constructor (destructor (info0, {}))
`




val _ = overload_on ("EX", ``statements$EX``)
val _ = overload_on ("ST", ``statements$ST``)

val state_typemap_def = Define`
  state_typemap s = FUN_FMAP (\id. THE (lookup_type s id))
                       { id | ?ty. lookup_type s id = SOME ty }
`
val _ = add_record_field ("typemap", ``state_typemap``)

(* updates "dynamic" map only *)
val state_updtypemap_def = Define`
  state_updtypemap f s =
    s with env := FTNode (item s.env with typemap updated_by f)
                         (map s.env)
`;
val _ = add_record_fupdate("typemap", ``state_updtypemap``)

val state_classmap_def = Define`
  state_classmap s = FUN_FMAP (\id. THE (lookup_class s id))
                              { id | ?c. lookup_class s id = SOME c }
`;
val _ = add_record_field ("classmap", ``state_classmap``)

(* binds a class-member name to an address.  The member might be a static
   variable, or a reference.  If the latter, then the pcopt field will be
   SOME a0, where a0 is the address of the parent. *)
val cenv_new_addr_binding_def = Define`
  (cenv_new_addr_binding [sf] s pcopt a (cenv : IDComp |-> class_env) =
     let cdata = cenv ' sf in
     let (ci,udfs) = THE (item cdata).info
     in
        if ?prot ty. MEM (FldDecl (IDName s) ty,T,prot) ci.fields then
          cenv |+ (sf, FTNode (item cdata with statvars
                                 updated_by (\fm. fm |+ (s,a)))
                              (map cdata))
        else
          cenv |+ (sf, FTNode (item cdata with refs
                                 updated_by (\fm. fm |+ ((s,THE pcopt), a)))
                              (map cdata))) /\
  (cenv_new_addr_binding (sf::sfs) s pcopt a cenv =
     cenv |+ (sf, FTNode (item (cenv ' sf))
                         (cenv_new_addr_binding sfs s pcopt a
                                                (map (cenv ' sf)))))
`;

(* binds an id to an address in an environment.  The id might be associated
   with a class *)
val enew_addr_binding_def = Define`
  (enew_addr_binding [] s pcopt a env =
     FTNode (item env with varmap updated_by (\fm. fm |+ (s,a)))
            (map env)) /\
  (enew_addr_binding (sf :: sfs) s pcopt a env =
     if sf IN FDOM (item env).classenv then
       FTNode (item env with classenv updated_by
                 cenv_new_addr_binding (sf :: sfs) s pcopt a)
              (map env)
     else
       let s' = sfld_string sf
       in
         FTNode
           (item env)
           (map env |+ (s', enew_addr_binding sfs s pcopt a (map env ' s'))))
`;

val new_addr_binding_def = Define`
  (new_addr_binding (IDConstant T sfs (IDName str)) pcopt a s =
      s with genv updated_by enew_addr_binding sfs str pcopt a) /\
  (new_addr_binding (IDConstant F sfs (IDName str)) pcopt a s =
      s with env updated_by enew_addr_binding sfs str pcopt a)
`;

(* setting up a new type binding is only necessary for dynamically allocated
   variables - all other sorts will already have their type information
   recorded in the state *)
val new_type_binding_def = Define`
  (new_type_binding (IDConstant F [] (IDName str)) ty s =
     s with env := FTNode (item s.env with typemap
                             updated_by (\fm. fm |+ (IDName str, ty)))
                          (map s.env)) /\
  (new_type_binding id ty s = s)
`;

val vdeclare_def = Define`
  vdeclare s0 ty nm s =
     (?a sz rs.
         (rs = range_set a sz) /\
         object_type ty /\ malloc s0 ty a /\ sizeof T (sizeofmap s) ty sz /\
         (s = (new_addr_binding nm NONE (a,default_path ty) o
               new_type_binding nm ty)
              (s0 with <| constmap :=
                            if const_type ty then s0.constmap UNION rs
                            else s0.constmap DIFF rs;
                         allocmap updated_by (UNION) rs |>)))
        \/
     (?ty0.
        (ty = Ref ty0) /\
        (* before the reference gets initialised, what should its value be?
           Or, what does an uninitialised reference look like?
           Certainly, references must be initialised by valid objects, so
           attempting
              int &y = y ;
           must be bad.  So, let's make it a reference to a guaranteed bad
           address, 0.  We can't just leave the varmap unchanged as
           the declaration of a variable masks other variables of the same
           name.  See notes/ref001.cpp *)
        (s = (new_addr_binding nm NONE (0,default_path ty) o
              new_type_binding nm ty0) s0))
`;


val initA_constructor_call_def = Define`
  initA_constructor_call mdp subobjp cnm addr args =
      VDecInitA
        (Class cnm)
        (ObjPlace addr)
        (DirectInit
           (EX (FnApp (ConstructorFVal mdp subobjp addr cnm) args) base_se))
`;

val initA_member_call_def = Define`
  initA_member_call parent_addr alvl nm ty addr args =
    case strip_const ty of
       Class cnm -> initA_constructor_call T alvl cnm addr args
    || Ref ty0 -> VDecInitA ty
                            (RefPlace (SOME parent_addr) nm)
                            (CopyInit (EX (HD args) base_se))
    || _ -> VDecInitA ty
                      (ObjPlace addr)
                      (CopyInit (EX (HD args) base_se))
`;


(* 8.5 p5 : zero-initialisation *)
(* TODO: handle unions *)
val (zero_init_rules, zero_init_ind, zero_init_cases) = Hol_reln`
   (!s mdp ty a.
     scalar_type ty
   ==>
     zero_init s mdp ty a [VDecInitA ty
                                     (ObjPlace a)
                                     (DirectInit (EX (Cnum 0) base_se))])

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
(* used to
   - initialise non-POD class members/bases (or arrays thereof) that are
     not mentioned in a constructor's mem-initializers (first two clauses)
       (12.6.2 p4, 8.5 p9)
   - that's it.  The third clause looks redundant, and is commented out.
     This redundancy is an existing Defect Report, #509.
*)
(* TODO: handle unions *)
val (default_init_rules, default_init_ind, default_init_cases) = Hol_reln`
   (!s mdp subobjp cnm a.
     ~PODstruct s cnm
   ==>
     default_init s mdp subobjp (Class cnm) a
                  [initA_constructor_call mdp subobjp cnm a []])

   /\

   (!s mdp subobjp ty n a sz sub_inits.
     sizeof T (sizeofmap s) ty sz /\
     listRel (\m l. default_init s mdp subobjp ty (a + m * sz) l)
             (GENLIST I n)
             sub_inits
   ==>
     default_init s mdp subobjp (Array ty n) a (FLAT sub_inits))

(*    /\

   (!s mdp ty a inits.
     ~array_type ty /\
     (!cnm. (ty = Class cnm) ==> PODstruct s cnm) /\
     zero_init s mdp ty a inits
   ==>
     default_init s mdp ty a inits)

*)
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
    parameters (12.6.2 p3)
*)
(* TODO: handle unions *)
val (value_init_rules, value_init_ind, value_init_cases) = Hol_reln`
   (!s mdp alvl cnm addr.
     has_user_constructor s cnm
   ==>
     value_init s mdp alvl (Class cnm) addr
                [initA_constructor_call mdp alvl cnm addr []])

   /\

   (!s mdp alvl cnm a sub_inits.
     ~has_user_constructor s cnm /\
     listRel (\(cc,off) l.
                value_init s (nsdp cc) alvl (cc_type cc) (a + off) l)
             (init_order_offsets s mdp cnm)
             sub_inits
   ==>
     value_init s mdp alvl (Class cnm) a (FLAT sub_inits))

   /\

   (!s mdp alvl ty n addr sz sub_inits.
     sizeof T (sizeofmap s) ty sz /\
     listRel (\n l. value_init s T alvl ty (addr + n * sz) l)
             (GENLIST I n)
             sub_inits
   ==>
     value_init s mdp alvl (Array ty n) addr (FLAT sub_inits))

   /\

   (!s mdp alvl a ty inits.
     (!ty0. ~(ty = Class ty0)) /\ ~array_type ty /\
     zero_init s mdp ty a inits
   ==>
     value_init s mdp alvl ty a inits)
`;

val record_creation_def = Define`
  record_creation alvl a cnm stk =
    let stk' = update_nth_rev (LENGTH stk) (upd4 (CONS (a,cnm))) stk
    in
      if alvl < LENGTH stk /\ ~MEM (a,cnm) (sel4 (REV_EL alvl stk)) then
        update_nth_rev alvl (upd4 (CONS (a,cnm))) stk'
      else
        stk'
`;

(* example:
     C : B1, B2 : A1, A2

   constructor for C calls constructor for B1 and B2, latter of which calls
   constructor for A1 and A2.  Say C's a-level is 4.
   If we're in constructor for A2 (having successfully completed construction
   of A1), and it looks like

     A2::A2(argsA2) mem-inits { localdecs; ... }

   and something raises an exception in the ..., then the objects in
   localdecs, mem-inits and argsA2 will need to be destroyed first in
   that order.  Then, we pop out to the B2 constructor.  Assume this
   looks like:

     B2::B2(argsB2) : A1(params1), A2(params2) { .... }

   at this point, A1 should be killed (_not_, argsB2).  Then the args
   should be killed followed by popping out to C's constructor, which
   looks like

     C::C(argsC) : B1(paramsB1), B2(paramsB2) { ... }

   then we should kill B1, followed by argsC.  And that will be the extent
   of the killing that's necessary.

   This will be implemented by putting all objects into potentially
   two positions within the stack, one at its a-level, and two at its
   "actual level", i.e., that block level where it was allocated "for
   real".  This is then used if an exception is raised.
 *)


val exceptional_destructors_def = Define`
  exceptional_destructors (h :: t) =
    let dest_these = sel4 h in
    let t' = MAP (upd4 (FILTER (\e. ~MEM e dest_these))) t
  in
    (dest_these,upd4 (K []) h :: t')
`

val normal_destructors_def = Define`
  normal_destructors (h :: t) =
    let d0 = sel4 h in
    let d = FILTER (\e. ~EXISTS (EXISTS ((=) e) o sel4) t) d0
  in
    (d,upd4 (K []) h::t)
`;


val realise_destructor_calls_def = Define`
  (* parameters
      exp           : T iff we are leaving a block because of an exception
      s0            : starting state, where there is a non-empty list
                      of things to destroy as the (addr#CPP_ID) list
                      component of s.stack.  If this is not an exceptional
                      exit, then objects that appear twice in the stack
                      are not destroyed at this level.  If this is, the
                      object gets destroyed (and also pulled out of the
                      stack at its a-level).
     outputs
      destcals      : list of statements with explicit destructor
                      calls for those objects that need destroying
      s             : resulting state, with updated stack lists (but with
                      the top element still un-popped).
  *)
  realise_destructor_calls exp s0 =
    let cloc2call (a, cnm) = DestructorCall a cnm in
    let (dests,stk') = if exp then exceptional_destructors s0.stack
                       else normal_destructors s0.stack
    in
        (MAP cloc2call dests, s0 with stack := stk')
`;

val callterminate_def = Define`
  callterminate =
    FnApp (Var  (IDConstant T [IDName "std"] (IDName "terminate"))) []
`;

(* sets up destructor calls for an expression that has finished evaluating and
   has created rvalue objects along the way *)
val expression_destruction_def = Define`
  expression_destruction (s0,e0,se0) (s,e) =
     ?destcalls.
        ~(sel4 (HD s0.stack) = []) /\
        final_value (EX e0 se0) /\
        ((destcalls,s) = realise_destructor_calls F s0) /\
        (e = FOLDR CommaSep e destcalls)
`;

(* sets up destructor calls for a piece of expression syntax that has become
   a exception statement, but which has created rvalue objects along the way *)
val exception_destruction_def = Define`
  exception_destruction (s0, exst) (s, newst) =
    ?st c' destcalls wrap.
       is_exnval exst /\
       (exst = ST st c') /\
       ~(sel4 (HD s0.stack) = []) /\
       ((destcalls,s) = realise_destructor_calls T s0) /\
       (wrap = (\e. Catch (Standalone (EX e base_se))
                          [(NONE, Standalone (EX callterminate base_se))])) /\
       (newst = Block T [] (MAP wrap destcalls ++ [st]))
`;



val _ = print "Defining (utility) declaration relation\n"
(* this relation performs the various manipulations on declaration syntax
   that are independent of the rest of the meaning relation *)
(* TODO: handle construction of arrays of objects, which happens in order
   of increasing subscripts (see 12.6 p3) *)
val (declmng_rules, declmng_ind, declmng_cases) = Hol_reln`

(* RULE-ID: decl-vdec-nonclass *)
(!s0 ty name s.
     vdeclare s0 ty name s /\
     object_type ty /\
     ~class_type (strip_array ty)
   ==>
     declmng mng (VDec ty name, s0) ([], s)
)

   /\

(* RULE-ID: decl-vdec-class *)
(* if called on to declare a class variable, then the default, argument-less
   constructor gets called *)
(!s0 name cnm.
     T
   ==>
     declmng mng (VDec (Class cnm) name, s0)
                 ([VDecInit (Class cnm) name (DirectInit0 [])], s0))

   /\

(* RULE-ID: decl-vdec-array-class *)
(* similarly, if called onto declare an array, then any nested constructors
   will be called with no arguments *)
(!s0 s a name cnm ty subdecls sz.
     (strip_array ty = Class cnm) /\
     array_type ty /\
     vdeclare s0 ty name s /\
     sizeof T (sizeofmap s0) (Class cnm) sz /\
     (subdecls =
       GENLIST (\n. VDecInitA
                      (strip_array ty)
                      (ObjPlace (a + n * sz))
                      (DirectInit
                         (EX (FnApp (ConstructorFVal T
                                       (LENGTH s0.stack)
                                       (a + n * sz) cnm)
                                    [])
                                base_se)))
               (array_size ty))
   ==>
     declmng mng (VDec ty name, s0) (subdecls, s))

   /\


(* decl-vdecinit-start-evaluate rules switch from VDecInit to
   VDecInitA, reflecting allocation of space for the "object".  The
   vdeclare relation handles functions and references as well.
   Functions can't be initialised, so they won't appear here.
   References must be initialised, and the behaviour of vdeclare on
   references is to put them into the typemap, but to allocate no
   space, and to put them into the varmap at address 0.

*)

(* RULE-ID: decl-vdecinit-start-evaluate-direct-class *)
(* the subobjp flag of the ConstructorFVal is F because this is a top-level
   declaration of a object. *)
(!s0 ty cnm name args s1 a pth.
     (strip_const ty = Class cnm) /\
     vdeclare s0 ty name s1 /\
     (SOME (a,pth) = lookup_addr s1 name)
   ==>
     declmng mng
             (VDecInit ty name (DirectInit0 args), s0)
             ([VDecInitA ty
                 (ObjPlace a)
                 (DirectInit
                    (EX (FnApp (ConstructorFVal T (LENGTH s1.stack) a cnm)
                               args)
                        base_se))],
              s1)
)

   /\

(* RULE-ID: decl-vdecinit-copy-becomes-direct *)
(* corresponds to 8.5 p14, where there is a copy initialisation, and
   "source type is the same class as, or a derived class of, the class of
    the destination" *)
(* NOTE: this rule precludes constructing a temporary directly into a new
         object value, as it fires once the initializer has been fully
         evaluated *)
(!ty a arg argty argnm pth s0 se cnm.
     (strip_const ty = Class cnm) /\
     (arg = LVal a argty pth) /\
     (strip_const argty = Class argnm) /\
       (* note how argnm is ignored, used here just to establish that
          the type of the argument really is of class type.  argnm gives
          the dynamic type, and we're interested in the static type *)
     (s0,{}) |- path (LAST pth) to cnm unique
       (* arg is equal to or a derived class *)
   ==>
     declmng mng
             (VDecInitA ty (ObjPlace a) (CopyInit (EX arg se)), s0)
             ([VDecInitA ty
                  (ObjPlace a)
                  (DirectInit
                  (EX
                     (FnApp (ConstructorFVal T (LENGTH s0.stack) a cnm)
                            [arg])
                     se))],
              s0))

   /\

(* RULE-ID: decl-init-start-eval-dnonclass *)
(* A direct initialisation of a non-class object is the same as a
   copy-initialisation *)
(!s0 ty name arg s a pth loc.
     ~class_type ty /\
     vdeclare s0 ty name s /\
     (SOME (a,pth) = lookup_addr s name) /\
     (loc = if ref_type ty then RefPlace NONE name else ObjPlace a)
   ==>
     declmng mng
             (VDecInit ty name (DirectInit0 [arg]), s0)
             ([VDecInitA ty loc (CopyInit (EX arg base_se))], s))

   /\

(* RULE-ID: decl-init-start-eval-copy *)
(!s0 ty name arg s a pth loc.
     vdeclare s0 ty name s /\
     (SOME (a,pth) = lookup_addr s name) /\
     (loc = if ref_type ty then RefPlace NONE name else ObjPlace a)
   ==>
     declmng mng
             (VDecInit ty name (CopyInit arg), s0)
             ([VDecInitA ty loc (CopyInit arg)], s)
)

   /\


(* RULE-ID: decl-vdecinit-evaluation *)
(!s0 ty loc exte exte' s f.
     mng (s0, exte) (s, exte') /\
     ((f = CopyInit) \/ (f = DirectInit))
   ==>
     declmng mng (VDecInitA ty loc (f exte), s0)
                 ([VDecInitA ty loc (f exte')], s)
)

   /\

(* RULE-ID: decl-vdecinit-lval2rval *)
(!ty loc e0 se0 s0 s e se f.
     lval2rval (s0,e0,se0) (s,e,se) /\
     ~ref_type ty /\
     ((f = CopyInit) /\ ~class_type (strip_const ty) \/
      (f = DirectInit))
   ==>
     declmng mng (VDecInitA ty loc (f (EX e0 se0)), s0)
                 ([VDecInitA ty loc (f (EX e se))], s)
)

   /\

(* RULE-ID: decl-vdecinit-finish *)
(* for non-class, non-reference types *)
(!s0 s e v ty dty v' se a rs f amap env rest thisv.
     (e = ECompVal v ty) /\
     nonclass_conversion s0 (v,ty) (v',dty) /\
     is_null_se se /\
     ~class_type dty /\
     (s = val2mem (s0 with initmap updated_by (UNION) rs) a v') /\
     (rs = range_set a (LENGTH v')) /\
     ((f = CopyInit) \/ (f = DirectInit)) /\
     (s.stack = (env,thisv,amap,[]) :: rest)
   ==>
     declmng mng
        (VDecInitA dty (ObjPlace a) (f (EX e se)), s0)
        ([], s with <| stack := rest; allocmap := amap|>)
)

   /\

(* RULE-ID: decl-vdecinit-finish-ref *)
(* if isSome, aopt is the address of a containing class *)
(!s0 ty1 refnm a aopt ty2 p p' s se f env thisv amap rest.
     is_null_se se /\
     ((f = CopyInit) \/ (f = DirectInit)) /\
     (if class_type ty1 then
        (s0,{}) |- dest_class ty1 casts p into p'
      else (p' = p)) /\
     (s = new_addr_binding refnm aopt (a,dest_class ty2,p') s0) /\
     (s.stack = (env,thisv,amap,[]) :: rest)
   ==>
     declmng mng
             (VDecInitA (Ref ty1)
                        (RefPlace aopt refnm)
                        (f (EX (LVal a ty2 p) se)), s0)
             ([], s with <| stack := rest; allocmap := amap |>)
)

   /\

(* RULE-ID: decl-vdecinit-direct-class-finish *)
(* differences with decl-vdecinit-finish:
     * no need to update memory, or init_map as this will have all been
       done by the constructor
*)
(!cnm alvl a se0 s0 s env thisv amap rest.
     is_null_se se0 /\
     (s0.stack = (env,thisv,amap,[]) :: rest) /\
     (s = s0 with <| stack := rest; allocmap := amap |>)
   ==>
     declmng mng
       (VDecInitA (Class cnm) (ObjPlace a)
                  (DirectInit (EX (ConstructedVal alvl a cnm) se0)),
        s0)
       ([], s with stack updated_by record_creation alvl a cnm)
)

   /\

(* RULE-ID: decl-parameter-copy-elision *)
(!cnm nm a alvl s0.
     T
   ==>
     declmng mng
       (VDecInit (Class cnm) nm
                 (CopyInit (EX (NoScope (ConstructedVal alvl a cnm)) base_se)),
        s0)
       ([], new_addr_binding nm NONE (a,cnm,[cnm])
              (new_type_binding nm (Class cnm) s0))
)

   /\

(* RULE-ID: decl-fncall-copy-elision *)
(!fnc fnid ftype thisobj s0 args cnm params body a se.
     (fnc = FVal fnid ftype thisobj) /\
     find_best_fnmatch s0 fnid (MAP valuetype args)
                       (Class cnm) params body
   ==>
     declmng mng
       (VDecInitA (Class cnm) (ObjPlace a)
                  (CopyInit (EX (FnApp_sqpt NONE fnc args) se)),
        s0)
       ([VDecInitA (Class cnm) (ObjPlace a)
                   (CopyInit (EX (FnApp_sqpt
                                      (SOME(LENGTH s0.stack,a,cnm))
                                      fnc
                                      args)
                                 se))],
        s0)
)

   /\

(* RULE-ID: decl-class-copy-finishes *)
(!se e a alvl cnm s s' env thisv amap rest.
     is_null_se se /\
     (e = ConstructedVal alvl a cnm) /\
     (s.stack = (env,thisv,amap,[]) :: rest) /\
     (s' = s with <| stack := rest; allocmap := amap |>)
   ==>
     declmng mng
       (VDecInitA (Class cnm) (ObjPlace a) (CopyInit (EX e se)), s)
       ([], s' with stack updated_by record_creation alvl a cnm)
)

   /\

(* RULE-ID: decl-class-copy-call-copy *)
(!s se e a cnm.
     final_value (EX e se) /\
     (!alvl. ~(e = ConstructedVal alvl a cnm))
   ==>
     declmng mng
       (VDecInitA (Class cnm) (ObjPlace a) (CopyInit (EX e se)), s)
       ([VDecInitA (Class cnm) (ObjPlace a)
                   (CopyInit (EX (FnApp_sqpt NONE
                                    (ConstructorFVal T
                                       (LENGTH s.stack)
                                       a
                                       cnm)
                                    [e])
                                 base_se))],
        s)
)

   /\

(* RULE-ID: decl-expr-destroys-rvalues *)
(!f ty pl e0 se0 s0 e s.
     ((f = CopyInit) \/ (f = DirectInit)) /\
     expression_destruction (s0,e0,se0) (s,e)
   ==>
     declmng mng
        (VDecInitA ty pl (f (EX e0 se0)), s0)
        ([VDecInitA ty pl (f (EX e se0))], s)
)

`

val declmng_MONO = store_thm(
  "declmng_MONO",
  ``(!x y. P x y ==> Q x y) ==>
    (declmng P s1 s2 ==> declmng Q s1 s2)``,
  STRIP_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`s2`, `s1`] THEN
  HO_MATCH_MP_TAC declmng_ind THEN
  REPEAT STRIP_TAC THEN
  FIRST (map (fn th => MATCH_MP_TAC th THEN SRW_TAC [][] THEN METIS_TAC [])
             (CONJUNCTS
                (SIMP_RULE pure_ss [FORALL_AND_THM] declmng_rules))));
val _ = export_mono "declmng_MONO"

val _ = export_theory();



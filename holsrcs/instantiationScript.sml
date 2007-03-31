(* Matching and instantiation operations on programs *)

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

val _ = new_theory "instantiation"


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

val is_var_type_def = Define`
  (is_var_type (TypeID cid) = T) /\
  (is_var_type _ = F)
`;

val dest_var_type_def = Define`
  (dest_var_type (TypeID cid) = cid)
`;

val typeid_def = Define`
  (typeid (TypeID cid) = SOME cid) /\
  (typeid _ = NONE)
`;
val _ = export_rewrites ["typeid_def"]


(* instantiate a type with template arguments *)
val type_inst_defn = Hol_defn "type_inst" `
  (type_inst sigma (TypeID cid) = cppid_inst sigma cid) /\
  (type_inst sigma (Ptr ty) = OPTION_MAP Ptr (type_inst sigma ty)) /\
  (type_inst sigma (MPtr nm ty) =
     OP2CMB MPtr
            (case cppid_inst sigma nm of NONE -> NONE || SOME ty -> typeid ty)
            (type_inst sigma ty)) /\
  (type_inst sigma (Ref ty) = OPTION_MAP Ref (type_inst sigma ty)) /\
  (type_inst sigma (Array ty n) =
     OPTION_MAP (\ty. Array ty n) (type_inst sigma ty)) /\
  (type_inst sigma (Function ty tylist) =
     OP2CMB Function (type_inst sigma ty) (olmap (type_inst sigma) tylist)) /\
  (type_inst sigma (Const ty) = OPTION_MAP Const (type_inst sigma ty)) /\
  (type_inst sigma (Class cid) = SOME (Class cid)) /\
  (type_inst sigma ty = SOME ty)

    /\

  (* id instantiation returns a type.  The type may just be a TypeID,
     possibly representing no change, or a "real" type. *)
  (cppid_inst sigma (IDVar s) = SOME (sigma.typemap s)) /\
  (cppid_inst sigma (IDFld cid fld) =
     OPTION_MAP TypeID
                (OP2CMB IDFld
                        (case cppid_inst sigma cid of
                            NONE -> NONE
                         || SOME ty -> typeid ty)
                        (sfld_inst sigma fld))) /\
  (cppid_inst sigma (IDTempCall tempid tempargs) =
     OPTION_MAP (TypeID o IDTempCall (tempid_inst sigma tempid))
                (olmap (temparg_inst sigma) tempargs)) /\
  (cppid_inst sigma (IDConstant tnm) = SOME (TypeID (IDConstant tnm)))

    /\

  (temparg_inst sigma (TType ty) = OPTION_MAP TType (type_inst sigma ty)) /\
  (temparg_inst sigma (TTemp tid) = SOME (TTemp (tempid_inst sigma tid))) /\
  (temparg_inst sigma (TVal tva) =
      OPTION_MAP TVal (temp_valarg_inst sigma tva))

    /\

  (temp_valarg_inst sigma (TNum i) = SOME (TNum i)) /\
  (temp_valarg_inst sigma (TObj id) =
      OPTION_MAP TObj (case cppid_inst sigma id of
                          NONE -> NONE
                       || SOME ty -> typeid ty)) /\
  (temp_valarg_inst sigma (TMPtr id ty) =
      OP2CMB TMPtr
             (case cppid_inst sigma id of NONE-> NONE || SOME ty -> typeid ty)
             (type_inst sigma ty)) /\
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
    Induct_on `tylist` THEN SRW_TAC [][] THEN
    SRW_TAC [ARITH_ss][] THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `tempargs` THEN SRW_TAC [][] THEN
    SRW_TAC [ARITH_ss][] THEN RES_TAC THEN DECIDE_TAC,
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
    (!id. cppid_inst empty_inst id = SOME (TypeID id)) /\
    (!ta. temparg_inst empty_inst ta = SOME ta) /\
    (!tva. temp_valarg_inst empty_inst tva = SOME tva) /\
    (!sfld. sfld_inst empty_inst sfld = SOME sfld)``,
  Q_TAC SUFF_TAC
   `(!s ty. (s = empty_inst) ==> (type_inst s ty = SOME ty)) /\
    (!s id. (s = empty_inst) ==> (cppid_inst s id = SOME (TypeID id))) /\
    (!s ta. (s = empty_inst) ==> (temparg_inst s ta = SOME ta)) /\
    (!s tva. (s = empty_inst) ==> (temp_valarg_inst s tva = SOME tva)) /\
    (!s sfld. (s = empty_inst) ==> (sfld_inst s sfld = SOME sfld))`
   THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC type_inst_ind THEN
  SRW_TAC [][] THEN SRW_TAC [][] THENL [
    `olmap (\a. type_inst empty_inst a) tylist = SOME tylist`
       by (Induct_on `tylist` THEN SRW_TAC [][empty_inst_def]) THEN
    SRW_TAC [][],
    SRW_TAC [][empty_inst_def],
    SRW_TAC [ETA_ss] [] THEN Induct_on `tempargs` THEN SRW_TAC [][],
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

fun FTRY tac = TRY (tac THEN NO_TAC)



val cppid_non_typeid = store_thm(
  "cppid_non_typeid",
  ``(cppid_inst s id = SOME ty) /\ (typeid ty = NONE) ==>
    ?nm. (id = IDVar nm) /\ (s.typemap nm = ty)``,
  Cases_on `id` THEN SRW_TAC [][] THENL [
    Cases_on `typeid ty = NONE` THEN SRW_TAC [][] THEN
    Cases_on `ty = TypeID z` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [],

    Cases_on `typeid ty = NONE` THEN SRW_TAC [][] THEN
    DISJ2_TAC THEN STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [],

    Cases_on `typeid ty = NONE` THEN SRW_TAC [][] THEN
    STRIP_TAC THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
  ]);

val option_case_EQ_SOME = store_thm(
  "option_case_EQ_SOME",
  ``(option_case NONE f v = SOME v0) =
        ?v0'. (v = SOME v0') /\ (f v0' = SOME v0)``,
  Cases_on `v` THEN SRW_TAC [][]);
val _ = export_rewrites ["option_case_EQ_SOME"]


val inst_comp_thm = store_thm(
  "inst_comp_thm",
  ``(!id1 s1 s2 ty2 id3 ty4.
        (cppid_inst s1 id1 = SOME ty2) /\
        (typeid ty2 = SOME id3) /\
        (cppid_inst s2 id3 = SOME ty4) ==>
        (cppid_inst (inst_comp s2 s1) id1 = SOME ty4)) /\
    (!sfld1 sfld2 sfld3 s1 s2.
        (sfld_inst s1 sfld1 = SOME sfld2) /\
        (sfld_inst s2 sfld2 = SOME sfld3) ==>
        (sfld_inst (inst_comp s2 s1) sfld1 = SOME sfld3)) /\
    (!ta1 ta2 ta3 s1 s2.
        (temparg_inst s1 ta1 = SOME ta2) /\
        (temparg_inst s2 ta2 = SOME ta3) ==>
        (temparg_inst (inst_comp s2 s1) ta1 = SOME ta3)) /\
    (!tva1 tva2 tva3 s1 s2.
        (temp_valarg_inst s1 tva1 = SOME tva2) /\
        (temp_valarg_inst s2 tva2 = SOME tva3) ==>
        (temp_valarg_inst (inst_comp s2 s1) tva1 = SOME tva3)) /\
    (!ty1 ty2 ty3 s1 s2.
        (type_inst s1 ty1 = SOME ty2) /\
        (type_inst s2 ty2 = SOME ty3) ==>
        (type_inst (inst_comp s2 s1) ty1 = SOME ty3)) /\
    (!tal1 tal2 tal3 s1 s2.
        (olmap (temparg_inst s1) tal1 = SOME tal2) /\
        (olmap (temparg_inst s2) tal2 = SOME tal3) ==>
        (olmap (temparg_inst (inst_comp s2 s1)) tal1 = SOME tal3)) /\
    (!tyl1 tyl2 tyl3 s1 s2.
        (olmap (type_inst s1) tyl1 = SOME tyl2) /\
        (olmap (type_inst s2) tyl2 = SOME tyl3) ==>
        (olmap (type_inst (inst_comp s2 s1)) tyl1 = SOME tyl3))``,
  Induct THEN SRW_TAC [][] THEN
  FTRY (SRW_TAC[][]) THEN FTRY (FULL_SIMP_TAC (srw_ss()) []) THEN
  FTRY (RES_TAC THEN SRW_TAC [][]) THENL [
    (* IDVar case *)
    Cases_on `s1.typemap s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][inst_comp_def],

    (* IDFld case *)
    SRW_TAC [DNF_ss][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    PROVE_TAC [],

    (* IDTempCall *)
    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [],

    (* IDConstant *)
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [],

    (* SFTempCall *)
    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [],

    (* TObj *)
    FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC [],

    (* TMPtr *)
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN PROVE_TAC [],

    (* TVAVar *)
    SRW_TAC [][inst_comp_def],

    (* MPtr *)
    FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC [],

    (* Function (type) case *)
    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [],

    (* typeid case (?) *)
    Cases_on `typeid ty2` THENL [
      `?nm. (id1 = IDVar nm) /\ (s1.typemap nm = ty2)`
          by METIS_TAC [cppid_non_typeid] THEN
      SRW_TAC [][inst_comp_def],
      `ty2 = TypeID x`
         by (Cases_on `ty2` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
      FULL_SIMP_TAC (srw_ss()) []
    ]
  ]);

(* SANITY theorem = comment under definition 2 to the effect <= is
   transitive *)
val type_match_trans = store_thm(
  "type_match_trans",
  ``!(ty1:CPP_Type) ty2 ty3. ty1 <= ty2 /\ ty2 <= ty3 ==> ty1 <= ty3``,
  SRW_TAC [][type_match_def] THEN Q.EXISTS_TAC `inst_comp s' s` THEN
  SRW_TAC [][inst_comp_thm]);

val is_renaming_def = Define`
  is_renaming s = (!v. ?nm. s.typemap v = TypeID (IDVar nm)) /\
                  (!v. ?nm. s.tempmap v = TemplateVar nm) /\
                  (!v. ?nm. s.valmap v = TVAVar nm)
`;

val empty_inst_is_renaming = store_thm(
  "empty_inst_is_renaming",
  ``is_renaming empty_inst``,
  SRW_TAC [][empty_inst_def, is_renaming_def]);

val tidinst_sz_def = Define`
  (tidinst_sz (TemplateConstant n) = 1n) /\
  (tidinst_sz (TemplateVar s) = 0)
`;
val _ = export_rewrites ["tidinst_sz_def"]

val tempid_inst_size = store_thm(
  "tempid_inst_size",
  ``tidinst_sz tid <= tidinst_sz (tempid_inst s tid)``,
  Cases_on `tid` THEN SRW_TAC [][]);

val tyinst_sz_def = Define`
  (tyinst_sz (Class cid) = 2) /\
  (tyinst_sz (Ptr ty) = 1 + tyinst_sz ty) /\
  (tyinst_sz (MPtr id ty) = 1 + cppidinst_sz id + tyinst_sz ty) /\
  (tyinst_sz (Ref ty) = 1 + tyinst_sz ty) /\
  (tyinst_sz (Array ty n) = 1 + tyinst_sz ty) /\
  (tyinst_sz (Function ty tyl) = 1 + tyinst_sz ty + tylinst_sz tyl) /\
  (tyinst_sz (Const ty) = 1 + tyinst_sz ty) /\
  (tyinst_sz (TypeID id) = 1 + cppidinst_sz id) /\
  (tyinst_sz Void = 2) /\
  (tyinst_sz BChar = 2) /\
  (tyinst_sz Bool = 2) /\
  (tyinst_sz (Unsigned _) = 2) /\
  (tyinst_sz (Signed _) = 2) /\
  (tyinst_sz Float = 2) /\
  (tyinst_sz Double = 2) /\
  (tyinst_sz LDouble = 2)

     /\

  (cppidinst_sz (IDVar s) = 0) /\
  (cppidinst_sz (IDFld id sfld) = cppidinst_sz id + sfldinst_sz sfld + 1) /\
  (cppidinst_sz (IDTempCall tid tal) =
     tidinst_sz tid + talinst_sz tal + 1) /\
  (cppidinst_sz (IDConstant tn) = 1)

     /\

  (sfldinst_sz (SFTempCall s tal) = 1 + talinst_sz tal) /\
  (sfldinst_sz (SFName s) = 1)

     /\

  (tainst_sz (TType ty) = 1 + tyinst_sz ty) /\
  (tainst_sz (TTemp tid) = 1 + tidinst_sz tid) /\
  (tainst_sz (TVal tva) = 1 + tvainst_sz tva)

     /\

  (tvainst_sz (TNum i) = 1) /\
  (tvainst_sz (TObj id) = 1 + cppidinst_sz id) /\
  (tvainst_sz (TMPtr id ty) = 1 + cppidinst_sz id + tyinst_sz ty) /\
  (tvainst_sz (TVAVar s) = 0)

     /\

  (talinst_sz [] = 0) /\
  (talinst_sz (ta::tal) = 1 + tainst_sz ta + talinst_sz tal)

     /\

  (tylinst_sz [] = 0) /\
  (tylinst_sz (ty::tyl) = 1 + tyinst_sz ty + tylinst_sz tyl)
`
val _ = export_rewrites ["tyinst_sz_def"]

val typeid_size = store_thm(
  "typeid_size",
  ``(typeid ty = SOME id) ==> (tyinst_sz ty = 1 + cppidinst_sz id)``,
  Cases_on `ty` THEN SRW_TAC [][]);

val zero_lt_tysize = store_thm(
  "zero_lt_tysize",
  ``0 < tyinst_sz ty``,
  Cases_on `ty` THEN SRW_TAC [ARITH_ss][]);

val cppidinst_sz_EQ_0 = store_thm(
  "cppidinst_sz_EQ_0",
  ``(cppidinst_sz id = 0) = ?nm. id = IDVar nm``,
  Cases_on `id` THEN SRW_TAC [][]);
val _ = export_rewrites ["cppidinst_sz_EQ_0"]

val tyinst_sz_EQ_1 = store_thm(
  "tyinst_sz_EQ_1",
  ``(tyinst_sz ty = 1) = ?nm. ty = TypeID (IDVar nm)``,
  Cases_on `ty` THEN SRW_TAC [][] THEN
  MP_TAC (Q.INST [`ty` |-> `C''`] zero_lt_tysize) THEN
  TRY DECIDE_TAC THEN
  MP_TAC (Q.INST [`ty` |-> `C0`] zero_lt_tysize) THEN DECIDE_TAC);
val _ = export_rewrites ["tyinst_sz_EQ_1"]

val tvainst_sz_EQ_0 = store_thm(
  "tvainst_sz_EQ_0",
  ``!tva. (tvainst_sz tva = 0) = ?nm. tva = TVAVar nm``,
  Cases THEN SRW_TAC [][]);
val _ = export_rewrites ["tvainst_sz_EQ_0"]

val type_match_size_increase = store_thm(
  "type_match_size_increase",
  ``(!id1 s ty2. (cppid_inst s id1 = SOME ty2) ==>
                 cppidinst_sz id1 < tyinst_sz ty2) /\
    (!sfld1 s sfld2. (sfld_inst s sfld1 = SOME sfld2) ==>
                     sfldinst_sz sfld1 <= sfldinst_sz sfld2) /\
    (!ta1 s ta2. (temparg_inst s ta1 = SOME ta2) ==>
                 tainst_sz ta1 <= tainst_sz ta2) /\
    (!tva1 s tva2. (temp_valarg_inst s tva1 = SOME tva2) ==>
                   tvainst_sz tva1 <= tvainst_sz tva2) /\
    (!ty1 s ty2. (type_inst s ty1 = SOME ty2) ==>
                 tyinst_sz ty1 <= tyinst_sz ty2) /\
    (!tal1 s tal2. (olmap (temparg_inst s) tal1 = SOME tal2) ==>
                   talinst_sz tal1 <= talinst_sz tal2) /\
    (!tyl1 s tyl2. (olmap (type_inst s) tyl1 = SOME tyl2) ==>
                   (tylinst_sz tyl1 <= tylinst_sz tyl2))``,
  Induct THEN SRW_TAC [][] THEN SRW_TAC [][] THEN
  FTRY (RES_TAC THEN DECIDE_TAC) THEN
  FTRY (IMP_RES_TAC typeid_size THEN RES_TAC THEN DECIDE_TAC) THENL [
    MATCH_ACCEPT_TAC (GEN_ALL zero_lt_tysize),

    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THEN RES_TAC THEN
    MP_TAC (Q.INST [`tid` |-> `T'`] tempid_inst_size) THEN
    DECIDE_TAC,

    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THEN RES_TAC THEN DECIDE_TAC,

    SRW_TAC [][tempid_inst_size],

    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THEN RES_TAC THEN DECIDE_TAC
  ]);

val _ = Hol_datatype`frees_record = <| tyfvs : string set ;
                                       tempfvs : string set ;
                                       valfvs : string set |>`
val empty_freerec_def = Define`
  empty_freerec = <| tyfvs := {}; tempfvs := {}; valfvs := {} |>
`;

val _ = overload_on ("EMPTY", ``empty_freerec``)

val freerec_UNION_def = Define`
  freerec_UNION fr1 fr2 = <| tyfvs := fr1.tyfvs UNION fr2.tyfvs ;
                             tempfvs := fr1.tempfvs UNION fr2.tempfvs;
                             valfvs := fr1.valfvs UNION fr2.valfvs |>
`;
val _ = overload_on ("UNION", ``freerec_UNION``)

val tyfree_sing_def = Define`
  tyfree_sing s = <| tyfvs := {s}; tempfvs := {}; valfvs := {} |>
`;
val tempfree_sing_def = Define`
  tempfree_sing s = <| tyfvs := {}; tempfvs := {s}; valfvs := {} |>
`
val valfree_sing_def = Define`
  valfree_sing s = <| tyfvs := {}; tempfvs := {}; valfvs := {s} |>
`

val renaming_upto_def = Define`
  renaming_upto frees s = (!v. v IN frees.tyfvs ==>
                               ?nm. s.typemap v = TypeID (IDVar nm)) /\
                          (!v. v IN frees.tempfvs ==>
                               ?nm. s.tempmap v = TemplateVar nm) /\
                          (!v. v IN frees.valfvs ==>
                               ?nm. s.valmap v = TVAVar nm)
`;

val renaming_upto_empty = store_thm(
  "renaming_upto_empty",
  ``renaming_upto {} s``,
  SRW_TAC [][renaming_upto_def, empty_freerec_def]);
val _ = export_rewrites ["renaming_upto_empty"]

val renaming_upto_UNION = store_thm(
  "renaming_upto_UNION",
  ``renaming_upto (s1 UNION s2) s = renaming_upto s1 s /\ renaming_upto s2 s``,
  SRW_TAC [DNF_ss][freerec_UNION_def, renaming_upto_def] THEN
  METIS_TAC []);
val _ = export_rewrites ["renaming_upto_UNION"]

val tidfrees_def = Define`
  (tidfrees (TemplateConstant tn) = {}) /\
  (tidfrees (TemplateVar s) = tempfree_sing s)
`;
val _ = export_rewrites ["tidfrees_def"]


val tyfrees_def = Define`
  (tyfrees (Class cid) = {}) /\
  (tyfrees (Ptr ty) = tyfrees ty) /\
  (tyfrees (MPtr id ty) = cppidfrees id UNION tyfrees ty) /\
  (tyfrees (Ref ty) = tyfrees ty) /\
  (tyfrees (Array ty n) = tyfrees ty) /\
  (tyfrees (Function ty tyl) = tyfrees ty UNION tylfrees tyl) /\
  (tyfrees (Const ty) = tyfrees ty) /\
  (tyfrees (TypeID id) = cppidfrees id) /\
  (tyfrees Void = {}) /\
  (tyfrees BChar = {}) /\
  (tyfrees Bool = {}) /\
  (tyfrees (Unsigned _) = {}) /\
  (tyfrees (Signed _) = {}) /\
  (tyfrees Float = {}) /\
  (tyfrees Double = {}) /\
  (tyfrees LDouble = {})

     /\

  (cppidfrees (IDVar s) = tyfree_sing s) /\
  (cppidfrees (IDFld id sfld) = cppidfrees id UNION sfldfrees sfld) /\
  (cppidfrees (IDTempCall tid tal) = tidfrees tid UNION talfrees tal) /\
  (cppidfrees (IDConstant tn) = {})

     /\

  (sfldfrees (SFTempCall s tal) = talfrees tal) /\
  (sfldfrees (SFName s) = {})

     /\

  (tafrees (TType ty) = tyfrees ty) /\
  (tafrees (TTemp tid) = tidfrees tid) /\
  (tafrees (TVal tva) = tvalfrees tva)

     /\

  (tvalfrees (TNum i) = {}) /\
  (tvalfrees (TObj id) = cppidfrees id) /\
  (tvalfrees (TMPtr id ty) = cppidfrees id UNION tyfrees ty) /\
  (tvalfrees (TVAVar s) = valfree_sing s)

     /\

  (talfrees [] = {}) /\
  (talfrees (ta::tal) = tafrees ta UNION talfrees tal)

     /\

  (tylfrees [] = {}) /\
  (tylfrees (ty::tyl) = tyfrees ty UNION tylfrees tyl)
`
val _ = export_rewrites ["tyfrees_def"]

val inst_size_tidrenaming = store_thm(
  "inst_size_tidrenaming",
  ``(tidinst_sz (tempid_inst s tid) = tidinst_sz tid) ==>
    renaming_upto (tidfrees tid) s``,
  Cases_on `tid` THEN SRW_TAC [][tempfree_sing_def] THEN
  Cases_on `s.tempmap s'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][renaming_upto_def]);

val type_match_size_eq_renaming = store_thm(
  "type_match_size_eq_renaming",
  ``(!id1 s ty2. (cppid_inst s id1 = SOME ty2) /\
                 (tyinst_sz ty2 = 1 + cppidinst_sz id1) ==>
                 renaming_upto (cppidfrees id1) s) /\
    (!sfld1 s sfld2. (sfld_inst s sfld1 = SOME sfld2) /\
                     (sfldinst_sz sfld2 = sfldinst_sz sfld1) ==>
                     renaming_upto (sfldfrees sfld1) s) /\
    (!ta1 s ta2. (temparg_inst s ta1 = SOME ta2) /\
                 (tainst_sz ta2 = tainst_sz ta1) ==>
                 renaming_upto (tafrees ta1) s) /\
    (!tva1 s tva2. (temp_valarg_inst s tva1 = SOME tva2) /\
                   (tvainst_sz tva2 = tvainst_sz tva1) ==>
                   renaming_upto (tvalfrees tva1) s) /\
    (!ty1 s ty2. (type_inst s ty1 = SOME ty2) /\
                 (tyinst_sz ty2 = tyinst_sz ty1) ==>
                 renaming_upto (tyfrees ty1) s) /\
    (!tal1 s tal2. (olmap (temparg_inst s) tal1 = SOME tal2) /\
                   (talinst_sz tal2 = talinst_sz tal1) ==>
                   renaming_upto (talfrees tal1) s) /\
    (!tyl1 s tyl2. (olmap (type_inst s) tyl1 = SOME tyl2) /\
                   (tylinst_sz tyl2 = tylinst_sz tyl1) ==>
                   renaming_upto (tylfrees tyl1) s)``,
  Induct THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THENL [
    SRW_TAC [][renaming_upto_def, tyfree_sing_def],

    `sfldinst_sz sfld1 <= sfldinst_sz y0 /\
     cppidinst_sz id1 < tyinst_sz ty`
       by METIS_TAC [type_match_size_increase] THEN
    IMP_RES_TAC typeid_size THEN
    `tyinst_sz ty = 1 + cppidinst_sz id1` by DECIDE_TAC THEN
    METIS_TAC [],

    `sfldinst_sz sfld1 <= sfldinst_sz y0 /\
     cppidinst_sz id1 < tyinst_sz ty`
       by METIS_TAC [type_match_size_increase] THEN
    IMP_RES_TAC typeid_size THEN
    `sfldinst_sz y0 = sfldinst_sz sfld1` by DECIDE_TAC THEN
    METIS_TAC [],

    `tidinst_sz T' <= tidinst_sz (tempid_inst s T') /\
     talinst_sz tal1 <= talinst_sz z`
       by METIS_TAC [tempid_inst_size, type_match_size_increase] THEN
    `tidinst_sz (tempid_inst s T') = tidinst_sz T'` by DECIDE_TAC THEN
    METIS_TAC [inst_size_tidrenaming],

    `tidinst_sz T' <= tidinst_sz (tempid_inst s T') /\
     talinst_sz tal1 <= talinst_sz z`
       by METIS_TAC [tempid_inst_size, type_match_size_increase] THEN
    `talinst_sz z = talinst_sz tal1` by DECIDE_TAC THEN
    METIS_TAC [],

    METIS_TAC [inst_size_tidrenaming],

    METIS_TAC [typeid_size],

    `tyinst_sz ty1 <= tyinst_sz y0 /\ cppidinst_sz id1 < tyinst_sz ty`
       by METIS_TAC [type_match_size_increase] THEN
    IMP_RES_TAC typeid_size THEN
    `tyinst_sz ty = 1 + cppidinst_sz id1` by DECIDE_TAC THEN
    METIS_TAC [],

    `cppidinst_sz id1 < tyinst_sz ty /\ tyinst_sz ty1 <= tyinst_sz y0`
       by METIS_TAC [type_match_size_increase] THEN
    IMP_RES_TAC typeid_size THEN
    `tyinst_sz y0 = tyinst_sz ty1` by DECIDE_TAC THEN
    METIS_TAC [],

    SRW_TAC [][renaming_upto_def, valfree_sing_def],

    `cppidinst_sz id1 < tyinst_sz ty /\ tyinst_sz ty1 <= tyinst_sz y0`
       by METIS_TAC [type_match_size_increase] THEN
    IMP_RES_TAC typeid_size THEN
    `tyinst_sz ty = 1 + cppidinst_sz id1` by DECIDE_TAC THEN
    METIS_TAC [],

    `cppidinst_sz id1 < tyinst_sz ty /\ tyinst_sz ty1 <= tyinst_sz y0`
       by METIS_TAC [type_match_size_increase] THEN
    IMP_RES_TAC typeid_size THEN
    `tyinst_sz y0 = tyinst_sz ty1` by DECIDE_TAC THEN METIS_TAC [],

    IMP_RES_TAC type_match_size_increase THEN
    `tyinst_sz x0 = tyinst_sz ty1` by DECIDE_TAC THEN METIS_TAC [],

    IMP_RES_TAC type_match_size_increase THEN
    `tylinst_sz y0 = tylinst_sz tyl1` by DECIDE_TAC THEN METIS_TAC [],

    IMP_RES_TAC type_match_size_increase THEN
    `tainst_sz h = tainst_sz ta1` by DECIDE_TAC THEN METIS_TAC [],

    IMP_RES_TAC type_match_size_increase THEN
    `talinst_sz z = talinst_sz tal1` by DECIDE_TAC THEN METIS_TAC [],

    IMP_RES_TAC type_match_size_increase THEN
    `tyinst_sz h = tyinst_sz ty1` by DECIDE_TAC THEN METIS_TAC [],

    IMP_RES_TAC type_match_size_increase THEN
    `tylinst_sz z = tylinst_sz tyl1` by DECIDE_TAC THEN METIS_TAC []
  ]);

val type_match_antisym = store_thm(
  "type_match_antisym",
  ``ty1 <= ty2 /\ ty2 <= ty1 ==>
       ?s. (type_inst s ty1 = SOME ty2) /\
           renaming_upto (tyfrees ty1) s``,
  SRW_TAC [][type_match_def] THEN
  `tyinst_sz ty1 <= tyinst_sz ty2 /\ tyinst_sz ty2 <= tyinst_sz ty1`
     by METIS_TAC [type_match_size_increase] THEN
  `tyinst_sz ty1 = tyinst_sz ty2` by DECIDE_TAC THEN
  METIS_TAC [type_match_size_eq_renaming]);

val cppID_inst_def = Define`
  cppID_inst s id =
    case cppid_inst s id of NONE -> NONE || SOME ty -> typeid ty
`;

(* instantiate an expression *)
val expr_inst_def = Define`
  (expr_inst sigma (Cnum n) = SOME (Cnum n)) /\
  (expr_inst sigma (Cchar n) = SOME (Cchar n)) /\
  (expr_inst sigma (Cnullptr ty) = OPTION_MAP Cnullptr (type_inst sigma ty)) /\
  (expr_inst sigma This = SOME This) /\
  (expr_inst sigma (Var id) =
     case id of
        IDConstant (F,[],s) ->
           (case sigma.valmap s of
              TNum i -> SOME (Cnum i)
           || TObj id' -> SOME (Var id')
           || TMPtr cid ty ->
                        (case cid of
                            IDFld cnm fldname -> SOME (MemAddr cnm fldname))
           || TVAVar s' -> SOME (Var (IDConstant (F, [], s'))))
     || x -> SOME (Var id)) /\
  (expr_inst sigma (COr e1 e2) =
     OP2CMB COr (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (CAnd e1 e2) =
     OP2CMB CAnd (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (CCond e1 e2 e3) =
     case expr_inst sigma e1 of
        NONE -> NONE
     || SOME e1' -> OP2CMB (CCond e1')
                           (expr_inst sigma e2)
                           (expr_inst sigma e3)) /\
  (expr_inst sigma (CApBinary cbop e1 e2) =
     OP2CMB (CApBinary cbop) (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (CApUnary cuop e) =
     OPTION_MAP (CApUnary cuop) (expr_inst sigma e)) /\
  (expr_inst sigma (Addr e) = OPTION_MAP Addr (expr_inst sigma e)) /\
  (expr_inst sigma (Deref e) = OPTION_MAP Deref (expr_inst sigma e)) /\
  (expr_inst sigma (MemAddr cid fld) =
     OP2CMB MemAddr (cppID_inst sigma cid) (sfld_inst sigma fld)) /\
  (expr_inst sigma (Assign bopopt e1 e2) =
     OP2CMB (Assign bopopt) (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (SVar e fld) =
     OP2CMB SVar (expr_inst sigma e) (sfld_inst sigma fld)) /\
  (expr_inst sigma (FnApp e args) =
     OP2CMB FnApp (expr_inst sigma e) (exprl_inst sigma args)) /\
  (expr_inst sigma (CommaSep e1 e2) =
     OP2CMB CommaSep (expr_inst sigma e1) (expr_inst sigma e2)) /\
  (expr_inst sigma (Cast ty e) =
     OP2CMB Cast (type_inst sigma ty) (expr_inst sigma e)) /\
  (expr_inst sigma (PostInc e) = OPTION_MAP PostInc (expr_inst sigma e)) /\
  (expr_inst sigma (New ty args_opt) =
     OP2CMB New (type_inst sigma ty) (exprlop_inst sigma args_opt)) /\
  (expr_inst sigma (FnApp_sqpt e args) =
     OP2CMB FnApp_sqpt (expr_inst sigma e) (exprl_inst sigma args)) /\
  (expr_inst sigma (LVal ad ty nms) =
     OP2CMB (LVal ad) (type_inst sigma ty) (olmap (cppID_inst sigma) nms)) /\
  (expr_inst sigma (FVal fnid ty eopt) =
     OP2CMB (FVal fnid) (type_inst sigma ty) (expropt_inst sigma eopt)) /\
  (expr_inst sigma (ConstructorFVal b1 b2 ad nm) =
     OPTION_MAP (ConstructorFVal b1 b2 ad) (cppID_inst sigma nm)) /\
  (expr_inst sigma (ConstructedVal b ad nm) =
     OPTION_MAP (ConstructedVal b ad) (cppID_inst sigma nm)) /\
  (expr_inst sigma (DestructorCall ad nm) =
     OPTION_MAP (DestructorCall ad) (cppID_inst sigma nm)) /\
  (expr_inst sigma (RValreq e) = OPTION_MAP RValreq (expr_inst sigma e)) /\
  (expr_inst sigma (ECompVal bytes ty) =
     OPTION_MAP (ECompVal bytes) (type_inst sigma ty)) /\
  (expr_inst sigma (ExceptionExpr e) =
     OPTION_MAP ExceptionExpr (expr_inst sigma e)) /\

  (exprl_inst sigma [] = SOME []) /\
  (exprl_inst sigma (e::es) =
     OP2CMB CONS (expr_inst sigma e) (exprl_inst sigma es)) /\

  (exprlop_inst sigma NONE = SOME NONE) /\
  (exprlop_inst sigma (SOME elist) =
     case exprl_inst sigma elist of
        NONE -> NONE
     || SOME elist' -> SOME (SOME elist')) /\

  (expropt_inst sigma NONE = SOME NONE) /\
  (expropt_inst sigma (SOME e) =
     case expr_inst sigma e of
        NONE -> NONE
     || SOME e' -> SOME (SOME e'))
`

(* this shouldn't ever actually be called, because instantiation shouldn't
   ever see programs with dynamic helper syntax (such as this) in place *)
val varlocn_inst_def = Define`
  (varlocn_inst sigma (RefPlace nopt nm) =
     OPTION_MAP (RefPlace nopt) (cppID_inst sigma nm)) /\
  (varlocn_inst sigma (ObjPlace n) = SOME (ObjPlace n))
`;

(* fields that are initialised can't be member functions, so there is no
   chance the MI_fld could be a template call *)
val meminitid_inst_def = Define`
  (meminitid_inst sigma (MI_C id) = OPTION_MAP MI_C (cppID_inst sigma id)) /\
  (meminitid_inst sigma (MI_fld nm) = SOME (MI_fld nm))
`;

val stmt_inst_defn = Hol_defn "stmt_inst" `
  (stmt_inst sigma EmptyStmt = SOME EmptyStmt) /\
  (stmt_inst sigma (CLoop ee st) =
     OP2CMB CLoop (eexpr_inst sigma ee) (stmt_inst sigma st)) /\
  (stmt_inst sigma (CIf ee st1 st2) =
     case eexpr_inst sigma ee of
        NONE -> NONE
     || SOME ee' ->
          OP2CMB (CIf ee') (stmt_inst sigma st1) (stmt_inst sigma st2)) /\
  (stmt_inst sigma (Standalone ee) =
     OPTION_MAP Standalone (eexpr_inst sigma ee)) /\
  (stmt_inst sigma (Block b vdl stl) =
     OP2CMB (Block b)
            (olmap (vdec_inst sigma) vdl)
            (olmap (stmt_inst sigma) stl)) /\
  (stmt_inst sigma (Ret ee) = OPTION_MAP Ret (eexpr_inst sigma ee)) /\
  (stmt_inst sigma EmptyRet = SOME EmptyRet) /\
  (stmt_inst sigma Break = SOME Break) /\
  (stmt_inst sigma Cont = SOME Cont) /\
  (stmt_inst sigma (Trap tt st) = OPTION_MAP (Trap tt) (stmt_inst sigma st)) /\
  (stmt_inst sigma (Throw eeopt) =
     case eeopt of
        NONE -> SOME (Throw NONE)
     || SOME ee -> (case eexpr_inst sigma ee of
                       NONE -> NONE
                    || SOME ee' -> SOME (Throw (SOME ee')))) /\
  (stmt_inst sigma (Catch st handlers) =
     OP2CMB Catch
            (stmt_inst sigma st)
            (olmap (\ (exnpd, st).
                      (OP2CMB (,)
                              (case exnpd of
                                  NONE -> SOME NONE
                               || SOME (sopt,ty) ->
                                   (case type_inst sigma ty of
                                       NONE -> NONE
                                    || SOME ty' -> SOME (SOME (sopt, ty'))))
                              (stmt_inst sigma st)))
                   handlers)) /\
  (stmt_inst sigma ClearExn = SOME ClearExn)

     /\

  (eexpr_inst sigma (NormE e se) =
     OPTION_MAP (\e. NormE e se) (expr_inst sigma e)) /\
  (eexpr_inst sigma (EStmt st c) =
     OPTION_MAP (\s. EStmt s c) (stmt_inst sigma st))

     /\

  (vdec_inst sigma (VDec ty nm) =
     OP2CMB VDec (type_inst sigma ty) (cppID_inst sigma nm)) /\
  (vdec_inst sigma (VDecInit ty nm init) =
     case type_inst sigma ty of
        NONE -> NONE
     || SOME ty' -> OP2CMB (VDecInit ty')
                           (cppID_inst sigma nm)
                           (initialiser_inst sigma init)) /\
  (vdec_inst sigma (VDecInitA ty vlocn init) =
     case type_inst sigma ty of
        NONE -> NONE
     || SOME ty' -> OP2CMB (VDecInitA ty')
                           (varlocn_inst sigma vlocn)
                           (initialiser_inst sigma init)) /\
  (vdec_inst sigma (VStrDec id infoopt) =
     case infoopt of
        NONE -> OPTION_MAP (\i. VStrDec i NONE) (cppID_inst sigma id)
     || SOME info ->
          (case cinfo_inst sigma info of
              NONE -> NONE
           || SOME info' -> OPTION_MAP (\i. VStrDec i (SOME info'))
                                       (cppID_inst sigma id))) /\
  (vdec_inst sigma (VException e) = OPTION_MAP VException (expr_inst sigma e))

     /\

  (centry_inst sigma (CFnDefn ty fld params body) =
     case type_inst sigma ty of
        NONE -> NONE
     || SOME ty' ->
          (case sfld_inst sigma fld of
              NONE -> NONE
           || SOME sfld' -> OP2CMB (CFnDefn ty' sfld')
                                   (olmap (\ (n,ty).
                                             OPTION_MAP ((,) n)
                                                        (type_inst sigma ty))
                                          params)
                                   (OPTION_MAP (stmt_inst sigma) body))) /\
  (centry_inst sigma (FldDecl fldnm ty) =
     OPTION_MAP (FldDecl fldnm) (type_inst sigma ty)) /\
  (centry_inst sigma (Constructor params meminits bodyopt) =
     case olmap (\ (n,ty). OPTION_MAP ((,)n) (type_inst sigma ty)) params of
        NONE -> NONE
     || SOME params' ->
          OP2CMB (Constructor params')
                 (olmap (\ (mid,optargs).
                           OP2CMB (,)
                                  (meminitid_inst sigma mid)
                                  (OPTION_MAP (olmap (expr_inst sigma))
                                              optargs))
                        meminits)
                 (OPTION_MAP (stmt_inst sigma) bodyopt)) /\
  (centry_inst sigma (Destructor bodyopt) =
     OPTION_MAP Destructor (OPTION_MAP (stmt_inst sigma) bodyopt))

     /\

  (cinfo_inst sigma ci =
     case
       olmap (\ (ce,b,p). OPTION_MAP (\ce. (ce,b,p)) (centry_inst sigma ce))
             ci.fields
     of
        NONE -> NONE
     || SOME fields' ->
          case olmap (\ (cs,b,p). OPTION_MAP (\i. (i,b,p))
                                             (cppID_inst sigma cs))
                     ci.ancestors
          of
             NONE -> NONE
          || SOME ancestors' -> SOME <| fields := fields';
                                        ancestors := ancestors' |>)

     /\

  (initialiser_inst sigma (DirectInit0 elist) =
     OPTION_MAP DirectInit0 (olmap (expr_inst sigma) elist)) /\
  (initialiser_inst sigma (DirectInit ee) =
     OPTION_MAP DirectInit (eexpr_inst sigma ee)) /\
  (initialiser_inst sigma (CopyInit ee) =
     OPTION_MAP CopyInit (eexpr_inst sigma ee))
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
    Cases_on `ci` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Induct_on `l` THEN SRW_TAC [][] THEN SRW_TAC [ARITH_ss][] THEN
    RES_TAC THEN DECIDE_TAC,
    Induct_on `vdl` THEN SRW_TAC [][] THEN SRW_TAC [ARITH_ss][] THEN
    RES_TAC THEN DECIDE_TAC,
    Induct_on `stl` THEN SRW_TAC [][] THEN SRW_TAC [ARITH_ss][] THEN
    RES_TAC THEN DECIDE_TAC
  ]);

val extdecl_inst_def = Define`
  (extdecl_inst sub (FnDefn retty fnm params body) = 
     case OP2CMB FnDefn (type_inst sub retty) (cppID_inst sub fnm) of 
        NONE -> NONE
     || SOME c -> OP2CMB c (olmap (\ (s,ty). 
                                     OPTION_MAP ((,)s) (type_inst sub ty))
                                  params)
                           (stmt_inst sub body)) /\
  (extdecl_inst sub (Decl d) = OPTION_MAP Decl (vdec_inst sub d)) /\
  (extdecl_inst sub (ClassConDef cnm params meminits body) = 
     case OP2CMB ClassConDef (cppID_inst sub cnm) 
                             (olmap (\ (s,ty).
                                       OPTION_MAP ((,)s) (type_inst sub ty))
                                    params)
     of
        NONE -> NONE
     || SOME c' -> OP2CMB c' 
                          (olmap (\ (mid,elistopt). 
                                       OP2CMB (,) (meminitid_inst sub mid)
                                                  (OPTION_MAP 
                                                   (olmap (expr_inst sub))
                                                   elistopt))
                                 meminits) 
                          (stmt_inst sub body)) /\
  (extdecl_inst sub (ClassDestDef cnm body) = 
     OP2CMB ClassDestDef (cppID_inst sub cnm) (stmt_inst sub body))
`

val _ = export_theory()

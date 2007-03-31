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

  (cidttypes (IDVar s) = {}) /\
  (cidttypes (IDFld cid sfld) = cidttypes cid UNION sfld_ttypes sfld) /\
  (cidttypes (IDTempCall tid targs) = {(tid,targs)} UNION talttypes targs) /\
  (cidttypes (IDConstant _) = {}) /\

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
  (tvattypes (TVAVar s) = {})
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
  (expr_ttypes (SVar e sfld) = expr_ttypes e UNION sfld_ttypes sfld) /\
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
  (expr_ttypes (ExceptionExpr _) = {}) /\
  (expr_ttypes UndefinedExpr = {}) /\

  (exprl_ttypes [] = {}) /\
  (exprl_ttypes (e::elist) = expr_ttypes e UNION exprl_ttypes elist) /\

  (exprlopt_ttypes NONE = {}) /\
  (exprlopt_ttypes (SOME elist) = exprl_ttypes elist)
`;

val mem_init_id_ttypes_def = Define`
  (mem_init_id_ttypes (MI_C cnm) = cidttypes cnm) /\
  (mem_init_id_ttypes (MI_fld s) = {})
`;

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

  (vd_ttypes (VDec ty nm) =
     if cppidfrees nm = {} then
       ttypes ty UNION cidttypes nm
     else {}) /\
  (vd_ttypes (VDecInit ty nm init) =
     if cppidfrees nm = {} then
       ttypes ty UNION cidttypes nm UNION init_ttypes init
     else {}) /\
  (vd_ttypes (VDecInitA ty vl init) = {}) /\ (* dynamic value only *)
  (vd_ttypes (VStrDec cspec cinfo_opt) =
     if cppidfrees cspec = {} then
       cidttypes cspec UNION
       (case cinfo_opt of
           NONE -> {}
        || SOME cinfo -> cinfo_ttypes cinfo)
     else {}) /\
  (vd_ttypes (VException _) = {})  /\ (* dynamic value only *)

  (centry_ttypes (CFnDefn retty sfld params bodyopt) =
     if sfldfrees sfld = {} then
       ttypes retty UNION sfld_ttypes sfld UNION
       FOLDL (\a (nm,ty). a UNION ttypes ty) {} params UNION
       (case bodyopt of NONE -> {} || SOME st -> stmt_ttypes st)
     else {}) /\
  (centry_ttypes (FldDecl string ty) = ttypes ty) /\
  (centry_ttypes (Constructor params meminits bodyopt) =
     FOLDL (\a (nm,ty). a UNION ttypes ty) {} params UNION
     (case bodyopt of NONE -> {} || SOME st -> stmt_ttypes st) UNION
     FOLDL (\a (memid, argsopt).
              a UNION mem_init_id_ttypes memid UNION
              exprlopt_ttypes argsopt)
           {} meminits) /\
  (centry_ttypes (Destructor bodyopt) =
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

val extdecl_ttypes_def = Define`
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
       centry_ttypes (Destructor (SOME body))
     else {})
`;


(* ----------------------------------------------------------------------
    process definitions
      inspired by Program Instantiation (Fig. 6) of Siek and Taha
   ---------------------------------------------------------------------- *)

(* Siek and Taha have two sorts of external declaration, template
   definitions of classes (which are patterns wrapped around a field
   declaration), and member function definitions.

   We have rather more complexity than this.  We have normal
   functions, multiple members per class, and data field.  In
   addition, we can have template member functions, template
   functions, and template template parameters

   This means that we need to do things slightly differently.

*)

val _ = Hol_datatype `inststate = Running of 'a | Done of 'b | Failed`
val _ = Hol_datatype `instneed_type = NeedFn | NeedVr`


val _ = Hol_datatype `
  FunctionRef = CallConstructor of CPP_ID => CPP_Type list
              | CallDestructor of CPP_ID
              | FnCall of CPP_ID
`

val sfld_basename_def = Define`
  (sfld_basename (SFName s) = s) /\
  (sfld_basename (SFTempCall s args) = s)
`;

val id_basename_def = Define`
  (id_basename (IDVar s) = NONE) /\
  (id_basename (IDFld cid sfld) = NONE) /\
  (id_basename (IDTempCall (TemplateConstant tn) targs) = SOME tn) /\
  (id_basename (IDTempCall (TemplateVar s) targs) = NONE) /\
  (id_basename (IDConstant tn) = SOME tn)
`;

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
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss)
                 [DB.fetch "expressions" "CExpr_size_def"] THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `elist` THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss)
                 [DB.fetch "expressions" "CExpr_size_def"] THEN
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



(* first thing to do on seeing a function definition (could be member function
   or not), is to check if it's at a ground type, or a template definition.
   If the latter, just put it into the Templates field.  Otherwise,
   scan it for ground template types, and put these onto the list of things
   that need doing.  *)
val fndefn0_def = Define`
  fndefn0 Templates Residuals Needs edecs (FnDefn ty nm params body) =
    let edec = FnDefn ty nm params body
    in
      if cppidfrees nm = {} then
        if MEM (FnDefn ty nm params body) Residuals then
          Running (Templates, Residuals, edecs)
        else
          let tys = extdecl_ttypes edec in
          let cmp id1 id2 = CPP_ID_size id1 <= CPP_ID_size id2 in
          let tyl = QSORT cmp
                      (SET_TO_LIST (IMAGE (\ (tid,targs). IDTempCall tid targs)
                                          tys))
          in
            Running(Templates,
                    Residuals,
                    Needs,
                    MAP (\id. (Decl (VStrDec id NONE), 0n)) tyl ++
                    [(edec,1)] ++ edecs)
      else (* might check that edec is not a partial specialisation
              occurring before the general pattern is given here *)
        Running (edec INSERT Templates, Residuals, Needs, edecs)
`;


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
      ctxt with classes updated_by (\fm. fm |+ (nm, ci))) /\
  (edec_ctxt ctxt (Decl (VException e)) = ctxt) (* dynamic value *)
`;





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
      ?body. MEM (ClassDestDef id body) residuals)
`;

val optimage_def = Define`
  optimage (f : 'a -> 'b option) (s : 'a set) =
     ({ b | ?a. a IN s /\ (SOME b = f a) },
      { a | f a = NONE })
`;

val optimage_image = store_thm(
  "optimage_image",
  ``optimage f s = (IMAGE THE (IMAGE f s DELETE NONE),
                    { a | f a = NONE })``,
  SRW_TAC [DNF_ss][optimage_def, EXTENSION, EQ_IMP_THM] THENL [
    Q.EXISTS_TAC `a` THEN POP_ASSUM (fn th => SRW_TAC [][SYM th]),
    Q.EXISTS_TAC `x''` THEN Cases_on `f x''` THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val best_class_match_def = Define`
  best_class_match Temps id sub (id', ci) =
    (cppID_inst sub id' = SOME id) /\
    Decl (VStrDec id' ci) IN Temps /\
    !id2 ci2 sub2.  Decl (VStrDec id2 ci2) IN Temps /\
                    (cppID_inst sub2 id2 = SOME id) ==>
                    ?sub'. cppID_inst sub' id2 = SOME id'
`;

val find_defn_def = Define`
  (find_defn Templates (FnCall id) =
      case id of
         IDFld cnm sfld ->

val categorise_new_fnrefs_def = Define`
  categorise_new_fnrefs Templates newfns

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
    let (NewNeeds, NewlyInstantiated) = categorise_new_fnrefs Templates newfns
    in
      Running(Templates, Residuals, NewNeeds ++ Needs,
              NewlyInstantiated ++ [(edec,2)] ++ edecs)
`;



val program_instantiate_def = Define`
  proginst (Templates, Residuals, Needs, extdecllist) =
    case extdecllist of
       [] -> Done (Residuals, Needs)
    || ((edec,m) :: edecs) ->
          (case edec of
             FnDefn ty nm params body ->
               if m = 0 then fndefn0 Templates Residuals Needs edecs edec
               else if m = 1 then fndefn1 Templates Residuals edecs edec
               else Running(Templates, edec :: Residuals, edecs))
`





val _ = export_theory();



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


val _ = Hol_datatype`
  inst_record = <| typemap : string -> CPP_Type ;
                   tempmap : string -> bool # StaticField list # string ;
                   valmap  : string -> TemplateValueArg 
|>`

val empty_inst_def = Define`
  empty_inst = <| typemap := (\s. TypeID (IDConstant(F,[],SFName s)));
                  tempmap := (\s. (F, [], s)); 
                  valmap := TVAVar |>
`;


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

val IDhd_def = Define`
  (IDhd (IDConstant(b, [], sf)) = sf) /\
  (IDhd (IDConstant(b, h::t, sf)) = h)
`;
val _ = export_rewrites ["IDhd_def"]

val ID_updhd_def = Define`
  (ID_updhd ty (IDConstant(b2, [], sf2)) = SOME ty) /\
  (ID_updhd ty (IDConstant(b2, h::t, sf2)) = 
     case typeid ty of 
        NONE -> NONE
     || SOME (IDConstant(b1,sfs1,sf1)) -> 
          SOME (TypeID (IDConstant(b1, sfs1 ++ [sf1] ++ t, sf2))) 
     || SOME (IDVar _) -> NONE)
`;
val _ = export_rewrites ["ID_updhd_def"]

val dest_sfname_def = Define`
  (dest_sfname (SFName s) = s) 
`;
val _ = export_rewrites ["dest_sfname_def"]

val ID_updtemphd_def = Define`
  (ID_updtemphd (b1,sfs1,sfn) targs (IDConstant(b2,[],sf2)) = 
     SOME (TypeID (IDConstant(b1, sfs1, SFTempCall sfn targs)))) /\
  (ID_updtemphd (b1,sfs1,sfn) targs (IDConstant(b2,h::t,sf2)) = 
     SOME (TypeID 
           (IDConstant(b1, 
                       sfs1 ++ [SFTempCall sfn targs] ++ t, sf2)))) /\
  (ID_updtemphd _ _ _ = NONE)
`;
val _ = export_rewrites ["ID_updtemphd_def"]

val IDtl_def = Define`
  IDtl (IDConstant(b, sfs, sf)) = sf
`;

val option_case_EQ_SOME = store_thm(
  "option_case_EQ_SOME",
  ``(option_case NONE f v = SOME v0) =
        ?v0'. (v = SOME v0') /\ (f v0' = SOME v0)``,
  Cases_on `v` THEN SRW_TAC [][]);
val _ = export_rewrites ["option_case_EQ_SOME"]

val olmap_ALL_MEM = store_thm(
  "olmap_ALL_MEM",
  ``!list x f. 
        (olmap f list = SOME x) = 
          (LENGTH x = LENGTH list) /\
          !i. i < LENGTH list ==>
              (f (EL i list) = SOME (EL i x))``,
  Induct_on `list` THEN SRW_TAC [][] THENL [
    SRW_TAC [][listTheory.LENGTH_NIL] THEN METIS_TAC [],
    Cases_on `x` THEN SRW_TAC [][] THEN 
    SRW_TAC [][EQ_IMP_THM] THENL [
      Cases_on `i` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [],
      FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][],
      FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` MP_TAC) THEN SRW_TAC [][]
    ]
  ]);

val IDhd_inst_def = Define`
  IDhd_inst sigma (b, sfs, sf) = 
     if b then SOME (TypeID (IDConstant(b, sfs, sf)))
     else 
       case IDhd (IDConstant(F, sfs, sf)) of 
          SFName s -> ID_updhd (sigma.typemap s) (IDConstant(F,sfs,sf))
       || SFTempCall s targs -> 
                      ID_updtemphd (sigma.tempmap s) targs 
                                   (IDConstant(F,sfs,sf))
`;

val IDcases = store_thm(
  "IDcases",
  ``!i. (?b sfs sf. i = IDConstant(b,sfs,sf)) \/ (?nm. i = IDVar nm)``,
  Cases THEN SRW_TAC [][] THEN 
  Cases_on `p` THEN Cases_on `r` THEN SRW_TAC [][]);
fun IDC_TAC q = Q.SPEC_THEN q FULL_STRUCT_CASES_TAC IDcases
fun FSRW_TAC l = FULL_SIMP_TAC (srw_ss()) l

val IDhd_inst_EQ_SOME = store_thm(
  "IDhd_inst_EQ_SOME",
  ``(IDhd_inst s (b,sfs,sf) = SOME ty) = 
       b /\ (ty = TypeID (IDConstant(T,sfs,sf))) \/
       ~b /\ (sfs = []) /\ 
         (?s'. (sf = SFName s') /\ (ty = s.typemap s')) \/
       ~b /\ (sfs = []) /\
         (?s' tas b2 sfs2 sfn2. 
             (sf = SFTempCall s' tas) /\ 
             (s.tempmap s' = (b2, sfs2, sfn2)) /\
             (ty = TypeID (IDConstant(b2,sfs2, SFTempCall sfn2 tas)))) \/
       ~b /\ 
         (?s' sfs1 sfs2 sf1 b'. 
             (sfs = SFName s' :: sfs2) /\
             (s.typemap s' = TypeID (IDConstant(b',sfs1,sf1))) /\
             (ty = TypeID (IDConstant(b',sfs1 ++ [sf1] ++ sfs2,sf)))) \/
       ~b /\ 
         (?s' tas b2 sfs1 sfs2 sfn2.
             (sfs = SFTempCall s' tas :: sfs2) /\
             (s.tempmap s' = (b2,sfs1,sfn2)) /\
             (ty = TypeID (IDConstant(b2,
                                      sfs1 ++ [SFTempCall sfn2 tas] ++ sfs2,
                                      sf))))``,
  SRW_TAC [][IDhd_inst_def] THEN1 METIS_TAC [] THEN 
  Cases_on `sfs` THENL [
    SRW_TAC [][] THEN Cases_on `sf` THEN SRW_TAC [][] THENL [
      Cases_on `s.tempmap s'` THEN Cases_on `r` THEN 
      SRW_TAC [][] THEN METIS_TAC [],
      METIS_TAC []
    ],
    SRW_TAC [][] THEN Cases_on `h` THEN SRW_TAC [][] THENL [
      Cases_on `s.tempmap s'` THEN Cases_on `r` THEN SRW_TAC [][] THEN 
      METIS_TAC [],
      Cases_on `s.typemap s'` THEN SRW_TAC [][] THEN 
      IDC_TAC `C''` THEN SRW_TAC [][] THEN METIS_TAC []
    ]
  ]);
      
(* the schema variable sigma is left out in order to get a nicer 
   termination proof and induction principle *)
val type_inst_defn = Hol_defn "type_inst" `
  (type_inst (TypeID cid) = cppid_inst cid) /\
  (type_inst (Ptr ty) = OPTION_MAP Ptr (type_inst ty)) /\
  (type_inst (MPtr nm ty) =
     OP2CMB MPtr
            (case cppid_inst nm of NONE -> NONE || SOME ty -> typeid ty)
            (type_inst ty)) /\
  (type_inst (Ref ty) = OPTION_MAP Ref (type_inst ty)) /\
  (type_inst (Array ty n) =
     OPTION_MAP (\ty. Array ty n) (type_inst ty)) /\
  (type_inst (Function ty tylist) =
     OP2CMB Function (type_inst ty) (olmap (type_inst) tylist)) /\
  (type_inst (Const ty) = OPTION_MAP Const (type_inst ty)) /\
  (type_inst (Class cid) = SOME (Class cid)) /\
  (type_inst ty = SOME ty)

    /\

  (* id instantiation returns a type.  The type may just be a TypeID,
     possibly representing no change, or a "real" type. *)
  (cppid_inst (IDVar s) = SOME (TypeID (IDVar s))) /\
  (cppid_inst (IDConstant(T,sfs,sf)) = 
      case (olmap sfld_inst sfs, sfld_inst sf) of 
         (NONE, NONE) -> NONE 
      || (NONE, SOME sf') -> NONE
      || (SOME sfs', NONE) -> NONE
      || (SOME sfs', SOME sf') -> SOME (TypeID (IDConstant(T,sfs',sf')))) /\
  (cppid_inst (IDConstant(F, sfs, sf)) = 
      case (olmap sfld_inst sfs, sfld_inst sf) of 
         (NONE, NONE) -> NONE
      || (NONE, SOME sf') -> NONE
      || (SOME sfs', NONE) -> NONE
      || (SOME sfs', SOME sf') -> IDhd_inst sigma (F,sfs',sf'))

    /\

  (temparg_inst (TType ty) = OPTION_MAP TType (type_inst ty)) /\
  (temparg_inst (TTemp tid) =
     case cppid_inst tid of
        NONE -> NONE
     || SOME ty -> OPTION_MAP TTemp (typeid ty)) /\
  (temparg_inst (TVal tva) =
      OPTION_MAP TVal (temp_valarg_inst tva))

    /\

  (temp_valarg_inst (TNum i) = SOME (TNum i)) /\
  (temp_valarg_inst (TObj id) =
      OPTION_MAP TObj (case cppid_inst id of
                          NONE -> NONE
                       || SOME ty -> typeid ty)) /\
  (temp_valarg_inst (TMPtr id ty) =
      OP2CMB TMPtr
             (case cppid_inst id of NONE-> NONE || SOME ty -> typeid ty)
             (type_inst ty)) /\
  (temp_valarg_inst (TVAVar s) = SOME (sigma.valmap s))

    /\

  (sfld_inst (SFTempCall s targs) =
      OPTION_MAP (SFTempCall s) (olmap (temparg_inst) targs)) /\
  (sfld_inst (SFName s) = SOME (SFName s))
`

val (type_inst_def, type_inst_ind) = Defn.tprove(type_inst_defn,
  WF_REL_TAC `^(last (TotalDefn.guessR type_inst_defn))` THEN 
  SRW_TAC [ARITH_ss][] THENL [
    Induct_on `tylist` THEN SRW_TAC [][] THEN
    SRW_TAC [ARITH_ss][] THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `sfs` THEN SRW_TAC [][] THEN
    SRW_TAC [ARITH_ss][] THEN RES_TAC THEN DECIDE_TAC,
    Induct_on `sfs` THEN SRW_TAC [][] THEN
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

val olmap_EQ_NONE = prove(
  ``(olmap f list = NONE) = ?e. MEM e list /\ (f e = NONE)``,
  Induct_on `list` THEN SRW_TAC [][] THEN Cases_on `f h` THEN
  SRW_TAC [][] THEN METIS_TAC [TypeBase.distinct_of ``:'a option``]);

val olmap_EQ_SOME = prove(
  ``((olmap f list = SOME []) = (list = [])) /\
    ((SOME [] = olmap f list) = (list = [])) /\
    ((olmap f list = SOME (h::t)) = 
        ?h0 t0. (f h0 = SOME h) /\ (list = h0::t0) /\ (olmap f t0 = SOME t))``,
  Cases_on `list` THEN SRW_TAC [][]);

val IDhd_inst_empty = store_thm(
  "IDhd_inst_empty",
  ``IDhd_inst empty_inst (b, sfs, sfld) = 
      SOME (TypeID (IDConstant(b, sfs, sfld)))``,
  SRW_TAC [][IDhd_inst_def] THEN Cases_on `sfs` THEN SRW_TAC [][] THENL [
    Cases_on `sfld` THEN SRW_TAC [][empty_inst_def],
    Cases_on `h` THEN SRW_TAC [][empty_inst_def]
  ]);
val _ = export_rewrites ["IDhd_inst_empty"]

val type_inst_empty = store_thm(
  "type_inst_empty",
  ``(!ty. type_inst empty_inst ty = SOME ty) /\
    (!id. cppid_inst empty_inst id = SOME (TypeID id)) /\
    (!ta. temparg_inst empty_inst ta = SOME ta) /\
    (!tva. temp_valarg_inst empty_inst tva = SOME tva) /\
    (!sfld. sfld_inst empty_inst sfld = SOME sfld)``,
  HO_MATCH_MP_TAC type_inst_ind THEN
  SRW_TAC [][] THEN SRW_TAC [][olmap_ALL_MEM, rich_listTheory.EL_IS_EL] THEN 
  SRW_TAC [][empty_inst_def]);

val type_match_refl = store_thm(
  "type_match_refl",
  ``!ty:CPP_Type. ty <= ty``,
  SIMP_TAC (srw_ss()) [type_match_def] THEN
  METIS_TAC [type_inst_empty]);

val cppID_inst_def = Define`
  cppID_inst s id =
    case cppid_inst s id of NONE -> NONE || SOME ty -> typeid ty
`;

val tempmap_comp_def = Define`
  tempmap_comp sigma (b,sfs,sn) = 
    case sfs of 
       [] -> if b then (T, [], sn) else sigma.tempmap sn
    || h::t -> if b then (T, THE (olmap (sfld_inst sigma) sfs), sn) 
               else 
                 let sfs' = THE (olmap (sfld_inst sigma) sfs)
                 in
                   case typeid (THE (IDhd_inst 
                                       sigma 
                                       (F, THE (olmap (sfld_inst sigma) sfs), 
                                        SFName sn)))
                    of 
                      SOME (IDConstant(b',sfs',SFName sn')) -> 
                        (b',sfs',sn')
                   || _ -> ARB
`;

val inst_comp_def = Define`
  inst_comp i2 i1 = <| typemap := THE o type_inst i2 o i1.typemap ;
                       tempmap := tempmap_comp i2 o i1.tempmap ;
                       valmap  := THE o temp_valarg_inst i2 o i1.valmap |>
`;

fun FTRY tac = TRY (tac THEN NO_TAC)

val option_case_NONE2 = store_thm(
  "option_case_NONE2", 
  ``(option_case NONE (\x. NONE) y = NONE)``,
  Cases_on `y` THEN SRW_TAC [][]);
val _ = export_rewrites ["option_case_NONE2"]

val cppid_non_typeid = store_thm(
  "cppid_non_typeid",
  ``(cppid_inst s id = SOME ty) /\ (typeid ty = NONE) ==>
    ?nm. (id = IDConstant(F,[],SFName nm)) /\ (s.typemap nm = ty)``,
  IDC_TAC `id` THEN SRW_TAC [][] THENL [
    Cases_on `b` THEN Cases_on `sfs` THEN FSRW_TAC [IDhd_inst_EQ_SOME] THEN 
    SRW_TAC [][] THEN FSRW_TAC [] THEN Cases_on `sf` THEN FSRW_TAC [],
        
    Cases_on `ty` THEN SRW_TAC [][]
  ]);

val olmap_APPEND = store_thm(
  "olmap_APPEND",
  ``olmap f (l1 ++ l2) = 
      case olmap f l1 of 
         NONE -> NONE
      || SOME l1' -> case olmap f l2 of 
                        NONE -> NONE
                     || SOME l2' -> SOME (l1' ++ l2')``,
  Q.ID_SPEC_TAC `l2` THEN Induct_on`l1` THEN SRW_TAC [][] THENL [
    Cases_on `olmap f l2` THEN SRW_TAC [][],
    Cases_on `f h` THEN SRW_TAC [][] THEN 
    Cases_on `olmap f l1` THEN SRW_TAC [][] THEN 
    Cases_on `olmap f l2` THEN SRW_TAC [][]
  ]);

val SNOC_11 = store_thm(
  "SNOC_11",
  ``!x y l1 l2. (l1 ++ [x] = l2 ++ [y]) = (l1 = l2) /\ (x = y)``,
  Induct_on `l1` THEN SRW_TAC [][] THENL [
    Cases_on `l2` THEN SRW_TAC [][],
    Cases_on `l2` THEN SRW_TAC [][] THEN METIS_TAC []
  ]);
    
val inst_comp_thm = store_thm(
  "inst_comp_thm",
  ``(!ty1 s1 ty2 ty3 s2.
        (type_inst s1 ty1 = SOME ty2) /\
        (type_inst s2 ty2 = SOME ty3) ==>
        (type_inst (inst_comp s2 s1) ty1 = SOME ty3)) /\
    (!id1 s1 s2 ty2 id3 ty4.
        (cppid_inst s1 id1 = SOME ty2) /\
        (typeid ty2 = SOME id3) /\
        (cppid_inst s2 id3 = SOME ty4) ==>
        (cppid_inst (inst_comp s2 s1) id1 = SOME ty4)) /\
    (!ta1 s1 ta2 ta3 s2.
        (temparg_inst s1 ta1 = SOME ta2) /\
        (temparg_inst s2 ta2 = SOME ta3) ==>
        (temparg_inst (inst_comp s2 s1) ta1 = SOME ta3)) /\
    (!tva1 s1 tva2 tva3 s2.
        (temp_valarg_inst s1 tva1 = SOME tva2) /\
        (temp_valarg_inst s2 tva2 = SOME tva3) ==>
        (temp_valarg_inst (inst_comp s2 s1) tva1 = SOME tva3)) /\
    (!sfld1 s1 sfld2 sfld3 s2.
        (sfld_inst s1 sfld1 = SOME sfld2) /\
        (sfld_inst s2 sfld2 = SOME sfld3) ==>
        (sfld_inst (inst_comp s2 s1) sfld1 = SOME sfld3))``,
  HO_MATCH_MP_TAC type_inst_ind THEN SRW_TAC [][]
  THEN FTRY (SRW_TAC [][]) THEN
  FTRY (FULL_SIMP_TAC (srw_ss()) []) THENL [
    (* TypeID *)
    Cases_on `typeid ty2` THENL [
      `?nm. (id1 = IDConstant (F, [], SFName nm)) /\ (s1.typemap nm = ty2)`
         by METIS_TAC [cppid_non_typeid] THEN
      SRW_TAC [][inst_comp_def, IDhd_inst_def],
      `ty2 = TypeID x` by (Cases_on `ty2` THEN FSRW_TAC []) THEN
      FSRW_TAC []
    ],

    (* MPtr *)
    FSRW_TAC [] THEN PROVE_TAC [],

    (* Function (type) case *)
    FSRW_TAC [olmap_ALL_MEM] THEN REPEAT STRIP_TAC THEN 
    Q_TAC SUFF_TAC `MEM (EL i tylist) tylist /\
                    ?ty2. (type_inst s1 (EL i tylist) = SOME ty2) /\
                          (type_inst s2 ty2 = SOME (EL i y0'))`
          THEN1 METIS_TAC [] THEN 
    SRW_TAC [][rich_listTheory.EL_IS_EL],

    (* IDVar case ? *)
    FSRW_TAC [] THEN SRW_TAC [][] THEN FSRW_TAC [],

    (* IDConstant case 1 *)
    FSRW_TAC [] THEN SRW_TAC [][] THEN FSRW_TAC [] THEN SRW_TAC [][] THEN 
    FSRW_TAC [olmap_ALL_MEM] THEN SRW_TAC [][] THEN 
    RULE_ASSUM_TAC (SIMP_RULE (bool_ss ++ DNF_ss) [AND_IMP_INTRO]) THEN 
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][rich_listTheory.EL_IS_EL],

    (* IDConstant case 2 *)
    FSRW_TAC [IDhd_inst_EQ_SOME] THEN SRW_TAC [][] THEN FSRW_TAC [] THENL [
      FSRW_TAC [olmap_EQ_SOME] THEN SRW_TAC [][] THEN 
      Q.EXISTS_TAC `SFName s'` THEN SRW_TAC [][] THEN 
      SRW_TAC [][inst_comp_def] THEN 
      Cases_on `s1.typemap s'` THEN FSRW_TAC [],

      SRW_TAC [][] THEN FSRW_TAC [olmap_EQ_SOME] THEN SRW_TAC [][] THEN 
      Cases_on `b2` THENL [
        FSRW_TAC [] THEN SRW_TAC [][] THEN 
        Q.EXISTS_TAC `SFTempCall s' z` THEN SRW_TAC [][] THEN 
        SRW_TAC [][inst_comp_def, tempmap_comp_def] THEN 
        Cases_on `sfs2` THEN FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [],
        FSRW_TAC [] THEN SRW_TAC [][] THEN 
        FSRW_TAC [IDhd_inst_EQ_SOME] THEN SRW_TAC [][] THENL [
          FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [olmap_EQ_SOME] THEN 
          SRW_TAC [][] THEN Q.EXISTS_TAC `SFTempCall s' z` THEN 
          SRW_TAC [][] THENL [
            FIRST_X_ASSUM MATCH_MP_TAC THEN 
            Q.EXISTS_TAC `SFTempCall s' tas` THEN 
            SRW_TAC [ETA_ss][],
            SRW_TAC [][inst_comp_def, tempmap_comp_def]
          ],
          Q.EXISTS_TAC `SFTempCall s' z` THEN SRW_TAC [][] THEN 
          FSRW_TAC [olmap_EQ_SOME] THEN SRW_TAC [][] THEN 
          FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THEN 
          SRW_TAC [][inst_comp_def, tempmap_comp_def] THEN 
          Q.UNABBREV_ALL_TAC THEN SRW_TAC [][IDhd_inst_def],
          FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [olmap_EQ_SOME] THEN 
          SRW_TAC [][] THEN Q.EXISTS_TAC `SFTempCall s' z` THEN 
          SRW_TAC [][] THENL [
            FIRST_X_ASSUM MATCH_MP_TAC THEN 
            Q.EXISTS_TAC `SFTempCall s' tas` THEN 
            SRW_TAC [ETA_ss][],
            SRW_TAC [][inst_comp_def, tempmap_comp_def] THEN 
            Q.UNABBREV_ALL_TAC THEN SRW_TAC [][IDhd_inst_def]
          ]
        ]
      ],

      SRW_TAC [][] THEN 
      FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [olmap_EQ_SOME] THEN SRW_TAC [][] THEN
      Cases_on `a` THEN FSRW_TAC [] THEN SRW_TAC [][] THEN 
      SRW_TAC [DNF_ss][] THEN Cases_on `b'` THEN FSRW_TAC [] THENL [
        SRW_TAC [][] THEN SRW_TAC [DNF_ss][] THEN 
        FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [olmap_APPEND] THEN 
        SRW_TAC [][] THEN 
        MAP_EVERY Q.EXISTS_TAC [`l2''`, `l1''`, `h`] THEN 
        SRW_TAC [][] THENL [ 
          FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [AND_IMP_INTRO, olmap_ALL_MEM] THEN
          SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN 
          METIS_TAC [rich_listTheory.EL_IS_EL],
          SRW_TAC [ETA_ss][inst_comp_def]
        ],
        FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [olmap_APPEND] THEN SRW_TAC [][] THEN
        MAP_EVERY Q.EXISTS_TAC [`l2''`,`sf'''`] THEN SRW_TAC [][] THEN 
        FULL_SIMP_TAC (srw_ss() ++ DNF_ss)
                      [IDhd_inst_EQ_SOME, AND_IMP_INTRO] 
        THENL [
          SRW_TAC [][] THEN Cases_on `l1''` THENL [
            FSRW_TAC [] THEN SRW_TAC [][] THEN 
            FSRW_TAC [olmap_EQ_SOME] THEN SRW_TAC [][] THEN 
            MAP_EVERY Q.EXISTS_TAC [`sfs1'`, `sf1'`] THEN 
            SRW_TAC [][] THENL [
              FSRW_TAC [olmap_ALL_MEM] THEN SRW_TAC [][] THEN 
              FIRST_X_ASSUM MATCH_MP_TAC THEN 
              METIS_TAC [rich_listTheory.EL_IS_EL],
              SRW_TAC [][inst_comp_def, IDhd_inst_def]
            ],
            FSRW_TAC [] THEN SRW_TAC [][] THEN 
            FSRW_TAC [olmap_EQ_SOME] THEN SRW_TAC [][] THEN 
            MAP_EVERY Q.EXISTS_TAC [`sfs1' ++ [sf1'] ++ t`, `h`] THEN 
            SRW_TAC [][] THENL [
              FSRW_TAC [olmap_ALL_MEM] THEN SRW_TAC [][] THEN 
              METIS_TAC [rich_listTheory.EL_IS_EL],
              SRW_TAC [ETA_ss][inst_comp_def, IDhd_inst_def]
            ]
          ],
          SRW_TAC [][] THEN Cases_on `l1''` THENL [
            FSRW_TAC [] THEN SRW_TAC [][] THEN 
            FSRW_TAC [olmap_EQ_SOME] THEN SRW_TAC [][] THEN 
            SRW_TAC [][SNOC_11] THENL [
              FSRW_TAC [olmap_ALL_MEM] THEN SRW_TAC [][] THEN 
              METIS_TAC [rich_listTheory.EL_IS_EL],
              SRW_TAC [ETA_ss][inst_comp_def, IDhd_inst_def]
            ],
            FSRW_TAC [] THEN SRW_TAC [][] THEN 
            FSRW_TAC [olmap_EQ_SOME] THEN SRW_TAC [][] THEN 
            REWRITE_TAC [SNOC_11] THEN SRW_TAC [][] THENL [
              FSRW_TAC [olmap_ALL_MEM] THEN SRW_TAC [][] THEN 
              METIS_TAC [rich_listTheory.EL_IS_EL],
              SRW_TAC [ETA_ss][inst_comp_def, IDhd_inst_def]
            ]
          ]
        ]
      ],

      SRW_TAC [][] THEN 
      FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [olmap_EQ_SOME] THEN 
      SRW_TAC [][] THEN SRW_TAC [DNF_ss][] THEN 
      Cases_on `b2` THEN FSRW_TAC [] THENL [
        SRW_TAC [][] THEN 
        FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [olmap_APPEND] THEN 
        SRW_TAC [][] THEN DISJ2_TAC THEN 
        MAP_EVERY Q.EXISTS_TAC [`l2''`, `s'`, `z`, `l1''`, `sfn2`] THEN 
        SRW_TAC [][] THENL [
          Cases_on `a` THEN FSRW_TAC [] THEN SRW_TAC [ETA_ss][] THEN 
          FULL_SIMP_TAC (srw_ss() ++ DNF_ss ++ ETA_ss) [],
          FULL_SIMP_TAC (srw_ss() ++ DNF_ss ++ ETA_ss) [olmap_ALL_MEM] THEN 
          METIS_TAC [rich_listTheory.EL_IS_EL],
          SRW_TAC [][inst_comp_def, tempmap_comp_def] THEN 
          Cases_on `sfs1` THEN SRW_TAC [][] THEN 
          FSRW_TAC [olmap_EQ_SOME]
        ],
        Cases_on `a` THEN FSRW_TAC [] THEN SRW_TAC [][] THEN 
        FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [olmap_APPEND] THEN 
        SRW_TAC [][] THEN FSRW_TAC [IDhd_inst_EQ_SOME] THENL [
          Q.EXISTS_TAC `l2''` THEN 
          Cases_on `l1''` THEN FSRW_TAC [] THEN SRW_TAC [][] THEN 
          SRW_TAC [][SNOC_11] THENL [
            FULL_SIMP_TAC (srw_ss() ++ DNF_ss ++ ETA_ss) [],
            FSRW_TAC [olmap_ALL_MEM] THEN METIS_TAC [rich_listTheory.EL_IS_EL],
            SRW_TAC [][inst_comp_def, tempmap_comp_def] THEN 
            FSRW_TAC [olmap_EQ_SOME] THEN 
            SRW_TAC [][LET_THM, IDhd_inst_def]
          ],
          SRW_TAC [][] THEN Q.EXISTS_TAC `l2''` THEN 
          Cases_on `l1''` THENL [
            FSRW_TAC [olmap_EQ_SOME] THEN SRW_TAC [][SNOC_11] THENL [
              FULL_SIMP_TAC (srw_ss() ++ DNF_ss ++ ETA_ss) [],
              FSRW_TAC [olmap_ALL_MEM] THEN 
              METIS_TAC [rich_listTheory.EL_IS_EL],
              SRW_TAC [][inst_comp_def, tempmap_comp_def]
            ],
            FSRW_TAC [olmap_EQ_SOME] THEN SRW_TAC [][SNOC_11] THENL [
              FULL_SIMP_TAC (srw_ss() ++ DNF_ss ++ ETA_ss) [],
              FSRW_TAC [olmap_ALL_MEM] THEN 
              METIS_TAC [rich_listTheory.EL_IS_EL],
              SRW_TAC [][inst_comp_def, tempmap_comp_def, LET_THM, 
                         IDhd_inst_def]
            ]
          ]
        ]
      ]
    ],

    (* TTemp case *)
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN METIS_TAC [],

    (* TOBj case *)
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN METIS_TAC [],

    (* TMPtr case *) 
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN 
    Q.EXISTS_TAC `ty'` THEN SRW_TAC [][],

    (* some tva case *)
    Cases_on `s1.valmap s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
    SRW_TAC [][inst_comp_def],

    (* SFTEmpCall case *)
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN 
    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [olmap_ALL_MEM] THEN 
    RULE_ASSUM_TAC (SIMP_RULE (bool_ss ++ DNF_ss) [AND_IMP_INTRO]) THEN 
    SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN 
    SRW_TAC [][rich_listTheory.EL_IS_EL]
  ]);

(* SANITY theorem = comment under definition 2 to the effect <= is
   transitive *)
val type_match_trans = store_thm(
  "type_match_trans",
  ``!(ty1:CPP_Type) ty2 ty3. ty1 <= ty2 /\ ty2 <= ty3 ==> ty1 <= ty3``,
  SRW_TAC [][type_match_def] THEN Q.EXISTS_TAC `inst_comp s' s` THEN
  SRW_TAC [][inst_comp_thm]);

val is_renaming_def = Define`
  is_renaming s = 
    (!v. ?nm. s.typemap v = TypeID (IDConstant(F,[],SFName nm))) /\
    (!v. ?nm. s.tempmap v = (F,[],nm)) /\
    (!v. ?nm. s.valmap v = TVAVar nm)
`;

val empty_inst_is_renaming = store_thm(
  "empty_inst_is_renaming",
  ``is_renaming empty_inst``,
  SRW_TAC [][empty_inst_def, is_renaming_def]);

val tyinst_sz_def = Define`
  (tyinst_sz (Class cid) = 2n) /\
  (tyinst_sz (Ptr ty) = 1 + tyinst_sz ty) /\
  (tyinst_sz (MPtr id ty) = 1 + cppidinst_sz id + tyinst_sz ty) /\
  (tyinst_sz (Ref ty) = 1 + tyinst_sz ty) /\
  (tyinst_sz (Array ty n) = 1 + tyinst_sz ty) /\
  (tyinst_sz (Function ty tyl) = 1 + tyinst_sz ty + tylinst_sz tyl) /\
  (tyinst_sz (Const ty) = 1 + tyinst_sz ty) /\
  (tyinst_sz (TypeID id) = 1) /\
  (tyinst_sz Void = 2) /\
  (tyinst_sz BChar = 2) /\
  (tyinst_sz Bool = 2) /\
  (tyinst_sz (Unsigned _) = 2) /\
  (tyinst_sz (Signed _) = 2) /\
  (tyinst_sz Float = 2) /\
  (tyinst_sz Double = 2) /\
  (tyinst_sz LDouble = 2)

     /\

  (cppidinst_sz (IDVar s) = 1) /\
  (cppidinst_sz (IDConstant tn) = 1)

     /\

  (sfldinst_sz (SFTempCall s tal) = 1 + talinst_sz tal) /\
  (sfldinst_sz (SFName s) = 1)

     /\

  (tainst_sz (TType ty) = 1 + tyinst_sz ty) /\
  (tainst_sz (TTemp tid) = 1 + cppidinst_sz tid) /\
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
  ``(typeid ty = SOME id) ==> (tyinst_sz ty = 1)``,
  Cases_on `ty` THEN SRW_TAC [][]);

val zero_lt_tysize = store_thm(
  "zero_lt_tysize",
  ``0 < tyinst_sz ty``,
  Cases_on `ty` THEN SRW_TAC [ARITH_ss][]);

val tyinst_sz_EQ_1 = store_thm(
  "tyinst_sz_EQ_1",
  ``(tyinst_sz ty = 1) = ?id. ty = TypeID id``,
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
                 cppidinst_sz id1 <= tyinst_sz ty2) /\
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
    Cases_on `p` THEN Case
    MATCH_ACCEPT_TAC (GEN_ALL zero_lt_tysize),

    Cases_on `p` THEN Cases_on `r` THEN Cases_on `q` THEN 
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN 
    FSRW_TAC [IDhd_inst_EQ_SOME] THEN SRW_TAC [][] THEN 
    Cases_on `s.typemap s'` THEN SRW_TAC [ARITH_ss][zero_lt_tysize] THENL [
      Q.SPEC_THEN `C0` MP_TAC (GEN_ALL zero_lt_tysize) THEN DECIDE_TAC,
      Q.SPEC_THEN `C''` MP_TAC (GEN_ALL zero_lt_tysize) THEN DECIDE_TAC,
      
      
    

    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [] THEN RES_TAC,

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
                               ?nm. s.tempmap v = IDVar nm) /\
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

val tyfrees_defn = Defn.Hol_defn "tyfrees" `
  (tyfrees (Class cid) = {}) /\
  (tyfrees (Ptr ty) = tyfrees ty) /\
  (tyfrees (MPtr id ty) = cppidfrees id UNION tyfrees ty) /\
  (tyfrees (Ref ty) = tyfrees ty) /\
  (tyfrees (Array ty n) = tyfrees ty) /\
  (tyfrees (Function ty tyl) = 
     FOLDL (\a ty.  a UNION tyfrees ty) (tyfrees ty) tyl) /\
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
  (cppidfrees (IDConstant (b,sfs,sf)) = 
     FOLDL (\a sf. a UNION sfldfrees sf) (sfldfrees sf) sfs)

     /\

  (sfldfrees (SFTempCall s tal) = FOLDL (\a ta. a UNION tafrees ta) {} tal) /\
  (sfldfrees (SFName s) = {})

     /\

  (tafrees (TType ty) = tyfrees ty) /\
  (tafrees (TTemp tid) = cppidfrees tid) /\
  (tafrees (TVal tva) = tvalfrees tva)

     /\

  (tvalfrees (TNum i) = {}) /\
  (tvalfrees (TObj id) = cppidfrees id) /\
  (tvalfrees (TMPtr id ty) = cppidfrees id UNION tyfrees ty) /\
  (tvalfrees (TVAVar s) = valfree_sing s)
`

val (tyfrees_def, tyfrees_ind) = Defn.tprove(
  tyfrees_defn, 
  WF_REL_TAC 
    `^(last (TotalDefn.guessR tyfrees_defn))` THEN 
  SRW_TAC [ARITH_ss][] THENL [
    Induct_on `tyl` THEN SRW_TAC [][] THEN SRW_TAC [ARITH_ss][] THEN 
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `sfs` THEN SRW_TAC [][] THEN 
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Induct_on `tal` THEN SRW_TAC [][] THEN 
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);
val _ = save_thm("tyfrees_def", tyfrees_def)
val _ = save_thm("tyfrees_ind", tyfrees_ind)
val _ = export_rewrites ["tyfrees_def"]

val renaming_upto_FOLDL = store_thm(
  "renaming_upto_FOLDL",
  ``!list acc s. 
       (!e. MEM e list ==> renaming_upto (f e) s) /\
       renaming_upto acc s ==> 
       renaming_upto (FOLDL (\a e. a UNION f e) acc list) s``,
  Induct THEN SRW_TAC [][]);

val tylinst_sz_leq = prove(
  ``!xl yl x y. 
      (x + tylinst_sz xl = y + tylinst_sz yl) /\ x <= y /\
      (LENGTH xl = LENGTH yl) /\
      (!i. i < LENGTH xl ==> tyinst_sz (EL i xl) <= tyinst_sz (EL i yl)) ==>
      (x = y) /\ (tylinst_sz xl = tylinst_sz yl)``,
  Induct THEN1 SRW_TAC [ARITH_ss][] THEN 
  Cases_on `yl` THEN SIMP_TAC (srw_ss()) [] THEN 
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  `tyinst_sz h' <= tyinst_sz h`
      by (FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][]) THEN 
  FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` (MP_TAC o Q.GEN `i`)) THEN 
  SIMP_TAC (srw_ss()) [] THEN 
  `x + tyinst_sz h' + 1 + tylinst_sz xl = 
     y + tyinst_sz h + 1 + tylinst_sz t` by DECIDE_TAC THEN 
  `x + tyinst_sz h' + 1 <= y + tyinst_sz h + 1` by DECIDE_TAC THEN 
  STRIP_TAC THEN 
  `(x + tyinst_sz h' + 1 = y + tyinst_sz h + 1) /\ 
   (tylinst_sz xl = tylinst_sz t)`
     by METIS_TAC [] THEN 
  DECIDE_TAC);
  
val type_match_size_eq_renaming = store_thm(
  "type_match_size_eq_renaming",
  ``(!s ty1 ty2. (type_inst s ty1 = SOME ty2) /\
                 (tyinst_sz ty2 = tyinst_sz ty1) ==>
                 renaming_upto (tyfrees ty1) s) /\
    (!s id1 ty2. (cppid_inst s id1 = SOME ty2) /\
                 (tyinst_sz ty2 = 1 + cppidinst_sz id1) ==>
                 renaming_upto (cppidfrees id1) s) /\
    (!s ta1 ta2. (temparg_inst s ta1 = SOME ta2) /\
                 (tainst_sz ta2 = tainst_sz ta1) ==>
                 renaming_upto (tafrees ta1) s) /\
    (!s tva1 tva2. (temp_valarg_inst s tva1 = SOME tva2) /\
                   (tvainst_sz tva2 = tvainst_sz tva1) ==>
                   renaming_upto (tvalfrees tva1) s) /\
    (!s sfld1 sfld2. (sfld_inst s sfld1 = SOME sfld2) /\
                     (sfldinst_sz sfld2 = sfldinst_sz sfld1) ==>
                     renaming_upto (sfldfrees sfld1) s) ``,
  HO_MATCH_MP_TAC type_inst_ind THEN SRW_TAC [][] THEN 
  FULL_SIMP_TAC (srw_ss()) [] THENL [
    `cppidinst_sz id1 < tyinst_sz ty /\ tyinst_sz ty1 <= tyinst_sz y0` 
       by METIS_TAC [type_match_size_increase] THEN 
    IMP_RES_TAC typeid_size THEN 
    SRW_TAC [ARITH_ss][],

    `cppidinst_sz id1 < tyinst_sz ty /\ tyinst_sz ty1 <= tyinst_sz y0` 
       by METIS_TAC [type_match_size_increase] THEN 
    IMP_RES_TAC typeid_size THEN 
    SRW_TAC [ARITH_ss][],

    FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [AND_IMP_INTRO, olmap_ALL_MEM] THEN
    `(!i. i < LENGTH tylist ==> 
          (tyinst_sz (EL i tylist) <= tyinst_sz (EL i y0))) /\
     tyinst_sz ty1 <= tyinst_sz x0`
       by METIS_TAC [type_match_size_increase] THEN 
    
    
      
    MATCH_MP_TAC renaming_upto_FOLDL THEN SRW_TAC [][] THENL [

    SRW_TAC [][renaming_upto_def, tyfree_sing_def],

    

    
      
    `tyinst_sz ty = 1 + cppidinst_sz id` by 


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
  (expr_inst sigma (SVar e id) =
     OP2CMB SVar (expr_inst sigma e) (cppID_inst sigma id)) /\
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
  (expr_inst sigma (EThrow eopt) = OPTION_MAP EThrow (expropt_inst sigma eopt))

     /\

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
                                       (cppID_inst sigma id)))

     /\

  (centry_inst sigma (CFnDefn virtp ty fld params body) =
     case type_inst sigma ty of
        NONE -> NONE
     || SOME ty' ->
          (case sfld_inst sigma fld of
              NONE -> NONE
           || SOME sfld' ->
                OP2CMB (CFnDefn virtp ty' sfld')
                       (olmap (\ (n,ty).
                                 OPTION_MAP ((,) n) (type_inst sigma ty))
                              params)
                       (case body of
                           NONE -> SOME NONE
                        || SOME NONE -> SOME (SOME NONE)
                        || SOME (SOME st) ->
                             (case stmt_inst sigma st of
                                 NONE -> NONE
                              || SOME st' -> SOME (SOME (SOME st')))))) /\
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
  (centry_inst sigma (Destructor virtp bodyopt) =
     OPTION_MAP (Destructor virtp) (OPTION_MAP (stmt_inst sigma) bodyopt))

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

val _ = save_thm("stmt_inst_def", stmt_inst_def)
val _ = save_thm("stmt_inst_ind", stmt_inst_ind)
val _ = export_rewrites ["stmt_inst_def"]

val extdecl_inst_defn = Defn.Hol_defn "extdecl_inst" `
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
     OP2CMB ClassDestDef (cppID_inst sub cnm) (stmt_inst sub body)) /\
  (extdecl_inst sub (NameSpace s edecs) =
     OPTION_MAP (NameSpace s) (olmap (extdecl_inst sub) edecs))
`

val (extdecl_inst_def, extdecl_inst_ind) = Defn.tprove(
  extdecl_inst_defn,
  WF_REL_TAC `measure (\(sub,e). ext_decl_size e)` THEN
  Induct_on `edecs` THEN
  SRW_TAC [ARITH_ss][#2 (TypeBase.size_of ``:ext_decl``)] THENL [
    DECIDE_TAC,
    FIRST_X_ASSUM (Q.SPECL_THEN [`s`, `a`] MP_TAC) THEN
    SRW_TAC [ARITH_ss][]
  ]);

val _ = save_thm("extdecl_inst_def", extdecl_inst_def)
val _ = save_thm("extdecl_inst_ind", extdecl_inst_ind)
val _ = export_rewrites ["extdecl_inst_def"]

val _ = export_theory()

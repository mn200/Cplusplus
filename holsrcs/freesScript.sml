(* Calculating the free names of a type *)

(* Michael Norrish *)

open HolKernel boolLib Parse BasicProvers
open simpLib bossLib arithmeticTheory pred_setTheory boolSimps

local open stringTheory integerTheory in end;
open listTheory typesTheory

val _ = new_theory "frees";



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

val freerec_UNION_empty = store_thm(
  "freerec_UNION_empty",
  ``(freerec_UNION fr1 {} = fr1) /\ (freerec_UNION {} fr2 = fr2)``,
  SRW_TAC [][freerec_UNION_def, empty_freerec_def,
             theorem "frees_record_component_equality"]);
val _ = export_rewrites ["freerec_UNION_empty"]

val DISJOINT_def = Define`
  DISJOINT f1 f2 = pred_set$DISJOINT f1.tyfvs f2.tyfvs /\
                   pred_set$DISJOINT f1.tempfvs f2.tempfvs /\
                   pred_set$DISJOINT f1.valfvs f1.valfvs
`;

val tyfree_sing_def = Define`
  tyfree_sing s = <| tyfvs := {s}; tempfvs := {}; valfvs := {} |>
`;
val tempfree_sing_def = Define`
  tempfree_sing s = <| tyfvs := {}; tempfvs := {s}; valfvs := {} |>
`
val valfree_sing_def = Define`
  valfree_sing s = <| tyfvs := {}; tempfvs := {}; valfvs := {s} |>
`


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

  (cppidfrees (IDConstant b sfs sf) =
     FOLDL (\a sf. a UNION sfldfrees sf)
           (sfldfrees sf UNION
            (if b then {}
             else case IDhd (IDConstant b sfs sf) of
                    IDName s -> tyfree_sing s
                 || IDTempCall s targs -> tempfree_sing s) )
           sfs)

     /\

  (sfldfrees (IDTempCall s tal) = FOLDL (\a ta. a UNION tafrees ta) {} tal) /\
  (sfldfrees (IDName s) = {})

     /\

  (tafrees (TType ty) = tyfrees ty) /\
  (tafrees (TTemp (IDConstant b sfs sf)) =
     case sf of
       IDName s -> if (sfs = []) /\ ~b then tempfree_sing s
                   else cppidfrees (IDConstant b sfs sf)
    || IDTempCall s targs -> {}) /\
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


val _ = export_theory();

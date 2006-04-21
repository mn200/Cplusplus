(* \#line cholera-model.nw 26 *)
open HolKernel boolLib Parse mnUtils Psyntax
open simpLib bossLib boolSimps arithmeticTheory pred_setTheory
infix >-

val hol_ss = bossLib.list_ss

(* \#line cholera-model.nw 1694 *)
local open cholmemTheory cholstmtTheory in end;

(* \#line cholera-model.nw 1734 *)
open Datatype
val _ = new_theory "cholstate";

val _ = Hol_datatype `fn_info = <| return_type : CType ;
                                   parameters  : (string # CType) list ;
                                   body        : CStmt |>`;
val _ = Hol_datatype
  `CState = <| allocmap : num -> bool ;
               fnmap    : string -> fn_info ;
               gstrmap  : string -> str_info ;
               gtypemap : string -> CType ;
               gvarmap  : string -> num ;
               initmap  : num -> bool ;
               locmap   : num -> MemObj ;
               strmap   : string -> str_info ;
               typemap  : string -> CType ;
               varmap   : string -> num |>`;
(* \#line cholera-model.nw 1769 *)
val _ = new_definition(
  "expr_type_comps",
  (--`expr_type_comps s = (s.strmap, s.typemap)`--));
(* \#line cholera-model.nw 1793 *)
val val2mem = new_definition (
  "val2mem",
  --`val2mem s loc l =
       s with locmap updated_by
                (\lmp x. if loc <= x /\ x < loc + LENGTH l then
                           EL (x - loc) l
                         else lmp x)`--);
(* \#line cholera-model.nw 1809 *)
val mem2val = new_recursive_definition {
  name = "mem2val",  (* memory to value *)
  def = (--`(mem2val s loc 0 = []) /\
            (mem2val s loc (SUC n) =
                s.locmap loc :: mem2val s (loc+1) n)`--),
  rec_axiom = prim_recTheory.num_Axiom
};
(* \#line cholera-model.nw 1822 *)
val mem2val_LENGTH = store_thm(
  "mem2val_LENGTH",
  --`!sz s n. LENGTH (mem2val s n sz) = sz`--,
  numLib.INDUCT_TAC THEN ASM_SIMP_TAC hol_ss [mem2val]);
(* \#line cholera-model.nw 1838 *)
val _ = new_definition(
  "install_global_maps",
  (--`install_global_maps s =
         s with <| gvarmap := s.varmap ;
                   gstrmap := s.strmap;
                   gtypemap := s.typemap |>`--));
(* \#line cholera-model.nw 1698 *)
val _ = export_theory();

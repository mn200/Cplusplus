(* Overloading Resolution for C++ Functions *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps


(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
local open side_effectsTheory statesTheory operatorsTheory in end



val _ = new_theory "overloading"

(* given the state, a function-identifier, and the types of the actual
   arguments, return ("relationally"), the return type, parameters and
   body of the function that should be called *)
val find_best_fnmatch_def = Define`
  find_best_fnmatch s fnid actualtypes rettype params body =
    (s.fnmap ' fnid = <| return_type := rettype;
                         parameters := params;
                         body := body |>)
`;

val _ = export_theory()
open HolKernel Parse boolLib bossLib

local open stringTheory in end

val _ = new_theory "names"

val _ = Hol_datatype`CPPname = <| base : string ;
                                  absolute : bool ;
                                  nspaces : string list ;
                                  classes : string list
                               |>`

val is_class_name_def = Define`is_class_name n = ~(NULL n.classes)`;

val Base_def = Define`
  Base s = <| base := s; absolute := F; nspaces := []; classes := [] |>
`;

val Member_def = Define`
  Member nm mem = <| base := mem;
                     absolute := nm.absolute;
                     nspaces := nm.nspaces;
                     classes := (nm.classes ++ [nm.base])
                  |>
`;

val _ = export_theory()

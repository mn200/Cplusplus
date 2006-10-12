open HolKernel Parse boolLib bossLib

local open stringTheory in end

val _ = new_theory "names"

val _ = Hol_datatype`CPPname = Base of string
                             | ClassN of string => CPPname
                             | NameScopeN of string => CPPname
                             | TopScope of CPPname`

val _ = export_theory()

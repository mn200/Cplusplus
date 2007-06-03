(* Dynamic Semantics of C++ top-level or "external" declarations *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps


(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open typesTheory memoryTheory expressionsTheory staticsTheory class_infoTheory
open aggregatesTheory declaration_dynamicsTheory
local
  open side_effectsTheory statesTheory operatorsTheory overloadingTheory
       dynamicsTheory
in end

val _ = new_theory "ext_decls";

val _ = set_trace "inddef strict" 1



(* ----------------------------------------------------------------------
    how to evaluate a sequence of external declarations
   ---------------------------------------------------------------------- *)

(* if the evaluation can't get the list of external declarations to the
   empty list, this is (implicitly) an occurrence of undefined behaviour *)
val (emeaning_rules, emeaning_ind, emeaning_cases) = Hol_reln`

(* RULE-ID: global-fndefn *)
(*     installation of a non-class function *)
(!s0 s fval name rettype params body edecls.
     installfn s0 Ptr rettype name params body fval s /\
     ~is_class_name s0 name /\
     (~is_qualified name \/ ~is_class_name s0 (class_part name)) 
   ==>
     emeaning
       (FnDefn rettype name params body :: edecls) s0
       (s, edecls))

   /\

(* RULE-ID: member-fndefn *)

(* We're assuming that the program is well-formed, and so one might
   think it unnecessary to check that the function has been correctly
   declared in a class somewhere else.  However, we do need to extract
   how the function was declared in terms of its virtualness, static-ness
   and protection because all this information is not repeated for us.
*)

(!rettype virtp name params body edecls s0 s ci staticp prot cpart base.
     is_qualified name /\
     is_class_name s0 name /\
     (cpart = class_part name) /\ 
     (base = IDtl name) /\                              
     (ci = cinfo s0 cpart) /\
     ((?pms'. MEM (CFnDefn virtp rettype base pms' NONE, staticp, prot) 
                  ci.fields /\
              (MAP SND pms' = MAP SND params)) \/
      MEM (FldDecl base (Function rettype (MAP SND params)), staticp, prot)
          ci.fields /\ ~virtp) /\
     install_member_functions 
        cpart 
        s0 
        [(CFnDefn virtp rettype base params (SOME (SOME body)), staticp, prot)]
        s
   ==>
     emeaning (FnDefn rettype name params body :: edecls) s0
              (s, edecls))

   /\

(* RULE-ID: global-declmng *)
(!s0 s d0 ds edecls.
     declmng meaning (d0, s0) (ds, s)
   ==>
     emeaning (Decl d0 :: edecls) s0 (s, MAP Decl ds ++ edecls))

   /\

(* RULE-ID: global-class-declaration *)
(*   A class declaration has no effect dynamically; its manipulation of name
     spaces has been recorded in phase1. 
*)
(!name edecls s0.
     T
   ==>
     emeaning
        (Decl (VStrDec name NONE) :: edecls) s0 (s0, edecls))

   /\

(* RULE-ID: global-class-definition *)
(!s0 s name info0 userdefs info edecls.
     ((info,userdefs) = define_default_specials info0) /\
     install_member_functions name s0 info.fields s
   ==>
     emeaning (Decl (VStrDec name (SOME info0)) :: edecls) s0
              (s, edecls))
`;

val _ = export_theory() 


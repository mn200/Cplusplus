(* Resolution of names within a sequence of external declarations *)

(* (Can be viewed as a phase of compilation) *)

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
in end

val _ = new_theory "name_resolution";

val lift_vdec_def = Define`
  lift_vdec n (VDec

val flatten_nspaces_def = Define`
  (flatten_nspaces [] = []) /\
  (flatten_nspaces (NameSpace n ds :: t) =
     MAP (


val _ = Hol_datatype`
  nameres_ctxt = <|
    objs : string -> CPP_ID # CPP_Type ;
    classes : string -> CPP_ID ;
    nspaces : string -> string list ;
  |>
`;


val _ = Hol_datatype`
  nametypes = NSname | Classname | Unknown
`

val tn_outermost_def = Define`
  (tn_outermost (b, [], s) = (b, s, Unknown)) /\
  (tn_outermost (b, h::t, s) = (b, h, NSname))
`;

val tid_outermost_def = Define`
  (tid_outermost (TemplateConstant tn) = tn_outermost tn)
`

val get_outerid_def = Define`
  (get_outerid (IDFld id sf) =
     case get_outerid id of
        (b, s, Unknown) -> (b,s,Classname)
     || x -> x) /\
  (get_outerid (IDTempCall tid targs) = tid_outermost tid) /\
  (get_outerid (IDConstant tn) = tn_outermost tn)
`;

val tid_prepend_def = Define`
  tid_prepend nslist clist (TemplateConstant (b, ns, s)) =
    if ns = [] then
      if clist = [] then
        IDConstant(T, nslist, s)
      else

val id_prepend_def = Define`
  (id_prepend nslist clist (IDFld id sf) =
     IDFld (id_prepend nslist clist id) sf) /\
  (id_prepend nslist clist (IDConstant (b, ns, s)) =
     if ns = [] then
       if clist = [] then
         IDConstant(T, nslist, s)
       else
         FOLDL IDFld (IDConstant(T,nslist, HD clist)) (TL clist ++ [s])
     else
       IDConstant (T, nslist ++ ns, s)) /\
  (id_prepend nslist clist (IDVar s) = IDVar s) /\
  (id_prepend nslist clist (IDTempCall tid targs) =
     IDTempCall (tid_prepend nslist clist tid) targs)
`;

val translate_tid_def = Define`
  (translate_tid ctxt (TemplateConstant tn) =
     case tn_outermost tn of
        (T, h, ty) -> TemplateConstant tn
     || (F, h, NSname) -> TemplateConstant (T, ctxt.nspaces h

val translate_id_def = Define`
  (translate_id ctxt classp (IDVar s) = IDVar s) /\
  (translate_id ctxt classp (IDFld id sfld) =
     IDFld (translate_id ctxt T id) sfld) /\
  (translate_id ctxt (IDTempCall tid targs) =
     IDTempCall (translate_tid ctxt tid)





val _ = set_trace "inddef strict" 1


(* non-function field resolution rule
(* Note how the path p is used:
     - to figure out the static type of the l-value (LAST p)
     - to derive the path from the most-derived class to the sub-object
       enclosing the field.  The offset is calculated with respect to
       this because the sub-object could be anywhere, and might be virtual.


       subobject of the original LVal is ignored.  This is because
   only functions can get a "virtual" treatment.
   This doesn't mean that a field reference can't be to an ancestor's field.

*)
(!s cnm fld ftype Cflds se offn i a p p'.
     s |- LAST p has least fld -: ftype via p' /\
     (Cflds = THE (nsdmembers s (LAST p'))) /\
     object_type ftype /\
     lookup_field_info (MAP (\ (n,ty). (SFName n, ty)) Cflds) fld (i,ftype) /\
     offset (sizeofmap s) (MAP (UNCURRY NSD) Cflds) i offn
   ==>
     ^mng (mExpr (SVar (LVal a (Class cnm) p) fld) se) s
          (s, ev (LVal (a + subobj_offset s (cnm, p ^ p') + offn) ftype
                       (default_path ftype)) se))
*)


(* ----------------------------------------------------------------------
    how to evaluate a sequence of external declarations
   ---------------------------------------------------------------------- *)

(* split a name into a class::fld part *)
val class_fld_split_def = Define`
  class_fld_split (IDFld id fld) = (id, fld)
`;


(* if the evaluation can't get the list of external declarations to the
   empty list, this is (implicitly) an occurrence of undefined behaviour *)
val (emeaning_rules, emeaning_ind, emeaning_cases) = Hol_reln`

(* RULE-ID: global-fndefn *)
(!s0 s fval name rettype params body ftype edecls.
     installfn s0 Ptr rettype name params body fval s /\
     ~(name IN FDOM s.typemap) /\ ~is_class_name s0 name /\
     (ftype = Function rettype (MAP SND params))
   ==>
     emeaning
       (FnDefn rettype name params body :: edecls) s
       (s with <| typemap updated_by (\tm. tm |+ (name, ftype)) |>,
        edecls))

   /\

(* RULE-ID: member-fndefn *)
(* The first MEM clause looks up the assumed declaration, and gets
   static-ness and protection information there.
   The second MEM clauses checks that this is not a duplicate definition
     (this is a static check, one that would be performed by the compiler
      if the duplication occurred within a single translation unit, or by
      the linker if it occurred across multiple units)
*)
(!rettype userdefs name params body edecls s0 s cinfo staticp prot cpart base.
     is_class_name s0 name /\
     ((cpart, base) = class_fld_split name) /\
     (SOME (cinfo, userdefs) = s0.classmap ' cpart) /\
     (?pms'.
         MEM (CFnDefn rettype base pms' NONE, staticp, prot)
             cinfo.fields /\
         (MAP SND pms' = MAP SND params)) /\
     (!bdy' rettype' statp prot pms'.
         MEM (CFnDefn rettype' base pms' bdy', statp, prot) cinfo.fields
           ==>
         ~(MAP SND pms' = MAP SND params)) /\
     install_member_functions cpart s0
                              [(CFnDefn rettype base params (SOME body),
                                staticp, prot)]
                              s
   ==>
     emeaning (FnDefn rettype name params body :: edecls) s0
              (s, edecls))

   /\

(* RULE-ID: global-declmng *)
(!s0 s d0 ds edecls.
     declmng meaning copy2globals (d0, s0) (ds, s)
   ==>
     emeaning (Decl d0 :: edecls) s0 (s, MAP Decl ds ++ edecls))

   /\

(* RULE-ID: global-class-declaration *)
(*   one might argue that this is a useless rule to have dynamically, as
     class declarations are only made for the benefit of static type-checking
*)
(!name edecls s0.
     T
   ==>
     emeaning
        (Decl (VStrDec name NONE) :: edecls) s0
        (copy2globals
           (s0 with classmap updated_by (\sm. sm |+ (name, NONE))),
         edecls))

   /\

(* RULE-ID: global-class-definition *)
(!s0 s name info0 userdefs info edecls.
     ((info,userdefs) = define_default_specials info0) /\
     install_member_functions name s0 info.fields s
   ==>
     emeaning (Decl (VStrDec name (SOME info0)) :: edecls) s0
              (copy2globals
                  (s with <| classmap updated_by
                                      (\sm. sm |+ (name,
                                                   SOME (info, userdefs))) |>),
               edecls))
`;




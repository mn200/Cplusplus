(* The C++ class hierarchy, and functions on it, derived from information
   stored in a state *)

(* Michael Norrish *)

(* pro-forma *)
open HolKernel boolLib Parse bossLib BasicProvers
open boolSimps

(* Standard HOL ancestory theories *)
open arithmeticTheory pred_setTheory integerTheory
local open wordsTheory integer_wordTheory finite_mapTheory in end

(* C++ ancestor theories  *)
open statesTheory

val _ = new_theory "hierarchy";

(* BAD_ASSUMPTION: for the moment, our hierarchies only allow one
   ancestor class at most
*)

(* c2 is an ancestor of c1 *)
val ancestor_def = Define`
  ancestor s c1 c2 = c1 IN FDOM (deNONE s.classmap) /\
                     ((THE(s.classmap ' c1)).ancestors = SOME c2)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,2),
                                  BeginFinalBlock(PP.CONSISTENT,0), TM,
                                  BreakSpace(1,0), TOK "<", BreakSpace(1,0)],
                   term_name = "ancestor",
                   fixity = Infix(NONASSOC, 460) }


(* See the Subjobjs_R relation of Wasserab et al. *)
val (rsubobjs_rules, rsubobjs_ind, rsubobjs_cases) = Hol_reln`
  (!C s. C IN FDOM (deNONE s.classmap) ==> rsubobjs s (C, [C]))

    /\

  (!C Cs D s.
      s |- C < D /\ rsubobjs s (D, Cs)
   ==>
      rsubobjs s (C, C::Cs))
`;

(* The Subobjs relation of Wasserab et al.  Because of the absence of
   multiple inheritance, let alone virtual (shared) ancestors, this is
   currently the same as rsubobjs *)
val (subobjs_rules, subobjs_ind, subobjs_cases) = Hol_reln`
  (!C Cs s. rsubobjs s (C,Cs) ==> subobjs s (C,Cs))
`;

val pord1_def = Define`
  pord1 (s, C) Cs Ds = (Cs = FRONT Ds) /\ (C,Cs) IN rsubobjs s /\
                       (C,Ds) IN rsubobjs s
`;


(* s |- path C to D unique *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Suffix 465,
                  pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,0),
                                 TOK "path", BreakSpace(1,0), TM,
                                 BreakSpace(1,0), TOK "to", BreakSpace(1,0),
                                 TM, BreakSpace(1,0), TOK "unique"],
                  term_name = "unique_path"}

val unique_path_def = Define`
  s |- path C to D unique = ?!Cs. subobjs s (C,Cs) /\ (LAST Cs = D)
`

(* s |- path C to D via Cs *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix (NONASSOC, 460),
                  pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,0),
                                 TOK "path", BreakSpace(1,0), TM,
                                 BreakSpace(1,0), TOK "to", BreakSpace(1,0),
                                 TM, BreakSpace(1,0), TOK "via",
                                 BreakSpace(1,0)],
                  term_name = "path_via"}
val path_via_def = Define`
  s |- path C to D via Cs = (C,Cs) IN subobjs s /\ (LAST Cs = D)
`;

(* finding fields W et al. 5.1.3 *)
val fieldname_def = Define`
  (fieldname (FldDecl n ty) = n) /\
  (fieldname (CFnDefn retty n args body) = n)
`

val fieldtype_def = Define`
  (fieldtype (FldDecl n ty) = ty) /\
  (fieldtype (CFnDefn retty n args body) = Function retty (MAP SND args))
`;

val FieldDecls_def = Define`
  FieldDecls s C fnm =
     { (Cs, ty) | (C,Cs) IN subobjs s /\
                  LAST Cs IN FDOM (deNONE s.classmap) /\
                  ?cinfo fld. (deNONE s.classmap ' (LAST Cs) = cinfo) /\
                              MEM fld cinfo.fields /\
                              (fieldname (FST fld) = fnm) /\
                              (fieldtype (FST fld) = ty) }
`;


(* s |- C has least fld -: ty via Cs *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix (NONASSOC, 460),
                  pp_elements = [BreakSpace(1,0), TOK "|-", BreakSpace(1,0),
                                 TM, BreakSpace(1,0),
                                 TOK "has", BreakSpace(1,0),
                                 TOK "least", BreakSpace(1,0),
                                 PPBlock([TM, BreakSpace(1,0),
                                          TOK "-:", BreakSpace(1,0), TM],
                                         (PP.CONSISTENT, 0)),
                                 BreakSpace(1,0), TOK "via", BreakSpace(1,0)],
                  term_name = "fieldty_via"}
val fieldty_via_def = Define`
  s |- C has least fld -: ty via Cs =
         (Cs,ty) IN FieldDecls s C fld /\
         !Cs' ty'. (Cs',ty') IN FieldDecls s C fld ==>
                   RTC (pord1 (s,C)) Cs Cs'
`


(* nsdmembers (non-static data-members) *)
val nsdmembers_def = Define`
  nsdmembers s c =
    case FLOOKUP (deNONE s.classmap) c of
       NONE -> NONE
    || SOME cinfo ->
         SOME
           (mapPartial
              (\ci. case ci of
                       (CFnDefn ret nm args bod, stat, prot) -> NONE
                    || (FldDecl nm ty, stat, prot) -> if stat then NONE
                                                      else SOME (nm,ty))
              cinfo.fields)
`








val _ = export_theory();

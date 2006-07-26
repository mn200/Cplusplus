fun read_test fname = let
  val strm = TextIO.openIn fname
  val string = TextIO.inputAll strm
  val _ = TextIO.closeIn strm
in
  Parse.Term [QUOTE string]
end

local open dynamicsTheory statesTheory typesTheory simpLib BasicProvers
           class_infoTheory
in
val e1_ss = srw_ss() ++ rewrites [vdeclare_def, copy2globals_def, initial_state_def,
                                  object_type_def, GSYM RIGHT_EXISTS_AND_THM,
                                  GSYM LEFT_EXISTS_AND_THM,
                                  malloc_def, sizeofmap_def, lfimap_def]
end

fun emeaning_eval1 ctxt edecl state = let
  open dynamicsTheory statesTheory typesTheory
  open simpLib BasicProvers
  val rwt1 =
      SIMP_RULE (srw_ss()) []
                (SPEC_ALL (SPECL [edecl,state] emeaning_cases))
  fun splitup th = let
    val th' = #2 (EQ_IMP_RULE th)
  in
    CONJUNCTS (REWRITE_RULE [DISJ_IMP_THM] th')
  end
  val phase2c =
       SIMP_CONV e1_ss ctxt THENC
       ONCE_REWRITE_CONV [memoryTheory.sizeof_cases, memoryTheory.align_cases] THENC
       SIMP_CONV e1_ss ctxt
  fun strip th = let
    fun recurse th = let
      val c = concl th
    in
      if is_imp c then let
          val (ant,con) = dest_imp c
        in
          if is_exists ant then
            recurse (CONV_RULE LEFT_IMP_EXISTS_CONV th)
          else if is_eq ant then let
              val (l0,r0) = dest_eq ant
              val (l,r) = if is_var l0 then (l0,r0) else (r0,l0)
            in
              if not (free_in l r) andalso is_var l then
                recurse (MP (INST [l |-> r] th) (REFL r))
              else if null (free_vars l0) then
                recurse (UNDISCH (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ)) th))
              else recurse (UNDISCH th)
            end
          else if is_conj ant then
            recurse (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) th)
          else recurse (UNDISCH th)
        end
      else if is_forall c then recurse (SPEC_ALL th)
      else th
    end
  in
    recurse th
  end
  fun augment th = List.foldl (fn (cth,th) => ADD_ASSUM (concl cth) th) th ctxt
in
  seq.map (augment o strip o CONV_RULE (LAND_CONV phase2c))
          (seq.fromList (splitup rwt1))
end

fun emeaning_evalstar ctxt edecls state =
    if same_const ``list$NIL : 'a list`` edecls then seq.fromList [[]]
    else let
        val onestep_sq = emeaning_eval1 ctxt edecls state
        fun extract_next th = let
          val c = concl th
        in
          pairSyntax.dest_pair (rand c)
        end
        fun recurse th = let
          val (state', edecls') = extract_next th
          val sq = emeaning_evalstar (map ASSUME (hyp th)) edecls' state'
        in
          seq.map (cons th) sq
        end
      in
        seq.bind onestep_sq recurse
      end

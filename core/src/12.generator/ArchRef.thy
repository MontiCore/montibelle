theory ArchRef

imports "HOL-Eisbach.Eisbach" bundlelocale.SBGen spslocale.WrappedSPSComp spslocale.WrappedSPSCompConvert spslocale.WrappedSPSCompInstanceConvert

begin


method solve_cases uses simps = 
  (solves \<open>(rename_tac c, case_tac c; simp add: simps)\<close>)


method solve_simulation_subproof uses sbGen_axioms buildSB_defs =
  (solves \<open>simp add: sbGen_axioms\<close>,
  solves \<open>simp add: sbGen_axioms\<close>,
  solves \<open>simp add: sbGen_axioms\<close>,
  solves \<open>simp add: sbGen_axioms\<close>,
  solve_cases simps: ctype_def,
  solve_cases simps: ctype_def,
  solves \<open>rename_tac c, case_tac c; auto simp add: buildSB_defs\<close>,
  solves \<open>rename_tac c, case_tac c; auto simp add: buildSB_defs\<close>)

method connector_simulation_proof uses simp_defs con_defs sbGen_axioms buildSB_defs =
  (simp add: simp_defs del: Set.insert_subset,
   (rule equalityD1[OF simulation_connector_eq] |
    rule equalityD2[OF simulation_connector_eq] |
    rule simulation_connector_eq | 
    rule simulation_connector_eq[symmetric]),
   solves \<open>simp add: con_defs\<close>,
   solve_simulation_subproof sbGen_axioms: sbGen_axioms buildSB_defs: buildSB_defs)

method component_simulation_proof uses simp_defs sps_ref con_defs sbGen_axioms buildSB_defs =
  (simp add: simp_defs,
   (subst seqcomp_assoc)+,
   (rule simulation_component_eq | 
    rule simulation_component_eq[symmetric] | 
    rule usimulation_component_refinement[OF sps_ref] | 
    rule u1simulation_component_refinement[OF sps_ref]),
   solves \<open>simp add: con_defs\<close>,
   solves \<open>simp add: con_defs\<close>,
   solve_simulation_subproof sbGen_axioms: sbGen_axioms buildSB_defs: buildSB_defs)


method wrappedSPS_proof uses input_channels_exists =
  ((solve_cases simps: ctype_def),
   (solve_cases simps: ctype_def),
   (solve_cases),
   (solve_cases),
   (solves \<open>simp add: surj_def; rule allI, solve_cases simps: input_channels_exists\<close>))

method wrappedSPSConvert_proof uses input_channels_exists =
  ((wrappedSPS_proof input_channels_exists: input_channels_exists),
   (solve_cases),
   (solve_cases),
   (solve_cases),
   (solves \<open>simp; force\<close>))

method wrappedSPSInstance_proof =
  ((solve_cases),
   (solve_cases),
   (solve_cases),
   (solve_cases))

method solve_decompose uses decompose_lemma = 
  (solves \<open>(rule decompose_lemma; simp only: Pure.triv_forall_equality; solve_decompose decompose_lemma: decompose_lemma) |  solve_cases\<close>)

method wrappedSPSCompNoOverlap_proof =
  ((solves \<open>simp; force\<close>),
   (solves \<open>simp; force\<close>),
   (solve_decompose decompose_lemma: wrappedSPSComp.named_comp_in_well1_decompose),
   (solve_decompose decompose_lemma: wrappedSPSComp.named_comp_in_well2_decompose),
   (solve_decompose decompose_lemma: wrappedSPSComp.named_comp_inverse_decompose),
   (solve_decompose decompose_lemma: wrappedSPSComp.named_comp_in_well1_decompose),
   (solve_decompose decompose_lemma: wrappedSPSComp.named_comp_in_well2_decompose),
   (solve_decompose decompose_lemma: wrappedSPSComp.named_comp_inverse_decompose))

method wrappedSPSCompParallel_proof = 
  ((solves \<open>simp; force\<close>),
   (solves \<open>simp; force\<close>),
   (solves \<open>simp; force\<close>),
   (solves \<open>simp; force\<close>))


method iterate_sps_comp_eq = ((subst wrappedSPSComp.named_sps_comp_eq[symmetric])+)?

method insert_simulation_mappings = (subst wrappedSPSConvert.named_sps_convert_eq[symmetric], iterate_sps_comp_eq)

method insert_instance_simulation_mappings = (subst wrappedSPSInstance.named_sbrenamech_spsconv_swap, iterate_sps_comp_eq)

method compositional_refinement_proof uses refinements = 
  (insert_simulation_mappings, 
   rule spsconvref,
   (rule spscomp_refinement; 
    (assumption | frule refinements | 
     (solves \<open>rule equalityD1, (simp | frule refinements)\<close>) | 
     (solves \<open>rule equalityD2, (simp | frule refinements)\<close>))?)+)

method compositional_equality_proof uses equalities = 
  (insert_simulation_mappings, 
   rule spsconveq,
   (rule spscomp_equality; (assumption | frule equalities | frule equalities[symmetric])?)+)



method unfold_sbrename_comp uses renamings_welldefined =
  (subst spfcomp_unfold,
   ((subst sbunion_getchl, solves \<open>simp\<close>) | (subst sbunion_getchr, solves \<open>simp\<close>)),
   (subst sbrenamech_getch2, solves \<open>simp\<close>, rule renamings_welldefined, 
    subst sbtypecast_getch,
    (((subst sbunion_minus_getchl, solves \<open>simp\<close>) | (subst sbunion_minus_getchr, solves \<open>simp\<close>, solves \<open>simp\<close>)), 
     (subst sbtypecast_getch2, solves \<open>simp\<close>)?
    )+
   )?
  )+

method merge_connectors_proof uses renamings_welldefined =
  (simp add: spscomp_singeltons spsConvert_def spfConvert_def,
   rule cfun_eqI,
   rule sb_eqI,
   (subst sbrenamech_getch, rule renamings_welldefined),
   rename_tac c, case_tac c; 
   simp; 
   solves \<open>unfold_sbrename_comp renamings_welldefined: renamings_welldefined, simp add: sbgetch_insert\<close>)

end

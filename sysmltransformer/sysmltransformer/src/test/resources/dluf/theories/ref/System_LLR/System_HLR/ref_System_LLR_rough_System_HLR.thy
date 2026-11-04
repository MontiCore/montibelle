theory ref_System_LLR_rough_System_HLR
  imports
    (* Core *) generator.ArchRef
    (* Gen  *) sps_System_LLR.def_System_LLR sps_System_HLR.def_System_HLR
               ref_DLUF_LLR_refines_DLUF_HLR1.ref_DLUF_LLR_rough_DLUF_HLR1
    (* Hwl  *)

begin



fun connector_in :: "def_System_LLR_connector_System_LLR_connector_Input.channels \<Rightarrow> def_System_HLR_connector_System_HLR_connector_Input.channels" where
  "connector_in def_System_LLR_connector_System_LLR_connector_Input.channel_dluf_output1_data = def_System_HLR_connector_System_HLR_connector_Input.channel_dluf_output1_data" |
  "connector_in def_System_LLR_connector_System_LLR_connector_Input.channel_dluf_output2_data = def_System_HLR_connector_System_HLR_connector_Input.channel_dluf_output2_data" |
  "connector_in def_System_LLR_connector_System_LLR_connector_Input.channel_dluf_output3_data = def_System_HLR_connector_System_HLR_connector_Input.channel_dluf_output3_data" |
  "connector_in def_System_LLR_connector_System_LLR_connector_Input.channel_dluf_output4_data = def_System_HLR_connector_System_HLR_connector_Input.channel_dluf_output4_data" |
  "connector_in def_System_LLR_connector_System_LLR_connector_Input.channel_mergex_output_data = def_System_HLR_connector_System_HLR_connector_Input.channel_mergex_output_data" |
  "connector_in def_System_LLR_connector_System_LLR_connector_Input.channel_user1_data = def_System_HLR_connector_System_HLR_connector_Input.channel_user1_data" |
  "connector_in def_System_LLR_connector_System_LLR_connector_Input.channel_user2_data = def_System_HLR_connector_System_HLR_connector_Input.channel_user2_data" |
  "connector_in def_System_LLR_connector_System_LLR_connector_Input.channel_user3_data = def_System_HLR_connector_System_HLR_connector_Input.channel_user3_data" |
  "connector_in def_System_LLR_connector_System_LLR_connector_Input.channel_user4_data = def_System_HLR_connector_System_HLR_connector_Input.channel_user4_data"

fun connector_out :: "def_System_HLR_connector_System_HLR_connector_Output.channels \<Rightarrow> def_System_LLR_connector_System_LLR_connector_Output.channels" where
  "connector_out def_System_HLR_connector_System_HLR_connector_Output.channel_dluf_input1_data = def_System_LLR_connector_System_LLR_connector_Output.channel_dluf_input1_data" |
  "connector_out def_System_HLR_connector_System_HLR_connector_Output.channel_dluf_input2_data = def_System_LLR_connector_System_LLR_connector_Output.channel_dluf_input2_data" |
  "connector_out def_System_HLR_connector_System_HLR_connector_Output.channel_dluf_input3_data = def_System_LLR_connector_System_LLR_connector_Output.channel_dluf_input3_data" |
  "connector_out def_System_HLR_connector_System_HLR_connector_Output.channel_dluf_input4_data = def_System_LLR_connector_System_LLR_connector_Output.channel_dluf_input4_data" |
  "connector_out def_System_HLR_connector_System_HLR_connector_Output.channel_link_data = def_System_LLR_connector_System_LLR_connector_Output.channel_link_data" |
  "connector_out def_System_HLR_connector_System_HLR_connector_Output.channel_mergex_input1_data = def_System_LLR_connector_System_LLR_connector_Output.channel_mergex_input1_data" |
  "connector_out def_System_HLR_connector_System_HLR_connector_Output.channel_mergex_input2_data = def_System_LLR_connector_System_LLR_connector_Output.channel_mergex_input2_data" |
  "connector_out def_System_HLR_connector_System_HLR_connector_Output.channel_mergex_input3_data = def_System_LLR_connector_System_LLR_connector_Output.channel_mergex_input3_data" |
  "connector_out def_System_HLR_connector_System_HLR_connector_Output.channel_mergex_input4_data = def_System_LLR_connector_System_LLR_connector_Output.channel_mergex_input4_data"


fun dluf_in :: "def_System_LLR_dluf_Input.channels \<Rightarrow> def_System_HLR_dluf_Input.channels" where
  "dluf_in def_System_LLR_dluf_Input.channel_dluf_input1_data = def_System_HLR_dluf_Input.channel_dluf_input1_data" |
  "dluf_in def_System_LLR_dluf_Input.channel_dluf_input2_data = def_System_HLR_dluf_Input.channel_dluf_input2_data" |
  "dluf_in def_System_LLR_dluf_Input.channel_dluf_input3_data = def_System_HLR_dluf_Input.channel_dluf_input3_data" |
  "dluf_in def_System_LLR_dluf_Input.channel_dluf_input4_data = def_System_HLR_dluf_Input.channel_dluf_input4_data"

fun dluf_out :: "def_System_HLR_dluf_Output.channels \<Rightarrow> def_System_LLR_dluf_Output.channels" where
  "dluf_out def_System_HLR_dluf_Output.channel_dluf_output1_data = def_System_LLR_dluf_Output.channel_dluf_output1_data" |
  "dluf_out def_System_HLR_dluf_Output.channel_dluf_output2_data = def_System_LLR_dluf_Output.channel_dluf_output2_data" |
  "dluf_out def_System_HLR_dluf_Output.channel_dluf_output3_data = def_System_LLR_dluf_Output.channel_dluf_output3_data" |
  "dluf_out def_System_HLR_dluf_Output.channel_dluf_output4_data = def_System_LLR_dluf_Output.channel_dluf_output4_data"


fun mergex_in :: "def_System_LLR_mergex_Input.channels \<Rightarrow> def_System_HLR_mergex_Input.channels" where
  "mergex_in def_System_LLR_mergex_Input.channel_mergex_input1_data = def_System_HLR_mergex_Input.channel_mergex_input1_data" |
  "mergex_in def_System_LLR_mergex_Input.channel_mergex_input2_data = def_System_HLR_mergex_Input.channel_mergex_input2_data" |
  "mergex_in def_System_LLR_mergex_Input.channel_mergex_input3_data = def_System_HLR_mergex_Input.channel_mergex_input3_data" |
  "mergex_in def_System_LLR_mergex_Input.channel_mergex_input4_data = def_System_HLR_mergex_Input.channel_mergex_input4_data"

fun mergex_out :: "def_System_HLR_mergex_Output.channels \<Rightarrow> def_System_LLR_mergex_Output.channels" where
  "mergex_out def_System_HLR_mergex_Output.channel_mergex_output_data = def_System_LLR_mergex_Output.channel_mergex_output_data"


(* refinement *)

lemma refinement_withAssms:
assumes "\<And> var_cap1 var_cap2 var_cap3 var_cap4. def_DLUF_LLR.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<subseteq> def_DLUF_HLR1.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
    and "def_Merge_LLR.Sps () \<subseteq> def_Merge_LLR.Sps ()"
  shows "def_System_LLR.Sps () \<subseteq> def_System_HLR.Sps ()"
proof -

  interpret step1: wrappedSPSCompParallelConvert
  dluf_in
  dluf_out
  mergex_in
  mergex_out
  "TYPE(def_System_HLR_Input.channels)"
  "TYPE(def_System_HLR_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_System_LLR_dluf_Input.channels_exists)
    apply(wrappedSPSConvert_proof input_channels_exists: def_System_LLR_mergex_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step2: wrappedSPSCompNoOverlapConvert
  connector_in
  connector_out
  step1.comp_in
  step1.comp_out
  "TYPE(def_System_HLR_Input.channels)"
  "TYPE(def_System_HLR_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_System_LLR_connector_System_LLR_connector_Input.channels_exists)
    by(wrappedSPSCompNoOverlap_proof)


  have "{sbRenameCh connector_in} \<then> def_System_LLR_connector.Sps () \<then> {sbRenameCh connector_out} \<subseteq> def_System_HLR_connector.Sps ()"
    by (connector_simulation_proof simp_defs: def_System_LLR_connector.Sps_def
                                              def_System_LLR_connector_System_LLR_connector_Input.sbgetter_def
                                              def_System_LLR_connector_System_LLR_connector_Output.sbsetter_def
                                              def_System_HLR_connector.Sps_def
                                              def_System_HLR_connector_System_HLR_connector_Input.sbgetter_def
                                              def_System_HLR_connector_System_HLR_connector_Output.sbsetter_def
                                    con_defs: def_System_LLR_connector.connector_def
                                              def_System_HLR_connector.connector_def
                                sbGen_axioms: def_System_LLR_connector_System_LLR_connector_Input.SB.sbGen_axioms
                                              def_System_LLR_connector_System_LLR_connector_Output.SB.sbGen_axioms
                                              def_System_HLR_connector_System_HLR_connector_Input.SB.sbGen_axioms
                                              def_System_HLR_connector_System_HLR_connector_Output.SB.sbGen_axioms
                                buildSB_defs: def_System_LLR_connector_System_LLR_connector_Input.buildSB_def
                                              def_System_LLR_connector_System_LLR_connector_Output.buildSB_def
                                              def_System_HLR_connector_System_HLR_connector_Input.buildSB_def
                                              def_System_HLR_connector_System_HLR_connector_Output.buildSB_def)

  moreover have "{sbRenameCh dluf_in} \<then> def_System_LLR_dluf.Sps () \<then> {sbRenameCh dluf_out} \<subseteq> def_System_HLR_dluf.Sps ()"
    by (component_simulation_proof sps_ref: assms(1)
                                 simp_defs: def_System_LLR_dluf.Sps_def
                                            def_System_LLR_dluf_InputMap.Sps_def
                                            def_System_LLR_dluf_OutputMap.Sps_def
                                            def_System_LLR_dluf_Input.sbgetter_def
                                            def_System_LLR_dluf_Output.sbsetter_def
                                            def_System_HLR_dluf.Sps_def
                                            def_System_HLR_dluf_InputMap.Sps_def
                                            def_System_HLR_dluf_OutputMap.Sps_def
                                            def_System_HLR_dluf_Input.sbgetter_def
                                            def_System_HLR_dluf_Output.sbsetter_def
                                  con_defs: def_System_LLR_dluf_InputMap.connector_def
                                            def_System_HLR_dluf_InputMap.connector_def
                                            def_System_LLR_dluf_OutputMap.connector_def
                                            def_System_HLR_dluf_OutputMap.connector_def
                              sbGen_axioms: def_System_LLR_dluf_Input.SB.sbGen_axioms
                                            def_System_LLR_dluf_Output.SB.sbGen_axioms
                                            def_System_HLR_dluf_Input.SB.sbGen_axioms
                                            def_System_HLR_dluf_Output.SB.sbGen_axioms
                              buildSB_defs: def_System_LLR_dluf_Input.buildSB_def
                                            def_System_LLR_dluf_Output.buildSB_def
                                            def_System_HLR_dluf_Input.buildSB_def
                                            def_System_HLR_dluf_Output.buildSB_def)

  moreover have "{sbRenameCh mergex_in} \<then> def_System_LLR_mergex.Sps () \<then> {sbRenameCh mergex_out} \<subseteq> def_System_HLR_mergex.Sps ()"
    by (component_simulation_proof sps_ref: assms(2)
                                 simp_defs: def_System_LLR_mergex.Sps_def
                                            def_System_LLR_mergex_InputMap.Sps_def
                                            def_System_LLR_mergex_OutputMap.Sps_def
                                            def_System_LLR_mergex_Input.sbgetter_def
                                            def_System_LLR_mergex_Output.sbsetter_def
                                            def_System_HLR_mergex.Sps_def
                                            def_System_HLR_mergex_InputMap.Sps_def
                                            def_System_HLR_mergex_OutputMap.Sps_def
                                            def_System_HLR_mergex_Input.sbgetter_def
                                            def_System_HLR_mergex_Output.sbsetter_def
                                  con_defs: def_System_LLR_mergex_InputMap.connector_def
                                            def_System_HLR_mergex_InputMap.connector_def
                                            def_System_LLR_mergex_OutputMap.connector_def
                                            def_System_HLR_mergex_OutputMap.connector_def
                              sbGen_axioms: def_System_LLR_mergex_Input.SB.sbGen_axioms
                                            def_System_LLR_mergex_Output.SB.sbGen_axioms
                                            def_System_HLR_mergex_Input.SB.sbGen_axioms
                                            def_System_HLR_mergex_Output.SB.sbGen_axioms
                              buildSB_defs: def_System_LLR_mergex_Input.buildSB_def
                                            def_System_LLR_mergex_Output.buildSB_def
                                            def_System_HLR_mergex_Input.buildSB_def
                                            def_System_HLR_mergex_Output.buildSB_def)

  ultimately show ?thesis
    apply(simp add: def_System_LLR.Sps_def def_System_LLR.rawSps_def
                    def_System_HLR.Sps_def def_System_HLR.rawSps_def)
    by(compositional_refinement_proof)?
qed

lemma refinement[simp]: "def_System_LLR.Sps () \<subseteq> def_System_HLR.Sps ()"
  using refinement_withAssms
  (* autosledgi *) oops


end

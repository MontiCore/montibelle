theory ref_Scheduler_LLR_rough_Scheduler_HLR3
  imports
    (* Core *) generator.ArchRef
    (* Gen  *) sps_Scheduler_LLR.def_Scheduler_LLR sps_Scheduler_HLR3.def_Scheduler_HLR3
               ref_Buffer_LLR_refines_Buffer_HLR3.ref_Queue_LLR_rough_Queue_HLR3
               ref_Capacity_LLR_refines_Capacity_HLR3.ref_RateLimiter_LLR_rough_RateLimiter_HLR3
    (* Hwl  *)

begin



fun connector_in :: "def_Scheduler_LLR_connector_Scheduler_LLR_connector_Input.channels \<Rightarrow> def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.channels" where
  "connector_in def_Scheduler_LLR_connector_Scheduler_LLR_connector_Input.channel_buffer_output_data = def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.channel_buffer_output_data" |
  "connector_in def_Scheduler_LLR_connector_Scheduler_LLR_connector_Input.channel_capacity_control_data = def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.channel_capacity_control_data" |
  "connector_in def_Scheduler_LLR_connector_Scheduler_LLR_connector_Input.channel_capacity_output_data = def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.channel_capacity_output_data" |
  "connector_in def_Scheduler_LLR_connector_Scheduler_LLR_connector_Input.channel_input_data = def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.channel_input_data"

fun connector_out :: "def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channels \<Rightarrow> def_Scheduler_LLR_connector_Scheduler_LLR_connector_Output.channels" where
  "connector_out def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channel_buffer_control_data = def_Scheduler_LLR_connector_Scheduler_LLR_connector_Output.channel_buffer_control_data" |
  "connector_out def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channel_buffer_input_data = def_Scheduler_LLR_connector_Scheduler_LLR_connector_Output.channel_buffer_input_data" |
  "connector_out def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channel_capacity_input_data = def_Scheduler_LLR_connector_Scheduler_LLR_connector_Output.channel_capacity_input_data" |
  "connector_out def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channel_output_data = def_Scheduler_LLR_connector_Scheduler_LLR_connector_Output.channel_output_data"


fun buffer_in :: "def_Scheduler_LLR_buffer_Input.channels \<Rightarrow> def_Scheduler_HLR3_buffer_Input.channels" where
  "buffer_in def_Scheduler_LLR_buffer_Input.channel_buffer_control_data = def_Scheduler_HLR3_buffer_Input.channel_buffer_control_data" |
  "buffer_in def_Scheduler_LLR_buffer_Input.channel_buffer_input_data = def_Scheduler_HLR3_buffer_Input.channel_buffer_input_data"

fun buffer_out :: "def_Scheduler_HLR3_buffer_Output.channels \<Rightarrow> def_Scheduler_LLR_buffer_Output.channels" where
  "buffer_out def_Scheduler_HLR3_buffer_Output.channel_buffer_output_data = def_Scheduler_LLR_buffer_Output.channel_buffer_output_data"


fun capacity_in :: "def_Scheduler_LLR_capacity_Input.channels \<Rightarrow> def_Scheduler_HLR3_capacity_Input.channels" where
  "capacity_in def_Scheduler_LLR_capacity_Input.channel_capacity_input_data = def_Scheduler_HLR3_capacity_Input.channel_capacity_input_data"

fun capacity_out :: "def_Scheduler_HLR3_capacity_Output.channels \<Rightarrow> def_Scheduler_LLR_capacity_Output.channels" where
  "capacity_out def_Scheduler_HLR3_capacity_Output.channel_capacity_control_data = def_Scheduler_LLR_capacity_Output.channel_capacity_control_data" |
  "capacity_out def_Scheduler_HLR3_capacity_Output.channel_capacity_output_data = def_Scheduler_LLR_capacity_Output.channel_capacity_output_data"


(* refinement *)

lemma refinement_withAssms:
assumes "def_Buffer_LLR.Sps () \<subseteq> def_Buffer_HLR3.Sps ()"
    and "\<And> var_cap. def_Capacity_LLR.Sps (var_cap) \<subseteq> def_Capacity_HLR3.Sps (var_cap)"
  shows "def_Scheduler_LLR.Sps (var_capacity) \<subseteq> def_Scheduler_HLR3.Sps (var_capacity)"
proof -

  interpret step1: wrappedSPSCompParallelConvert
  buffer_in
  buffer_out
  capacity_in
  capacity_out
  "TYPE(def_Scheduler_HLR2_Input.channels)"
  "TYPE(def_Scheduler_HLR2_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_Scheduler_LLR_buffer_Input.channels_exists)
    apply(wrappedSPSConvert_proof input_channels_exists: def_Scheduler_LLR_capacity_Input.channels_exists)
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
  "TYPE(def_Scheduler_HLR2_Input.channels)"
  "TYPE(def_Scheduler_HLR2_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_Scheduler_LLR_connector_Scheduler_LLR_connector_Input.channels_exists)
    by(wrappedSPSCompNoOverlap_proof)


  have "{sbRenameCh connector_in} \<then> def_Scheduler_LLR_connector.Sps () \<then> {sbRenameCh connector_out} \<subseteq> def_Scheduler_HLR3_connector.Sps ()"
    by (connector_simulation_proof simp_defs: def_Scheduler_LLR_connector.Sps_def
                                              def_Scheduler_LLR_connector_Scheduler_LLR_connector_Input.sbgetter_def
                                              def_Scheduler_LLR_connector_Scheduler_LLR_connector_Output.sbsetter_def
                                              def_Scheduler_HLR3_connector.Sps_def
                                              def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.sbgetter_def
                                              def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.sbsetter_def
                                    con_defs: def_Scheduler_LLR_connector.connector_def
                                              def_Scheduler_HLR3_connector.connector_def
                                sbGen_axioms: def_Scheduler_LLR_connector_Scheduler_LLR_connector_Input.SB.sbGen_axioms
                                              def_Scheduler_LLR_connector_Scheduler_LLR_connector_Output.SB.sbGen_axioms
                                              def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.SB.sbGen_axioms
                                              def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.SB.sbGen_axioms
                                buildSB_defs: def_Scheduler_LLR_connector_Scheduler_LLR_connector_Input.buildSB_def
                                              def_Scheduler_LLR_connector_Scheduler_LLR_connector_Output.buildSB_def
                                              def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.buildSB_def
                                              def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.buildSB_def)

  moreover have "\<And> var_capacity. {sbRenameCh buffer_in} \<then> def_Scheduler_LLR_buffer.Sps (var_capacity) \<then> {sbRenameCh buffer_out} \<subseteq> def_Scheduler_HLR3_buffer.Sps (var_capacity)"
    by (component_simulation_proof sps_ref: assms(1)
                                 simp_defs: def_Scheduler_LLR_buffer.Sps_def
                                            def_Scheduler_LLR_buffer_InputMap.Sps_def
                                            def_Scheduler_LLR_buffer_OutputMap.Sps_def
                                            def_Scheduler_LLR_buffer_Input.sbgetter_def
                                            def_Scheduler_LLR_buffer_Output.sbsetter_def
                                            def_Scheduler_HLR3_buffer.Sps_def
                                            def_Scheduler_HLR3_buffer_InputMap.Sps_def
                                            def_Scheduler_HLR3_buffer_OutputMap.Sps_def
                                            def_Scheduler_HLR3_buffer_Input.sbgetter_def
                                            def_Scheduler_HLR3_buffer_Output.sbsetter_def
                                  con_defs: def_Scheduler_LLR_buffer_InputMap.connector_def
                                            def_Scheduler_HLR3_buffer_InputMap.connector_def
                                            def_Scheduler_LLR_buffer_OutputMap.connector_def
                                            def_Scheduler_HLR3_buffer_OutputMap.connector_def
                              sbGen_axioms: def_Scheduler_LLR_buffer_Input.SB.sbGen_axioms
                                            def_Scheduler_LLR_buffer_Output.SB.sbGen_axioms
                                            def_Scheduler_HLR3_buffer_Input.SB.sbGen_axioms
                                            def_Scheduler_HLR3_buffer_Output.SB.sbGen_axioms
                              buildSB_defs: def_Scheduler_LLR_buffer_Input.buildSB_def
                                            def_Scheduler_LLR_buffer_Output.buildSB_def
                                            def_Scheduler_HLR3_buffer_Input.buildSB_def
                                            def_Scheduler_HLR3_buffer_Output.buildSB_def)

  moreover have "\<And> var_capacity. {sbRenameCh capacity_in} \<then> def_Scheduler_LLR_capacity.Sps (var_capacity) \<then> {sbRenameCh capacity_out} \<subseteq> def_Scheduler_HLR3_capacity.Sps (var_capacity)"
    by (component_simulation_proof sps_ref: assms(2)
                                 simp_defs: def_Scheduler_LLR_capacity.Sps_def
                                            def_Scheduler_LLR_capacity_InputMap.Sps_def
                                            def_Scheduler_LLR_capacity_OutputMap.Sps_def
                                            def_Scheduler_LLR_capacity_Input.sbgetter_def
                                            def_Scheduler_LLR_capacity_Output.sbsetter_def
                                            def_Scheduler_HLR3_capacity.Sps_def
                                            def_Scheduler_HLR3_capacity_InputMap.Sps_def
                                            def_Scheduler_HLR3_capacity_OutputMap.Sps_def
                                            def_Scheduler_HLR3_capacity_Input.sbgetter_def
                                            def_Scheduler_HLR3_capacity_Output.sbsetter_def
                                  con_defs: def_Scheduler_LLR_capacity_InputMap.connector_def
                                            def_Scheduler_HLR3_capacity_InputMap.connector_def
                                            def_Scheduler_LLR_capacity_OutputMap.connector_def
                                            def_Scheduler_HLR3_capacity_OutputMap.connector_def
                              sbGen_axioms: def_Scheduler_LLR_capacity_Input.SB.sbGen_axioms
                                            def_Scheduler_LLR_capacity_Output.SB.sbGen_axioms
                                            def_Scheduler_HLR3_capacity_Input.SB.sbGen_axioms
                                            def_Scheduler_HLR3_capacity_Output.SB.sbGen_axioms
                              buildSB_defs: def_Scheduler_LLR_capacity_Input.buildSB_def
                                            def_Scheduler_LLR_capacity_Output.buildSB_def
                                            def_Scheduler_HLR3_capacity_Input.buildSB_def
                                            def_Scheduler_HLR3_capacity_Output.buildSB_def)

  ultimately show ?thesis
    apply(simp add: def_Scheduler_LLR.Sps_def def_Scheduler_LLR.rawSps_def
                    def_Scheduler_HLR3.Sps_def def_Scheduler_HLR3.rawSps_def)
    by(compositional_refinement_proof)?
qed

lemma refinement[simp]: "def_Scheduler_LLR.Sps (var_capacity) \<subseteq> def_Scheduler_HLR3.Sps (var_capacity)"
  using refinement_withAssms
  (* autosledgi *) oops


end

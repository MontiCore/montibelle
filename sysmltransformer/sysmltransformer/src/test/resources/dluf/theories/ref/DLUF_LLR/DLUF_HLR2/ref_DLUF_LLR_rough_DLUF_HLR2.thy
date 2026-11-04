theory ref_DLUF_LLR_rough_DLUF_HLR2
  imports
    (* Core *) generator.ArchRef
    (* Gen  *) sps_DLUF_LLR.def_DLUF_LLR sps_DLUF_HLR2.def_DLUF_HLR2
               ref_Scheduler_LLR_refines_Scheduler_HLR2.ref_Scheduler_LLR_rough_Scheduler_HLR2
    (* Hwl  *)

begin



fun connector_in :: "def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channels \<Rightarrow> def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channels" where
  "connector_in def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channel_input1_data = def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channel_input1_data" |
  "connector_in def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channel_input2_data = def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channel_input2_data" |
  "connector_in def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channel_input3_data = def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channel_input3_data" |
  "connector_in def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channel_input4_data = def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channel_input4_data" |
  "connector_in def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channel_scheduler1_output_data = def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channel_scheduler1_output_data" |
  "connector_in def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channel_scheduler2_output_data = def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channel_scheduler2_output_data" |
  "connector_in def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channel_scheduler3_output_data = def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channel_scheduler3_output_data" |
  "connector_in def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channel_scheduler4_output_data = def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channel_scheduler4_output_data"

fun connector_out :: "def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.channels \<Rightarrow> def_DLUF_LLR_connector_DLUF_LLR_connector_Output.channels" where
  "connector_out def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.channel_output1_data = def_DLUF_LLR_connector_DLUF_LLR_connector_Output.channel_output1_data" |
  "connector_out def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.channel_output2_data = def_DLUF_LLR_connector_DLUF_LLR_connector_Output.channel_output2_data" |
  "connector_out def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.channel_output3_data = def_DLUF_LLR_connector_DLUF_LLR_connector_Output.channel_output3_data" |
  "connector_out def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.channel_output4_data = def_DLUF_LLR_connector_DLUF_LLR_connector_Output.channel_output4_data" |
  "connector_out def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.channel_scheduler1_input_data = def_DLUF_LLR_connector_DLUF_LLR_connector_Output.channel_scheduler1_input_data" |
  "connector_out def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.channel_scheduler2_input_data = def_DLUF_LLR_connector_DLUF_LLR_connector_Output.channel_scheduler2_input_data" |
  "connector_out def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.channel_scheduler3_input_data = def_DLUF_LLR_connector_DLUF_LLR_connector_Output.channel_scheduler3_input_data" |
  "connector_out def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.channel_scheduler4_input_data = def_DLUF_LLR_connector_DLUF_LLR_connector_Output.channel_scheduler4_input_data"


fun scheduler1_in :: "def_DLUF_LLR_scheduler1_Input.channels \<Rightarrow> def_DLUF_HLR2_scheduler1_Input.channels" where
  "scheduler1_in def_DLUF_LLR_scheduler1_Input.channel_scheduler1_input_data = def_DLUF_HLR2_scheduler1_Input.channel_scheduler1_input_data"

fun scheduler1_out :: "def_DLUF_HLR2_scheduler1_Output.channels \<Rightarrow> def_DLUF_LLR_scheduler1_Output.channels" where
  "scheduler1_out def_DLUF_HLR2_scheduler1_Output.channel_scheduler1_output_data = def_DLUF_LLR_scheduler1_Output.channel_scheduler1_output_data"


fun scheduler2_in :: "def_DLUF_LLR_scheduler2_Input.channels \<Rightarrow> def_DLUF_HLR2_scheduler2_Input.channels" where
  "scheduler2_in def_DLUF_LLR_scheduler2_Input.channel_scheduler2_input_data = def_DLUF_HLR2_scheduler2_Input.channel_scheduler2_input_data"

fun scheduler2_out :: "def_DLUF_HLR2_scheduler2_Output.channels \<Rightarrow> def_DLUF_LLR_scheduler2_Output.channels" where
  "scheduler2_out def_DLUF_HLR2_scheduler2_Output.channel_scheduler2_output_data = def_DLUF_LLR_scheduler2_Output.channel_scheduler2_output_data"


fun scheduler3_in :: "def_DLUF_LLR_scheduler3_Input.channels \<Rightarrow> def_DLUF_HLR2_scheduler3_Input.channels" where
  "scheduler3_in def_DLUF_LLR_scheduler3_Input.channel_scheduler3_input_data = def_DLUF_HLR2_scheduler3_Input.channel_scheduler3_input_data"

fun scheduler3_out :: "def_DLUF_HLR2_scheduler3_Output.channels \<Rightarrow> def_DLUF_LLR_scheduler3_Output.channels" where
  "scheduler3_out def_DLUF_HLR2_scheduler3_Output.channel_scheduler3_output_data = def_DLUF_LLR_scheduler3_Output.channel_scheduler3_output_data"


fun scheduler4_in :: "def_DLUF_LLR_scheduler4_Input.channels \<Rightarrow> def_DLUF_HLR2_scheduler4_Input.channels" where
  "scheduler4_in def_DLUF_LLR_scheduler4_Input.channel_scheduler4_input_data = def_DLUF_HLR2_scheduler4_Input.channel_scheduler4_input_data"

fun scheduler4_out :: "def_DLUF_HLR2_scheduler4_Output.channels \<Rightarrow> def_DLUF_LLR_scheduler4_Output.channels" where
  "scheduler4_out def_DLUF_HLR2_scheduler4_Output.channel_scheduler4_output_data = def_DLUF_LLR_scheduler4_Output.channel_scheduler4_output_data"


(* refinement *)

lemma refinement_withAssms:
assumes "\<And> var_capacity. def_Scheduler_LLR.Sps (var_capacity) \<subseteq> def_Scheduler_HLR2.Sps (var_capacity)"
    and "\<And> var_capacity. def_Scheduler_LLR.Sps (var_capacity) \<subseteq> def_Scheduler_HLR2.Sps (var_capacity)"
    and "\<And> var_capacity. def_Scheduler_LLR.Sps (var_capacity) \<subseteq> def_Scheduler_HLR2.Sps (var_capacity)"
    and "\<And> var_capacity. def_Scheduler_LLR.Sps (var_capacity) \<subseteq> def_Scheduler_HLR2.Sps (var_capacity)"
  shows "def_DLUF_LLR.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<subseteq> def_DLUF_HLR2.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
proof -

  interpret step1: wrappedSPSCompParallelConvert
  scheduler3_in
  scheduler3_out
  scheduler4_in
  scheduler4_out
  "TYPE(def_DLUF_HLR1_Input.channels)"
  "TYPE(def_DLUF_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_DLUF_LLR_scheduler3_Input.channels_exists)
    apply(wrappedSPSConvert_proof input_channels_exists: def_DLUF_LLR_scheduler4_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step2: wrappedSPSCompParallelConvert
  scheduler2_in
  scheduler2_out
  step1.comp_in
  step1.comp_out
  "TYPE(def_DLUF_HLR1_Input.channels)"
  "TYPE(def_DLUF_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_DLUF_LLR_scheduler2_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step3: wrappedSPSCompParallelConvert
  scheduler1_in
  scheduler1_out
  step2.comp_in
  step2.comp_out
  "TYPE(def_DLUF_HLR1_Input.channels)"
  "TYPE(def_DLUF_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_DLUF_LLR_scheduler1_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step4: wrappedSPSCompNoOverlapConvert
  connector_in
  connector_out
  step3.comp_in
  step3.comp_out
  "TYPE(def_DLUF_HLR1_Input.channels)"
  "TYPE(def_DLUF_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_DLUF_LLR_connector_DLUF_LLR_connector_Input.channels_exists)
    by(wrappedSPSCompNoOverlap_proof)


  have "{sbRenameCh connector_in} \<then> def_DLUF_LLR_connector.Sps () \<then> {sbRenameCh connector_out} \<subseteq> def_DLUF_HLR2_connector.Sps ()"
    by (connector_simulation_proof simp_defs: def_DLUF_LLR_connector.Sps_def
                                              def_DLUF_LLR_connector_DLUF_LLR_connector_Input.sbgetter_def
                                              def_DLUF_LLR_connector_DLUF_LLR_connector_Output.sbsetter_def
                                              def_DLUF_HLR2_connector.Sps_def
                                              def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.sbgetter_def
                                              def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.sbsetter_def
                                    con_defs: def_DLUF_LLR_connector.connector_def
                                              def_DLUF_HLR2_connector.connector_def
                                sbGen_axioms: def_DLUF_LLR_connector_DLUF_LLR_connector_Input.SB.sbGen_axioms
                                              def_DLUF_LLR_connector_DLUF_LLR_connector_Output.SB.sbGen_axioms
                                              def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.SB.sbGen_axioms
                                              def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.SB.sbGen_axioms
                                buildSB_defs: def_DLUF_LLR_connector_DLUF_LLR_connector_Input.buildSB_def
                                              def_DLUF_LLR_connector_DLUF_LLR_connector_Output.buildSB_def
                                              def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.buildSB_def
                                              def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.buildSB_def)

  moreover have "\<And> var_cap1 var_cap2 var_cap3 var_cap4. {sbRenameCh scheduler1_in} \<then> def_DLUF_LLR_scheduler1.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<then> {sbRenameCh scheduler1_out} \<subseteq> def_DLUF_HLR2_scheduler1.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
    by (component_simulation_proof sps_ref: assms(1)
                                 simp_defs: def_DLUF_LLR_scheduler1.Sps_def
                                            def_DLUF_LLR_scheduler1_InputMap.Sps_def
                                            def_DLUF_LLR_scheduler1_OutputMap.Sps_def
                                            def_DLUF_LLR_scheduler1_Input.sbgetter_def
                                            def_DLUF_LLR_scheduler1_Output.sbsetter_def
                                            def_DLUF_HLR2_scheduler1.Sps_def
                                            def_DLUF_HLR2_scheduler1_InputMap.Sps_def
                                            def_DLUF_HLR2_scheduler1_OutputMap.Sps_def
                                            def_DLUF_HLR2_scheduler1_Input.sbgetter_def
                                            def_DLUF_HLR2_scheduler1_Output.sbsetter_def
                                  con_defs: def_DLUF_LLR_scheduler1_InputMap.connector_def
                                            def_DLUF_HLR2_scheduler1_InputMap.connector_def
                                            def_DLUF_LLR_scheduler1_OutputMap.connector_def
                                            def_DLUF_HLR2_scheduler1_OutputMap.connector_def
                              sbGen_axioms: def_DLUF_LLR_scheduler1_Input.SB.sbGen_axioms
                                            def_DLUF_LLR_scheduler1_Output.SB.sbGen_axioms
                                            def_DLUF_HLR2_scheduler1_Input.SB.sbGen_axioms
                                            def_DLUF_HLR2_scheduler1_Output.SB.sbGen_axioms
                              buildSB_defs: def_DLUF_LLR_scheduler1_Input.buildSB_def
                                            def_DLUF_LLR_scheduler1_Output.buildSB_def
                                            def_DLUF_HLR2_scheduler1_Input.buildSB_def
                                            def_DLUF_HLR2_scheduler1_Output.buildSB_def)

  moreover have "\<And> var_cap1 var_cap2 var_cap3 var_cap4. {sbRenameCh scheduler2_in} \<then> def_DLUF_LLR_scheduler2.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<then> {sbRenameCh scheduler2_out} \<subseteq> def_DLUF_HLR2_scheduler2.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
    by (component_simulation_proof sps_ref: assms(2)
                                 simp_defs: def_DLUF_LLR_scheduler2.Sps_def
                                            def_DLUF_LLR_scheduler2_InputMap.Sps_def
                                            def_DLUF_LLR_scheduler2_OutputMap.Sps_def
                                            def_DLUF_LLR_scheduler2_Input.sbgetter_def
                                            def_DLUF_LLR_scheduler2_Output.sbsetter_def
                                            def_DLUF_HLR2_scheduler2.Sps_def
                                            def_DLUF_HLR2_scheduler2_InputMap.Sps_def
                                            def_DLUF_HLR2_scheduler2_OutputMap.Sps_def
                                            def_DLUF_HLR2_scheduler2_Input.sbgetter_def
                                            def_DLUF_HLR2_scheduler2_Output.sbsetter_def
                                  con_defs: def_DLUF_LLR_scheduler2_InputMap.connector_def
                                            def_DLUF_HLR2_scheduler2_InputMap.connector_def
                                            def_DLUF_LLR_scheduler2_OutputMap.connector_def
                                            def_DLUF_HLR2_scheduler2_OutputMap.connector_def
                              sbGen_axioms: def_DLUF_LLR_scheduler2_Input.SB.sbGen_axioms
                                            def_DLUF_LLR_scheduler2_Output.SB.sbGen_axioms
                                            def_DLUF_HLR2_scheduler2_Input.SB.sbGen_axioms
                                            def_DLUF_HLR2_scheduler2_Output.SB.sbGen_axioms
                              buildSB_defs: def_DLUF_LLR_scheduler2_Input.buildSB_def
                                            def_DLUF_LLR_scheduler2_Output.buildSB_def
                                            def_DLUF_HLR2_scheduler2_Input.buildSB_def
                                            def_DLUF_HLR2_scheduler2_Output.buildSB_def)

  moreover have "\<And> var_cap1 var_cap2 var_cap3 var_cap4. {sbRenameCh scheduler3_in} \<then> def_DLUF_LLR_scheduler3.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<then> {sbRenameCh scheduler3_out} \<subseteq> def_DLUF_HLR2_scheduler3.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
    by (component_simulation_proof sps_ref: assms(3)
                                 simp_defs: def_DLUF_LLR_scheduler3.Sps_def
                                            def_DLUF_LLR_scheduler3_InputMap.Sps_def
                                            def_DLUF_LLR_scheduler3_OutputMap.Sps_def
                                            def_DLUF_LLR_scheduler3_Input.sbgetter_def
                                            def_DLUF_LLR_scheduler3_Output.sbsetter_def
                                            def_DLUF_HLR2_scheduler3.Sps_def
                                            def_DLUF_HLR2_scheduler3_InputMap.Sps_def
                                            def_DLUF_HLR2_scheduler3_OutputMap.Sps_def
                                            def_DLUF_HLR2_scheduler3_Input.sbgetter_def
                                            def_DLUF_HLR2_scheduler3_Output.sbsetter_def
                                  con_defs: def_DLUF_LLR_scheduler3_InputMap.connector_def
                                            def_DLUF_HLR2_scheduler3_InputMap.connector_def
                                            def_DLUF_LLR_scheduler3_OutputMap.connector_def
                                            def_DLUF_HLR2_scheduler3_OutputMap.connector_def
                              sbGen_axioms: def_DLUF_LLR_scheduler3_Input.SB.sbGen_axioms
                                            def_DLUF_LLR_scheduler3_Output.SB.sbGen_axioms
                                            def_DLUF_HLR2_scheduler3_Input.SB.sbGen_axioms
                                            def_DLUF_HLR2_scheduler3_Output.SB.sbGen_axioms
                              buildSB_defs: def_DLUF_LLR_scheduler3_Input.buildSB_def
                                            def_DLUF_LLR_scheduler3_Output.buildSB_def
                                            def_DLUF_HLR2_scheduler3_Input.buildSB_def
                                            def_DLUF_HLR2_scheduler3_Output.buildSB_def)

  moreover have "\<And> var_cap1 var_cap2 var_cap3 var_cap4. {sbRenameCh scheduler4_in} \<then> def_DLUF_LLR_scheduler4.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<then> {sbRenameCh scheduler4_out} \<subseteq> def_DLUF_HLR2_scheduler4.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
    by (component_simulation_proof sps_ref: assms(4)
                                 simp_defs: def_DLUF_LLR_scheduler4.Sps_def
                                            def_DLUF_LLR_scheduler4_InputMap.Sps_def
                                            def_DLUF_LLR_scheduler4_OutputMap.Sps_def
                                            def_DLUF_LLR_scheduler4_Input.sbgetter_def
                                            def_DLUF_LLR_scheduler4_Output.sbsetter_def
                                            def_DLUF_HLR2_scheduler4.Sps_def
                                            def_DLUF_HLR2_scheduler4_InputMap.Sps_def
                                            def_DLUF_HLR2_scheduler4_OutputMap.Sps_def
                                            def_DLUF_HLR2_scheduler4_Input.sbgetter_def
                                            def_DLUF_HLR2_scheduler4_Output.sbsetter_def
                                  con_defs: def_DLUF_LLR_scheduler4_InputMap.connector_def
                                            def_DLUF_HLR2_scheduler4_InputMap.connector_def
                                            def_DLUF_LLR_scheduler4_OutputMap.connector_def
                                            def_DLUF_HLR2_scheduler4_OutputMap.connector_def
                              sbGen_axioms: def_DLUF_LLR_scheduler4_Input.SB.sbGen_axioms
                                            def_DLUF_LLR_scheduler4_Output.SB.sbGen_axioms
                                            def_DLUF_HLR2_scheduler4_Input.SB.sbGen_axioms
                                            def_DLUF_HLR2_scheduler4_Output.SB.sbGen_axioms
                              buildSB_defs: def_DLUF_LLR_scheduler4_Input.buildSB_def
                                            def_DLUF_LLR_scheduler4_Output.buildSB_def
                                            def_DLUF_HLR2_scheduler4_Input.buildSB_def
                                            def_DLUF_HLR2_scheduler4_Output.buildSB_def)

  ultimately show ?thesis
    apply(simp add: def_DLUF_LLR.Sps_def def_DLUF_LLR.rawSps_def
                    def_DLUF_HLR2.Sps_def def_DLUF_HLR2.rawSps_def)
    by(compositional_refinement_proof)?
qed

lemma refinement[simp]: "def_DLUF_LLR.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<subseteq> def_DLUF_HLR2.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
  using refinement_withAssms
  (* autosledgi *) oops


end

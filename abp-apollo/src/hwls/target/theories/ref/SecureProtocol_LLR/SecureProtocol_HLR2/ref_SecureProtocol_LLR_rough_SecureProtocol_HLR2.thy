theory ref_SecureProtocol_LLR_rough_SecureProtocol_HLR2
  imports
    (* Core *) generator.ArchRef
    (* Gen  *) sps_SecureProtocol_LLR.def_SecureProtocol_LLR sps_SecureProtocol_HLR2.def_SecureProtocol_HLR2
               ref_Bob_LLR_refines_Bob_HLR.ref_Receiver_LLR_rough_Receiver_HLR
    (* Hwl  *)

begin



fun connector_in :: "def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channels \<Rightarrow> def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channels" where
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_alice_output_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_alice_output_val" |
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_bob_control_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_bob_control_val" |
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_bob_output_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_bob_output_val" |
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_decrypt1_output_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_decrypt1_output_val" |
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_decrypt2_output_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_decrypt2_output_val" |
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_encrypt1_output_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_encrypt1_output_val" |
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_encrypt2_output_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_encrypt2_output_val" |
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_eve1_output_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_eve1_output_val" |
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_eve2_output_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_eve2_output_val" |
  "connector_in def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channel_input_val = def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channel_input_val"

fun connector_out :: "def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels \<Rightarrow> def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channels" where
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_alice_control_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_alice_control_val" |
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_alice_input_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_alice_input_val" |
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_bob_input_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_bob_input_val" |
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_decrypt1_input_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_decrypt1_input_val" |
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_decrypt2_input_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_decrypt2_input_val" |
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_encrypt1_input_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_encrypt1_input_val" |
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_encrypt2_input_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_encrypt2_input_val" |
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_eve1_input_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_eve1_input_val" |
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_eve2_input_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_eve2_input_val" |
  "connector_out def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channel_output_val = def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channel_output_val"


fun alice_in :: "def_SecureProtocol_LLR_alice_Input.channels \<Rightarrow> def_SecureProtocol_HLR2_alice_Input.channels" where
  "alice_in def_SecureProtocol_LLR_alice_Input.channel_alice_control_val = def_SecureProtocol_HLR2_alice_Input.channel_alice_control_val" |
  "alice_in def_SecureProtocol_LLR_alice_Input.channel_alice_input_val = def_SecureProtocol_HLR2_alice_Input.channel_alice_input_val"

fun alice_out :: "def_SecureProtocol_HLR2_alice_Output.channels \<Rightarrow> def_SecureProtocol_LLR_alice_Output.channels" where
  "alice_out def_SecureProtocol_HLR2_alice_Output.channel_alice_output_val = def_SecureProtocol_LLR_alice_Output.channel_alice_output_val"


fun encrypt1_in :: "def_SecureProtocol_LLR_encrypt1_Input.channels \<Rightarrow> def_SecureProtocol_HLR2_encrypt1_Input.channels" where
  "encrypt1_in def_SecureProtocol_LLR_encrypt1_Input.channel_encrypt1_input_val = def_SecureProtocol_HLR2_encrypt1_Input.channel_encrypt1_input_val"

fun encrypt1_out :: "def_SecureProtocol_HLR2_encrypt1_Output.channels \<Rightarrow> def_SecureProtocol_LLR_encrypt1_Output.channels" where
  "encrypt1_out def_SecureProtocol_HLR2_encrypt1_Output.channel_encrypt1_output_val = def_SecureProtocol_LLR_encrypt1_Output.channel_encrypt1_output_val"


fun eve1_in :: "def_SecureProtocol_LLR_eve1_Input.channels \<Rightarrow> def_SecureProtocol_HLR2_eve1_Input.channels" where
  "eve1_in def_SecureProtocol_LLR_eve1_Input.channel_eve1_input_val = def_SecureProtocol_HLR2_eve1_Input.channel_eve1_input_val"

fun eve1_out :: "def_SecureProtocol_HLR2_eve1_Output.channels \<Rightarrow> def_SecureProtocol_LLR_eve1_Output.channels" where
  "eve1_out def_SecureProtocol_HLR2_eve1_Output.channel_eve1_output_val = def_SecureProtocol_LLR_eve1_Output.channel_eve1_output_val"


fun decrypt1_in :: "def_SecureProtocol_LLR_decrypt1_Input.channels \<Rightarrow> def_SecureProtocol_HLR2_decrypt1_Input.channels" where
  "decrypt1_in def_SecureProtocol_LLR_decrypt1_Input.channel_decrypt1_input_val = def_SecureProtocol_HLR2_decrypt1_Input.channel_decrypt1_input_val"

fun decrypt1_out :: "def_SecureProtocol_HLR2_decrypt1_Output.channels \<Rightarrow> def_SecureProtocol_LLR_decrypt1_Output.channels" where
  "decrypt1_out def_SecureProtocol_HLR2_decrypt1_Output.channel_decrypt1_output_val = def_SecureProtocol_LLR_decrypt1_Output.channel_decrypt1_output_val"


fun bob_in :: "def_SecureProtocol_LLR_bob_Input.channels \<Rightarrow> def_SecureProtocol_HLR2_bob_Input.channels" where
  "bob_in def_SecureProtocol_LLR_bob_Input.channel_bob_input_val = def_SecureProtocol_HLR2_bob_Input.channel_bob_input_val"

fun bob_out :: "def_SecureProtocol_HLR2_bob_Output.channels \<Rightarrow> def_SecureProtocol_LLR_bob_Output.channels" where
  "bob_out def_SecureProtocol_HLR2_bob_Output.channel_bob_control_val = def_SecureProtocol_LLR_bob_Output.channel_bob_control_val" |
  "bob_out def_SecureProtocol_HLR2_bob_Output.channel_bob_output_val = def_SecureProtocol_LLR_bob_Output.channel_bob_output_val"


fun encrypt2_in :: "def_SecureProtocol_LLR_encrypt2_Input.channels \<Rightarrow> def_SecureProtocol_HLR2_encrypt2_Input.channels" where
  "encrypt2_in def_SecureProtocol_LLR_encrypt2_Input.channel_encrypt2_input_val = def_SecureProtocol_HLR2_encrypt2_Input.channel_encrypt2_input_val"

fun encrypt2_out :: "def_SecureProtocol_HLR2_encrypt2_Output.channels \<Rightarrow> def_SecureProtocol_LLR_encrypt2_Output.channels" where
  "encrypt2_out def_SecureProtocol_HLR2_encrypt2_Output.channel_encrypt2_output_val = def_SecureProtocol_LLR_encrypt2_Output.channel_encrypt2_output_val"


fun eve2_in :: "def_SecureProtocol_LLR_eve2_Input.channels \<Rightarrow> def_SecureProtocol_HLR2_eve2_Input.channels" where
  "eve2_in def_SecureProtocol_LLR_eve2_Input.channel_eve2_input_val = def_SecureProtocol_HLR2_eve2_Input.channel_eve2_input_val"

fun eve2_out :: "def_SecureProtocol_HLR2_eve2_Output.channels \<Rightarrow> def_SecureProtocol_LLR_eve2_Output.channels" where
  "eve2_out def_SecureProtocol_HLR2_eve2_Output.channel_eve2_output_val = def_SecureProtocol_LLR_eve2_Output.channel_eve2_output_val"


fun decrypt2_in :: "def_SecureProtocol_LLR_decrypt2_Input.channels \<Rightarrow> def_SecureProtocol_HLR2_decrypt2_Input.channels" where
  "decrypt2_in def_SecureProtocol_LLR_decrypt2_Input.channel_decrypt2_input_val = def_SecureProtocol_HLR2_decrypt2_Input.channel_decrypt2_input_val"

fun decrypt2_out :: "def_SecureProtocol_HLR2_decrypt2_Output.channels \<Rightarrow> def_SecureProtocol_LLR_decrypt2_Output.channels" where
  "decrypt2_out def_SecureProtocol_HLR2_decrypt2_Output.channel_decrypt2_output_val = def_SecureProtocol_LLR_decrypt2_Output.channel_decrypt2_output_val"


(* refinement *)

lemma refinement_withAssms:
assumes "def_Alice_HLR.Sps () \<subseteq> def_Alice_HLR.Sps ()"
    and "def_Encrypt1_HLR.Sps () \<subseteq> def_Encrypt1_HLR.Sps ()"
    and "def_Eve1_HLR.Sps () \<subseteq> def_Eve1_HLR.Sps ()"
    and "def_Decrypt1_HLR.Sps () \<subseteq> def_Decrypt1_HLR.Sps ()"
    and "def_Bob_LLR.Sps () \<subseteq> def_Bob_HLR.Sps ()"
    and "def_Encrypt2_HLR.Sps () \<subseteq> def_Encrypt2_HLR.Sps ()"
    and "def_Eve2_HLR.Sps () \<subseteq> def_Eve2_HLR.Sps ()"
    and "def_Decrypt2_HLR.Sps () \<subseteq> def_Decrypt2_HLR.Sps ()"
  shows "def_SecureProtocol_LLR.Sps () \<subseteq> def_SecureProtocol_HLR2.Sps ()"
proof -

  interpret step1: wrappedSPSCompParallelConvert
  eve2_in
  eve2_out
  decrypt2_in
  decrypt2_out
  "TYPE(def_SecureProtocol_HLR1_Input.channels)"
  "TYPE(def_SecureProtocol_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_SecureProtocol_LLR_eve2_Input.channels_exists)
    apply(wrappedSPSConvert_proof input_channels_exists: def_SecureProtocol_LLR_decrypt2_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step2: wrappedSPSCompParallelConvert
  encrypt2_in
  encrypt2_out
  step1.comp_in
  step1.comp_out
  "TYPE(def_SecureProtocol_HLR1_Input.channels)"
  "TYPE(def_SecureProtocol_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_SecureProtocol_LLR_encrypt2_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step3: wrappedSPSCompParallelConvert
  bob_in
  bob_out
  step2.comp_in
  step2.comp_out
  "TYPE(def_SecureProtocol_HLR1_Input.channels)"
  "TYPE(def_SecureProtocol_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_SecureProtocol_LLR_bob_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step4: wrappedSPSCompParallelConvert
  decrypt1_in
  decrypt1_out
  step3.comp_in
  step3.comp_out
  "TYPE(def_SecureProtocol_HLR1_Input.channels)"
  "TYPE(def_SecureProtocol_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_SecureProtocol_LLR_decrypt1_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step5: wrappedSPSCompParallelConvert
  eve1_in
  eve1_out
  step4.comp_in
  step4.comp_out
  "TYPE(def_SecureProtocol_HLR1_Input.channels)"
  "TYPE(def_SecureProtocol_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_SecureProtocol_LLR_eve1_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step6: wrappedSPSCompParallelConvert
  encrypt1_in
  encrypt1_out
  step5.comp_in
  step5.comp_out
  "TYPE(def_SecureProtocol_HLR1_Input.channels)"
  "TYPE(def_SecureProtocol_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_SecureProtocol_LLR_encrypt1_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step7: wrappedSPSCompParallelConvert
  alice_in
  alice_out
  step6.comp_in
  step6.comp_out
  "TYPE(def_SecureProtocol_HLR1_Input.channels)"
  "TYPE(def_SecureProtocol_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_SecureProtocol_LLR_alice_Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step8: wrappedSPSCompNoOverlapConvert
  connector_in
  connector_out
  step7.comp_in
  step7.comp_out
  "TYPE(def_SecureProtocol_HLR1_Input.channels)"
  "TYPE(def_SecureProtocol_HLR1_Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channels_exists)
    by(wrappedSPSCompNoOverlap_proof)


  have "{sbRenameCh connector_in} \<then> def_SecureProtocol_LLR_connector.Sps () \<then> {sbRenameCh connector_out} \<subseteq> def_SecureProtocol_HLR2_connector.Sps ()"
    by (connector_simulation_proof simp_defs: def_SecureProtocol_LLR_connector.Sps_def
                                              def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.sbgetter_def
                                              def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.sbsetter_def
                                              def_SecureProtocol_HLR2_connector.Sps_def
                                              def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.sbgetter_def
                                              def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.sbsetter_def
                                    con_defs: def_SecureProtocol_LLR_connector.connector_def
                                              def_SecureProtocol_HLR2_connector.connector_def
                                sbGen_axioms: def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.SB.sbGen_axioms
                                              def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.SB.sbGen_axioms
                                              def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.SB.sbGen_axioms
                                              def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.SB.sbGen_axioms
                                buildSB_defs: def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.buildSB_def
                                              def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.buildSB_def
                                              def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.buildSB_def
                                              def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.buildSB_def)

  moreover have "{sbRenameCh alice_in} \<then> def_SecureProtocol_LLR_alice.Sps () \<then> {sbRenameCh alice_out} \<subseteq> def_SecureProtocol_HLR2_alice.Sps ()"
    by (component_simulation_proof sps_ref: assms(1)
                                 simp_defs: def_SecureProtocol_LLR_alice.Sps_def
                                            def_SecureProtocol_LLR_alice_InputMap.Sps_def
                                            def_SecureProtocol_LLR_alice_OutputMap.Sps_def
                                            def_SecureProtocol_LLR_alice_Input.sbgetter_def
                                            def_SecureProtocol_LLR_alice_Output.sbsetter_def
                                            def_SecureProtocol_HLR2_alice.Sps_def
                                            def_SecureProtocol_HLR2_alice_InputMap.Sps_def
                                            def_SecureProtocol_HLR2_alice_OutputMap.Sps_def
                                            def_SecureProtocol_HLR2_alice_Input.sbgetter_def
                                            def_SecureProtocol_HLR2_alice_Output.sbsetter_def
                                  con_defs: def_SecureProtocol_LLR_alice_InputMap.connector_def
                                            def_SecureProtocol_HLR2_alice_InputMap.connector_def
                                            def_SecureProtocol_LLR_alice_OutputMap.connector_def
                                            def_SecureProtocol_HLR2_alice_OutputMap.connector_def
                              sbGen_axioms: def_SecureProtocol_LLR_alice_Input.SB.sbGen_axioms
                                            def_SecureProtocol_LLR_alice_Output.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_alice_Input.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_alice_Output.SB.sbGen_axioms
                              buildSB_defs: def_SecureProtocol_LLR_alice_Input.buildSB_def
                                            def_SecureProtocol_LLR_alice_Output.buildSB_def
                                            def_SecureProtocol_HLR2_alice_Input.buildSB_def
                                            def_SecureProtocol_HLR2_alice_Output.buildSB_def)

  moreover have "{sbRenameCh encrypt1_in} \<then> def_SecureProtocol_LLR_encrypt1.Sps () \<then> {sbRenameCh encrypt1_out} \<subseteq> def_SecureProtocol_HLR2_encrypt1.Sps ()"
    by (component_simulation_proof sps_ref: assms(2)
                                 simp_defs: def_SecureProtocol_LLR_encrypt1.Sps_def
                                            def_SecureProtocol_LLR_encrypt1_InputMap.Sps_def
                                            def_SecureProtocol_LLR_encrypt1_OutputMap.Sps_def
                                            def_SecureProtocol_LLR_encrypt1_Input.sbgetter_def
                                            def_SecureProtocol_LLR_encrypt1_Output.sbsetter_def
                                            def_SecureProtocol_HLR2_encrypt1.Sps_def
                                            def_SecureProtocol_HLR2_encrypt1_InputMap.Sps_def
                                            def_SecureProtocol_HLR2_encrypt1_OutputMap.Sps_def
                                            def_SecureProtocol_HLR2_encrypt1_Input.sbgetter_def
                                            def_SecureProtocol_HLR2_encrypt1_Output.sbsetter_def
                                  con_defs: def_SecureProtocol_LLR_encrypt1_InputMap.connector_def
                                            def_SecureProtocol_HLR2_encrypt1_InputMap.connector_def
                                            def_SecureProtocol_LLR_encrypt1_OutputMap.connector_def
                                            def_SecureProtocol_HLR2_encrypt1_OutputMap.connector_def
                              sbGen_axioms: def_SecureProtocol_LLR_encrypt1_Input.SB.sbGen_axioms
                                            def_SecureProtocol_LLR_encrypt1_Output.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_encrypt1_Input.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_encrypt1_Output.SB.sbGen_axioms
                              buildSB_defs: def_SecureProtocol_LLR_encrypt1_Input.buildSB_def
                                            def_SecureProtocol_LLR_encrypt1_Output.buildSB_def
                                            def_SecureProtocol_HLR2_encrypt1_Input.buildSB_def
                                            def_SecureProtocol_HLR2_encrypt1_Output.buildSB_def)

  moreover have "{sbRenameCh eve1_in} \<then> def_SecureProtocol_LLR_eve1.Sps () \<then> {sbRenameCh eve1_out} \<subseteq> def_SecureProtocol_HLR2_eve1.Sps ()"
    by (component_simulation_proof sps_ref: assms(3)
                                 simp_defs: def_SecureProtocol_LLR_eve1.Sps_def
                                            def_SecureProtocol_LLR_eve1_InputMap.Sps_def
                                            def_SecureProtocol_LLR_eve1_OutputMap.Sps_def
                                            def_SecureProtocol_LLR_eve1_Input.sbgetter_def
                                            def_SecureProtocol_LLR_eve1_Output.sbsetter_def
                                            def_SecureProtocol_HLR2_eve1.Sps_def
                                            def_SecureProtocol_HLR2_eve1_InputMap.Sps_def
                                            def_SecureProtocol_HLR2_eve1_OutputMap.Sps_def
                                            def_SecureProtocol_HLR2_eve1_Input.sbgetter_def
                                            def_SecureProtocol_HLR2_eve1_Output.sbsetter_def
                                  con_defs: def_SecureProtocol_LLR_eve1_InputMap.connector_def
                                            def_SecureProtocol_HLR2_eve1_InputMap.connector_def
                                            def_SecureProtocol_LLR_eve1_OutputMap.connector_def
                                            def_SecureProtocol_HLR2_eve1_OutputMap.connector_def
                              sbGen_axioms: def_SecureProtocol_LLR_eve1_Input.SB.sbGen_axioms
                                            def_SecureProtocol_LLR_eve1_Output.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_eve1_Input.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_eve1_Output.SB.sbGen_axioms
                              buildSB_defs: def_SecureProtocol_LLR_eve1_Input.buildSB_def
                                            def_SecureProtocol_LLR_eve1_Output.buildSB_def
                                            def_SecureProtocol_HLR2_eve1_Input.buildSB_def
                                            def_SecureProtocol_HLR2_eve1_Output.buildSB_def)

  moreover have "{sbRenameCh decrypt1_in} \<then> def_SecureProtocol_LLR_decrypt1.Sps () \<then> {sbRenameCh decrypt1_out} \<subseteq> def_SecureProtocol_HLR2_decrypt1.Sps ()"
    by (component_simulation_proof sps_ref: assms(4)
                                 simp_defs: def_SecureProtocol_LLR_decrypt1.Sps_def
                                            def_SecureProtocol_LLR_decrypt1_InputMap.Sps_def
                                            def_SecureProtocol_LLR_decrypt1_OutputMap.Sps_def
                                            def_SecureProtocol_LLR_decrypt1_Input.sbgetter_def
                                            def_SecureProtocol_LLR_decrypt1_Output.sbsetter_def
                                            def_SecureProtocol_HLR2_decrypt1.Sps_def
                                            def_SecureProtocol_HLR2_decrypt1_InputMap.Sps_def
                                            def_SecureProtocol_HLR2_decrypt1_OutputMap.Sps_def
                                            def_SecureProtocol_HLR2_decrypt1_Input.sbgetter_def
                                            def_SecureProtocol_HLR2_decrypt1_Output.sbsetter_def
                                  con_defs: def_SecureProtocol_LLR_decrypt1_InputMap.connector_def
                                            def_SecureProtocol_HLR2_decrypt1_InputMap.connector_def
                                            def_SecureProtocol_LLR_decrypt1_OutputMap.connector_def
                                            def_SecureProtocol_HLR2_decrypt1_OutputMap.connector_def
                              sbGen_axioms: def_SecureProtocol_LLR_decrypt1_Input.SB.sbGen_axioms
                                            def_SecureProtocol_LLR_decrypt1_Output.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_decrypt1_Input.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_decrypt1_Output.SB.sbGen_axioms
                              buildSB_defs: def_SecureProtocol_LLR_decrypt1_Input.buildSB_def
                                            def_SecureProtocol_LLR_decrypt1_Output.buildSB_def
                                            def_SecureProtocol_HLR2_decrypt1_Input.buildSB_def
                                            def_SecureProtocol_HLR2_decrypt1_Output.buildSB_def)

  moreover have "{sbRenameCh bob_in} \<then> def_SecureProtocol_LLR_bob.Sps () \<then> {sbRenameCh bob_out} \<subseteq> def_SecureProtocol_HLR2_bob.Sps ()"
    by (component_simulation_proof sps_ref: assms(5)
                                 simp_defs: def_SecureProtocol_LLR_bob.Sps_def
                                            def_SecureProtocol_LLR_bob_InputMap.Sps_def
                                            def_SecureProtocol_LLR_bob_OutputMap.Sps_def
                                            def_SecureProtocol_LLR_bob_Input.sbgetter_def
                                            def_SecureProtocol_LLR_bob_Output.sbsetter_def
                                            def_SecureProtocol_HLR2_bob.Sps_def
                                            def_SecureProtocol_HLR2_bob_InputMap.Sps_def
                                            def_SecureProtocol_HLR2_bob_OutputMap.Sps_def
                                            def_SecureProtocol_HLR2_bob_Input.sbgetter_def
                                            def_SecureProtocol_HLR2_bob_Output.sbsetter_def
                                  con_defs: def_SecureProtocol_LLR_bob_InputMap.connector_def
                                            def_SecureProtocol_HLR2_bob_InputMap.connector_def
                                            def_SecureProtocol_LLR_bob_OutputMap.connector_def
                                            def_SecureProtocol_HLR2_bob_OutputMap.connector_def
                              sbGen_axioms: def_SecureProtocol_LLR_bob_Input.SB.sbGen_axioms
                                            def_SecureProtocol_LLR_bob_Output.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_bob_Input.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_bob_Output.SB.sbGen_axioms
                              buildSB_defs: def_SecureProtocol_LLR_bob_Input.buildSB_def
                                            def_SecureProtocol_LLR_bob_Output.buildSB_def
                                            def_SecureProtocol_HLR2_bob_Input.buildSB_def
                                            def_SecureProtocol_HLR2_bob_Output.buildSB_def)

  moreover have "{sbRenameCh encrypt2_in} \<then> def_SecureProtocol_LLR_encrypt2.Sps () \<then> {sbRenameCh encrypt2_out} \<subseteq> def_SecureProtocol_HLR2_encrypt2.Sps ()"
    by (component_simulation_proof sps_ref: assms(6)
                                 simp_defs: def_SecureProtocol_LLR_encrypt2.Sps_def
                                            def_SecureProtocol_LLR_encrypt2_InputMap.Sps_def
                                            def_SecureProtocol_LLR_encrypt2_OutputMap.Sps_def
                                            def_SecureProtocol_LLR_encrypt2_Input.sbgetter_def
                                            def_SecureProtocol_LLR_encrypt2_Output.sbsetter_def
                                            def_SecureProtocol_HLR2_encrypt2.Sps_def
                                            def_SecureProtocol_HLR2_encrypt2_InputMap.Sps_def
                                            def_SecureProtocol_HLR2_encrypt2_OutputMap.Sps_def
                                            def_SecureProtocol_HLR2_encrypt2_Input.sbgetter_def
                                            def_SecureProtocol_HLR2_encrypt2_Output.sbsetter_def
                                  con_defs: def_SecureProtocol_LLR_encrypt2_InputMap.connector_def
                                            def_SecureProtocol_HLR2_encrypt2_InputMap.connector_def
                                            def_SecureProtocol_LLR_encrypt2_OutputMap.connector_def
                                            def_SecureProtocol_HLR2_encrypt2_OutputMap.connector_def
                              sbGen_axioms: def_SecureProtocol_LLR_encrypt2_Input.SB.sbGen_axioms
                                            def_SecureProtocol_LLR_encrypt2_Output.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_encrypt2_Input.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_encrypt2_Output.SB.sbGen_axioms
                              buildSB_defs: def_SecureProtocol_LLR_encrypt2_Input.buildSB_def
                                            def_SecureProtocol_LLR_encrypt2_Output.buildSB_def
                                            def_SecureProtocol_HLR2_encrypt2_Input.buildSB_def
                                            def_SecureProtocol_HLR2_encrypt2_Output.buildSB_def)

  moreover have "{sbRenameCh eve2_in} \<then> def_SecureProtocol_LLR_eve2.Sps () \<then> {sbRenameCh eve2_out} \<subseteq> def_SecureProtocol_HLR2_eve2.Sps ()"
    by (component_simulation_proof sps_ref: assms(7)
                                 simp_defs: def_SecureProtocol_LLR_eve2.Sps_def
                                            def_SecureProtocol_LLR_eve2_InputMap.Sps_def
                                            def_SecureProtocol_LLR_eve2_OutputMap.Sps_def
                                            def_SecureProtocol_LLR_eve2_Input.sbgetter_def
                                            def_SecureProtocol_LLR_eve2_Output.sbsetter_def
                                            def_SecureProtocol_HLR2_eve2.Sps_def
                                            def_SecureProtocol_HLR2_eve2_InputMap.Sps_def
                                            def_SecureProtocol_HLR2_eve2_OutputMap.Sps_def
                                            def_SecureProtocol_HLR2_eve2_Input.sbgetter_def
                                            def_SecureProtocol_HLR2_eve2_Output.sbsetter_def
                                  con_defs: def_SecureProtocol_LLR_eve2_InputMap.connector_def
                                            def_SecureProtocol_HLR2_eve2_InputMap.connector_def
                                            def_SecureProtocol_LLR_eve2_OutputMap.connector_def
                                            def_SecureProtocol_HLR2_eve2_OutputMap.connector_def
                              sbGen_axioms: def_SecureProtocol_LLR_eve2_Input.SB.sbGen_axioms
                                            def_SecureProtocol_LLR_eve2_Output.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_eve2_Input.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_eve2_Output.SB.sbGen_axioms
                              buildSB_defs: def_SecureProtocol_LLR_eve2_Input.buildSB_def
                                            def_SecureProtocol_LLR_eve2_Output.buildSB_def
                                            def_SecureProtocol_HLR2_eve2_Input.buildSB_def
                                            def_SecureProtocol_HLR2_eve2_Output.buildSB_def)

  moreover have "{sbRenameCh decrypt2_in} \<then> def_SecureProtocol_LLR_decrypt2.Sps () \<then> {sbRenameCh decrypt2_out} \<subseteq> def_SecureProtocol_HLR2_decrypt2.Sps ()"
    by (component_simulation_proof sps_ref: assms(8)
                                 simp_defs: def_SecureProtocol_LLR_decrypt2.Sps_def
                                            def_SecureProtocol_LLR_decrypt2_InputMap.Sps_def
                                            def_SecureProtocol_LLR_decrypt2_OutputMap.Sps_def
                                            def_SecureProtocol_LLR_decrypt2_Input.sbgetter_def
                                            def_SecureProtocol_LLR_decrypt2_Output.sbsetter_def
                                            def_SecureProtocol_HLR2_decrypt2.Sps_def
                                            def_SecureProtocol_HLR2_decrypt2_InputMap.Sps_def
                                            def_SecureProtocol_HLR2_decrypt2_OutputMap.Sps_def
                                            def_SecureProtocol_HLR2_decrypt2_Input.sbgetter_def
                                            def_SecureProtocol_HLR2_decrypt2_Output.sbsetter_def
                                  con_defs: def_SecureProtocol_LLR_decrypt2_InputMap.connector_def
                                            def_SecureProtocol_HLR2_decrypt2_InputMap.connector_def
                                            def_SecureProtocol_LLR_decrypt2_OutputMap.connector_def
                                            def_SecureProtocol_HLR2_decrypt2_OutputMap.connector_def
                              sbGen_axioms: def_SecureProtocol_LLR_decrypt2_Input.SB.sbGen_axioms
                                            def_SecureProtocol_LLR_decrypt2_Output.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_decrypt2_Input.SB.sbGen_axioms
                                            def_SecureProtocol_HLR2_decrypt2_Output.SB.sbGen_axioms
                              buildSB_defs: def_SecureProtocol_LLR_decrypt2_Input.buildSB_def
                                            def_SecureProtocol_LLR_decrypt2_Output.buildSB_def
                                            def_SecureProtocol_HLR2_decrypt2_Input.buildSB_def
                                            def_SecureProtocol_HLR2_decrypt2_Output.buildSB_def)

  ultimately show ?thesis
    apply(simp add: def_SecureProtocol_LLR.Sps_def def_SecureProtocol_LLR.rawSps_def
                    def_SecureProtocol_HLR2.Sps_def def_SecureProtocol_HLR2.rawSps_def)
    by(compositional_refinement_proof)?
qed

lemma refinement[simp]: "def_SecureProtocol_LLR.Sps () \<subseteq> def_SecureProtocol_HLR2.Sps ()"
  apply(simp add: refinement_withAssms)?
  (* autosledgi *) oops


end

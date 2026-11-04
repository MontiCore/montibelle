theory CompositeHlrNarrowing
  imports
    (* Core *) generator.ArchRef
    (* Gen  *) composition.SerialComposition composition.SerialComposition
               AutomaticHlrNarrowing
    (* Hwl  *)

begin



fun Connectors_Serial_in :: "Connector2Input.channels \<Rightarrow> Connector2Input.channels" where
  "Connectors_Serial_in Connector2Input.natInChannel_rep = Connector2Input.natInChannel_rep" |
  "Connectors_Serial_in Connector2Input.bInChannel_rep = Connector2Input.bInChannel_rep" |
  "Connectors_Serial_in Connector2Input.sInChannel_rep = Connector2Input.sInChannel_rep" |
  "Connectors_Serial_in Connector2Input.natOutChannel_instantiated_1_rep = Connector2Input.natOutChannel_instantiated_1_rep" |
  "Connectors_Serial_in Connector2Input.bOutChannel_instantiated_1_rep = Connector2Input.bOutChannel_instantiated_1_rep" |
  "Connectors_Serial_in Connector2Input.sOutChannel_instantiated_1_rep = Connector2Input.sOutChannel_instantiated_1_rep" |
  "Connectors_Serial_in Connector2Input.natOutChannel_instantiated_2_rep = Connector2Input.natOutChannel_instantiated_2_rep" |
  "Connectors_Serial_in Connector2Input.bOutChannel_instantiated_2_rep = Connector2Input.bOutChannel_instantiated_2_rep" |
  "Connectors_Serial_in Connector2Input.sOutChannel_instantiated_2_rep = Connector2Input.sOutChannel_instantiated_2_rep"

fun Connectors_Serial_out :: "Connector2Output.channels \<Rightarrow> Connector2Output.channels" where
  "Connectors_Serial_out Connector2Output.natInChannel_instantiated_1_rep = Connector2Output.natInChannel_instantiated_1_rep" |
  "Connectors_Serial_out Connector2Output.bInChannel_instantiated_1_rep = Connector2Output.bInChannel_instantiated_1_rep" |
  "Connectors_Serial_out Connector2Output.sInChannel_instantiated_1_rep = Connector2Output.sInChannel_instantiated_1_rep" |
  "Connectors_Serial_out Connector2Output.natInChannel_instantiated_2_rep = Connector2Output.natInChannel_instantiated_2_rep" |
  "Connectors_Serial_out Connector2Output.bInChannel_instantiated_2_rep = Connector2Output.bInChannel_instantiated_2_rep" |
  "Connectors_Serial_out Connector2Output.sInChannel_instantiated_2_rep = Connector2Output.sInChannel_instantiated_2_rep" |
  "Connectors_Serial_out Connector2Output.natOutChannel_rep = Connector2Output.natOutChannel_rep" |
  "Connectors_Serial_out Connector2Output.bOutChannel_rep = Connector2Output.bOutChannel_rep" |
  "Connectors_Serial_out Connector2Output.sOutChannel_rep = Connector2Output.sOutChannel_rep"


fun SpecificationInstance_in :: "Instance1Input.channels \<Rightarrow> Instance1Input.channels" where
  "SpecificationInstance_in Instance1Input.natInChannel_instantiated_1_rep = Instance1Input.natInChannel_instantiated_1_rep" |
  "SpecificationInstance_in Instance1Input.bInChannel_instantiated_1_rep = Instance1Input.bInChannel_instantiated_1_rep" |
  "SpecificationInstance_in Instance1Input.sInChannel_instantiated_1_rep = Instance1Input.sInChannel_instantiated_1_rep"

fun SpecificationInstance_out :: "Instance1Output.channels \<Rightarrow> Instance1Output.channels" where
  "SpecificationInstance_out Instance1Output.natOutChannel_instantiated_1_rep = Instance1Output.natOutChannel_instantiated_1_rep" |
  "SpecificationInstance_out Instance1Output.bOutChannel_instantiated_1_rep = Instance1Output.bOutChannel_instantiated_1_rep" |
  "SpecificationInstance_out Instance1Output.sOutChannel_instantiated_1_rep = Instance1Output.sOutChannel_instantiated_1_rep"


fun SpecificationInstance2_in :: "Instance2Input.channels \<Rightarrow> Instance2Input.channels" where
  "SpecificationInstance2_in Instance2Input.natInChannel_instantiated_2_rep = Instance2Input.natInChannel_instantiated_2_rep" |
  "SpecificationInstance2_in Instance2Input.bInChannel_instantiated_2_rep = Instance2Input.bInChannel_instantiated_2_rep" |
  "SpecificationInstance2_in Instance2Input.sInChannel_instantiated_2_rep = Instance2Input.sInChannel_instantiated_2_rep"

fun SpecificationInstance2_out :: "Instance2Output.channels \<Rightarrow> Instance2Output.channels" where
  "SpecificationInstance2_out Instance2Output.natOutChannel_instantiated_2_rep = Instance2Output.natOutChannel_instantiated_2_rep" |
  "SpecificationInstance2_out Instance2Output.bOutChannel_instantiated_2_rep = Instance2Output.bOutChannel_instantiated_2_rep" |
  "SpecificationInstance2_out Instance2Output.sOutChannel_instantiated_2_rep = Instance2Output.sOutChannel_instantiated_2_rep"


(* refinement *)

lemma refinement_withAssms:
assumes "Specification.Sps () \<subseteq> Specification.Sps ()"
    and "Specification.Sps () \<subseteq> Specification.Sps ()"
  shows "SerialComposition.Sps () \<subseteq> SerialComposition.Sps ()"
proof -

  interpret step1: wrappedSPSCompParallelConvert
  SpecificationInstance_in
  SpecificationInstance_out
  SpecificationInstance2_in
  SpecificationInstance2_out
  "TYPE(Input.channels)"
  "TYPE(Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: Instance1Input.channels_exists)
    apply(wrappedSPSConvert_proof input_channels_exists: Instance2Input.channels_exists)
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done

  interpret step2: wrappedSPSCompNoOverlapConvert
  Connectors_Serial_in
  Connectors_Serial_out
  step1.comp_in
  step1.comp_out
  "TYPE(Input.channels)"
  "TYPE(Output.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: Connector2Input.channels_exists)
    by(wrappedSPSCompNoOverlap_proof)


  have "{sbRenameCh Connectors_Serial_in} \<then> Connectors_Serial.Sps () \<then> {sbRenameCh Connectors_Serial_out} \<subseteq> Connectors_Serial.Sps ()"
    by (connector_simulation_proof simp_defs: Connectors_Serial.Sps_def
                                              Connector2Input.sbgetter_def
                                              Connector2Output.sbsetter_def
                                              Connectors_Serial.Sps_def
                                              Connector2Input.sbgetter_def
                                              Connector2Output.sbsetter_def
                                    con_defs: Connectors_Serial.connector_def
                                              Connectors_Serial.connector_def
                                sbGen_axioms: Connector2Input.SB.sbGen_axioms
                                              Connector2Output.SB.sbGen_axioms
                                              Connector2Input.SB.sbGen_axioms
                                              Connector2Output.SB.sbGen_axioms
                                buildSB_defs: Connector2Input.buildSB_def
                                              Connector2Output.buildSB_def
                                              Connector2Input.buildSB_def
                                              Connector2Output.buildSB_def)

  moreover have "{sbRenameCh SpecificationInstance_in} \<then> SpecificationInstance.Sps () \<then> {sbRenameCh SpecificationInstance_out} \<subseteq> SpecificationInstance.Sps ()"
    by (component_simulation_proof sps_ref: assms(1)
                                 simp_defs: SpecificationInstance.Sps_def
                                            InputMap.Sps_def
                                            OutputMap.Sps_def
                                            Instance1Input.sbgetter_def
                                            Instance1Output.sbsetter_def
                                            SpecificationInstance.Sps_def
                                            InputMap.Sps_def
                                            OutputMap.Sps_def
                                            Instance1Input.sbgetter_def
                                            Instance1Output.sbsetter_def
                                  con_defs: InputMap.connector_def
                                            InputMap.connector_def
                                            OutputMap.connector_def
                                            OutputMap.connector_def
                              sbGen_axioms: Instance1Input.SB.sbGen_axioms
                                            Instance1Output.SB.sbGen_axioms
                                            Instance1Input.SB.sbGen_axioms
                                            Instance1Output.SB.sbGen_axioms
                              buildSB_defs: Instance1Input.buildSB_def
                                            Instance1Output.buildSB_def
                                            Instance1Input.buildSB_def
                                            Instance1Output.buildSB_def)

  moreover have "{sbRenameCh SpecificationInstance2_in} \<then> SpecificationInstance2.Sps () \<then> {sbRenameCh SpecificationInstance2_out} \<subseteq> SpecificationInstance2.Sps ()"
    by (component_simulation_proof sps_ref: assms(2)
                                 simp_defs: SpecificationInstance2.Sps_def
                                            InputMap2.Sps_def
                                            OutputMap2.Sps_def
                                            Instance2Input.sbgetter_def
                                            Instance2Output.sbsetter_def
                                            SpecificationInstance2.Sps_def
                                            InputMap2.Sps_def
                                            OutputMap2.Sps_def
                                            Instance2Input.sbgetter_def
                                            Instance2Output.sbsetter_def
                                  con_defs: InputMap2.connector_def
                                            InputMap2.connector_def
                                            OutputMap2.connector_def
                                            OutputMap2.connector_def
                              sbGen_axioms: Instance2Input.SB.sbGen_axioms
                                            Instance2Output.SB.sbGen_axioms
                                            Instance2Input.SB.sbGen_axioms
                                            Instance2Output.SB.sbGen_axioms
                              buildSB_defs: Instance2Input.buildSB_def
                                            Instance2Output.buildSB_def
                                            Instance2Input.buildSB_def
                                            Instance2Output.buildSB_def)

  ultimately show ?thesis
    apply(simp add: SerialComposition.Sps_def SerialComposition.rawSps_def
                    SerialComposition.Sps_def SerialComposition.rawSps_def)
    by(compositional_refinement_proof)?
qed

lemma refinement[simp]: "SerialComposition.Sps () \<subseteq> SerialComposition.Sps ()"
  (* autosledgi *) oops


end

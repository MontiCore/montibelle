theory def_Composition_part
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Composition_part.def_Composition_part_Input bundle_Composition_part.def_Composition_part_Output sps_PartDefinition.def_PartDefinition sps_Composition_part_InputMap.def_Composition_part_InputMap sps_Composition_part_OutputMap.def_Composition_part_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_Composition_part_Input.channels\<^sup>\<Omega> \<rightarrow> def_Composition_part_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_Composition_part_InputMap.Sps () \<then> def_PartDefinition.Sps () \<then> def_Composition_part_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_PartDefinition.Sps () \<Longrightarrow> P (def_PartDefinition_Input.SB.getter\<cdot>sb) (def_PartDefinition_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_Composition_part_Input.SB.getter\<cdot>sb) (def_Composition_part_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_Composition_part_InputMap.Sps_def def_Composition_part_OutputMap.Sps_def
    oo_def def_Composition_part_InputMap.connector.rep_eq def_Composition_part_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_PartDefinition_Input.SB.get_set)


end

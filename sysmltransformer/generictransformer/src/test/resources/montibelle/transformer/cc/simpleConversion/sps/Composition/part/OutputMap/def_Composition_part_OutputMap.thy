theory def_Composition_part_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_PartDefinition.def_PartDefinition_Output bundle_Composition_part.def_Composition_part_Output
    (* Hwl  *)

begin


lift_definition connector :: "(bool event stream) \<rightarrow> (bool event stream)" is
"\<lambda> (channel_o_pattern). (channel_o_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_PartDefinition_Output.channels\<^sup>\<Omega> \<rightarrow> def_Composition_part_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Composition_part_Output.SB.setter oo connector oo def_PartDefinition_Output.SB.getter }"


end

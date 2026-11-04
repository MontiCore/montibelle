theory def_Composition_part_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Composition_part.def_Composition_part_Input bundle_PartDefinition.def_PartDefinition_Input
    (* Hwl  *)

begin


lift_definition connector :: "(bool event stream) \<rightarrow> (bool event stream)" is
"\<lambda> (channel_part_i_pattern). (channel_part_i_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Composition_part_Input.channels\<^sup>\<Omega> \<rightarrow> def_PartDefinition_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_PartDefinition_Input.SB.setter oo connector oo def_Composition_part_Input.SB.getter }"


end

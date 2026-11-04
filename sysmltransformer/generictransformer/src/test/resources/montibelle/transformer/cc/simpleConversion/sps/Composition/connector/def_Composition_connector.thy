theory def_Composition_connector
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Composition_connector.def_Composition_connector_Composition_connector_Input bundle_Composition_connector.def_Composition_connector_Composition_connector_Output
    (* Hwl  *)

begin


lift_definition connector :: "(bool event stream \<times> bool event stream) \<rightarrow> (bool event stream \<times> bool event stream)" is
"\<lambda> (channel_i_pattern, channel_part_o_pattern). (channel_part_o_pattern, channel_i_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Composition_connector_Composition_connector_Input.channels\<^sup>\<Omega> \<rightarrow> def_Composition_connector_Composition_connector_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Composition_connector_Composition_connector_Output.SB.setter oo connector oo def_Composition_connector_Composition_connector_Input.SB.getter }"


end

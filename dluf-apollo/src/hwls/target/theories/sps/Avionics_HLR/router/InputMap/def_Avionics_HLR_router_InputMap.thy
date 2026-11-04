theory def_Avionics_HLR_router_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Avionics_HLR_router.def_Avionics_HLR_router_Input bundle_Router.def_Router_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_router_input_data_pattern). (channel_router_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Avionics_HLR_router_Input.channels\<^sup>\<Omega> \<rightarrow> def_Router_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Router_Input.SB.setter oo connector oo def_Avionics_HLR_router_Input.SB.getter }"


end

theory def_SecureProtocol_HLR2_alice_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_HLR2_alice.def_SecureProtocol_HLR2_alice_Input bundle_Alice_HLR.def_Alice_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(bool tsyn stream \<times> nat tsyn stream) \<rightarrow> (bool tsyn stream \<times> nat tsyn stream)" is
"\<lambda> (channel_alice_control_val_pattern, channel_alice_input_val_pattern). (channel_alice_control_val_pattern, channel_alice_input_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR2_alice_Input.channels\<^sup>\<Omega> \<rightarrow> def_Alice_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Alice_HLR_Input.SB.setter oo connector oo def_SecureProtocol_HLR2_alice_Input.SB.getter }"


end

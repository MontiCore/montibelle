theory def_SecureProtocol_LLR_encrypt2_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_LLR_encrypt2.def_SecureProtocol_LLR_encrypt2_Input bundle_Encrypt2_HLR.def_Encrypt2_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(bool tsyn stream) \<rightarrow> (bool tsyn stream)" is
"\<lambda> (channel_encrypt2_input_val_pattern). (channel_encrypt2_input_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_LLR_encrypt2_Input.channels\<^sup>\<Omega> \<rightarrow> def_Encrypt2_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Encrypt2_HLR_Input.SB.setter oo connector oo def_SecureProtocol_LLR_encrypt2_Input.SB.getter }"


end

theory def_SecureProtocol_LLR_decrypt2_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_LLR_decrypt2.def_SecureProtocol_LLR_decrypt2_Input bundle_Decrypt2_HLR.def_Decrypt2_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(bool tsyn stream) \<rightarrow> (bool tsyn stream)" is
"\<lambda> (channel_decrypt2_input_val_pattern). (channel_decrypt2_input_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_LLR_decrypt2_Input.channels\<^sup>\<Omega> \<rightarrow> def_Decrypt2_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Decrypt2_HLR_Input.SB.setter oo connector oo def_SecureProtocol_LLR_decrypt2_Input.SB.getter }"


end

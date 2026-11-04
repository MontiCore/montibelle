theory def_SecureProtocol_LLR_encrypt2_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Encrypt2_HLR.def_Encrypt2_HLR_Output bundle_SecureProtocol_LLR_encrypt2.def_SecureProtocol_LLR_encrypt2_Output
    (* Hwl  *)

begin


lift_definition connector :: "(bool tsyn stream) \<rightarrow> (bool tsyn stream)" is
"\<lambda> (channel_output_val_pattern). (channel_output_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Encrypt2_HLR_Output.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_LLR_encrypt2_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SecureProtocol_LLR_encrypt2_Output.SB.setter oo connector oo def_Encrypt2_HLR_Output.SB.getter }"


end

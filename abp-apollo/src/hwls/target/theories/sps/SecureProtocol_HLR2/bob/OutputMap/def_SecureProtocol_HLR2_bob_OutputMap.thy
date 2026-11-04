theory def_SecureProtocol_HLR2_bob_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Bob_HLR.def_Bob_HLR_Output bundle_SecureProtocol_HLR2_bob.def_SecureProtocol_HLR2_bob_Output
    (* Hwl  *)

begin


lift_definition connector :: "(bool tsyn stream \<times> nat tsyn stream) \<rightarrow> (bool tsyn stream \<times> nat tsyn stream)" is
"\<lambda> (channel_control_val_pattern, channel_output_val_pattern). (channel_control_val_pattern, channel_output_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Bob_HLR_Output.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_HLR2_bob_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SecureProtocol_HLR2_bob_Output.SB.setter oo connector oo def_Bob_HLR_Output.SB.getter }"


end

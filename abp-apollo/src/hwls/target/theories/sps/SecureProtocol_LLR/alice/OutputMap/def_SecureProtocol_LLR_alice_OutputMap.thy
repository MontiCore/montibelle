theory def_SecureProtocol_LLR_alice_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Alice_HLR.def_Alice_HLR_Output bundle_SecureProtocol_LLR_alice.def_SecureProtocol_LLR_alice_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Data_Bool_Tuple tsyn stream) \<rightarrow> (Data_Bool_Tuple tsyn stream)" is
"\<lambda> (channel_output_val_pattern). (channel_output_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Alice_HLR_Output.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_LLR_alice_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SecureProtocol_LLR_alice_Output.SB.setter oo connector oo def_Alice_HLR_Output.SB.getter }"


end

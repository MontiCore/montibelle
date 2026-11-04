theory def_SecureProtocol_HLR2_decrypt1_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_HLR2_decrypt1.def_SecureProtocol_HLR2_decrypt1_Input bundle_Decrypt1_HLR.def_Decrypt1_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Data_Bool_Tuple tsyn stream) \<rightarrow> (Data_Bool_Tuple tsyn stream)" is
"\<lambda> (channel_decrypt1_input_val_pattern). (channel_decrypt1_input_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR2_decrypt1_Input.channels\<^sup>\<Omega> \<rightarrow> def_Decrypt1_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Decrypt1_HLR_Input.SB.setter oo connector oo def_SecureProtocol_HLR2_decrypt1_Input.SB.getter }"


end

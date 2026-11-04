theory def_SecureProtocol_HLR2_encrypt1_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_HLR2_encrypt1.def_SecureProtocol_HLR2_encrypt1_Input bundle_Encrypt1_HLR.def_Encrypt1_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Data_Bool_Tuple tsyn stream) \<rightarrow> (Data_Bool_Tuple tsyn stream)" is
"\<lambda> (channel_encrypt1_input_val_pattern). (channel_encrypt1_input_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR2_encrypt1_Input.channels\<^sup>\<Omega> \<rightarrow> def_Encrypt1_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Encrypt1_HLR_Input.SB.setter oo connector oo def_SecureProtocol_HLR2_encrypt1_Input.SB.getter }"


end

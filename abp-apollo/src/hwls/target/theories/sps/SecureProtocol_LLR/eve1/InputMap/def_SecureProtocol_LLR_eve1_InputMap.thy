theory def_SecureProtocol_LLR_eve1_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_LLR_eve1.def_SecureProtocol_LLR_eve1_Input bundle_Eve1_HLR.def_Eve1_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Data_Bool_Tuple tsyn stream) \<rightarrow> (Data_Bool_Tuple tsyn stream)" is
"\<lambda> (channel_eve1_input_val_pattern). (channel_eve1_input_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_LLR_eve1_Input.channels\<^sup>\<Omega> \<rightarrow> def_Eve1_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Eve1_HLR_Input.SB.setter oo connector oo def_SecureProtocol_LLR_eve1_Input.SB.getter }"


end

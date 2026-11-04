theory def_SecureProtocol_HLR2_bob_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_HLR2_bob.def_SecureProtocol_HLR2_bob_Input bundle_Bob_HLR.def_Bob_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Data_Bool_Tuple tsyn stream) \<rightarrow> (Data_Bool_Tuple tsyn stream)" is
"\<lambda> (channel_bob_input_val_pattern). (channel_bob_input_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR2_bob_Input.channels\<^sup>\<Omega> \<rightarrow> def_Bob_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Bob_HLR_Input.SB.setter oo connector oo def_SecureProtocol_HLR2_bob_Input.SB.getter }"


end

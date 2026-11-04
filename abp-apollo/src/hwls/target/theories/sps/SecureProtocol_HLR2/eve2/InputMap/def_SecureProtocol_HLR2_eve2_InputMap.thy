theory def_SecureProtocol_HLR2_eve2_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_HLR2_eve2.def_SecureProtocol_HLR2_eve2_Input bundle_Eve2_HLR.def_Eve2_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(bool tsyn stream) \<rightarrow> (bool tsyn stream)" is
"\<lambda> (channel_eve2_input_val_pattern). (channel_eve2_input_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR2_eve2_Input.channels\<^sup>\<Omega> \<rightarrow> def_Eve2_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Eve2_HLR_Input.SB.setter oo connector oo def_SecureProtocol_HLR2_eve2_Input.SB.getter }"


end

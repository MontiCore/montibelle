theory def_SecureProtocol_LLR_connector
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_LLR_connector.def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input bundle_SecureProtocol_LLR_connector.def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream) \<rightarrow> (bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream)" is
"\<lambda> (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern). (channel_decrypt2_output_val_pattern, channel_input_val_pattern, channel_decrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_bob_output_val_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Output.SB.setter oo connector oo def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input.SB.getter }"


end

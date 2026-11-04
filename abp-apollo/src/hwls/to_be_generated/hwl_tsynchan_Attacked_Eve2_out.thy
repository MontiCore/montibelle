theory hwl_tsynchan_Attacked_Eve2_out
  imports
    sps_SecureProtocol_HLR2.def_SecureProtocol_HLR2
    bundle.ChannelConverterTypes

begin

instance def_SecureProtocol_HLR2_eve2_Output.channels :: "tsynchan"
  by(intro_classes, case_tac "c", simp_all)


instance def_SecureProtocol_HLR2_eve2_Output.channels :: "one_chan"
  by(intro_classes, auto)

definition def_SecureProtocol_HLR2_eve2_Output_untimed_sbgetter :: "def_SecureProtocol_HLR2_eve2_Output.channels untimed\<^sup>\<Omega> \<Rightarrow> M stream" where
  "def_SecureProtocol_HLR2_eve2_Output_untimed_sbgetter sb = sb \<^enum> (UNTIMED def_SecureProtocol_HLR2_eve2_Output.channel_eve2_output_val)"

end

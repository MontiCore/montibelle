theory hwl_tsynchan_Attacked_Decrypt2_out
  imports
    sps_SecureProtocol_HLR2.def_SecureProtocol_HLR2
    bundle.ChannelConverterTypes
begin

instance def_SecureProtocol_HLR2_decrypt2_Output.channels :: "tsynchan"
  by(intro_classes, case_tac "c", simp_all)


instance def_SecureProtocol_HLR2_decrypt2_Output.channels :: "one_chan"
  by(intro_classes, auto)

end

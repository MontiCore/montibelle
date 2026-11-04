theory hwl_tsynchan_Attacked_Bob_in
  imports
    sps_SecureProtocol_HLR2.def_SecureProtocol_HLR2
    bundle.ChannelConverterTypes
begin

instance def_SecureProtocol_HLR2_bob_Input.channels :: "tsynchan"
  by(intro_classes, case_tac "c", simp_all)

instance def_SecureProtocol_HLR2_bob_Input.channels :: "one_chan"
  by(intro_classes, auto)

end

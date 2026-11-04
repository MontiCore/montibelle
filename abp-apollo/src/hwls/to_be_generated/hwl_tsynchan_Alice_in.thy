theory hwl_tsynchan_Alice_in
  imports
    sps_SecureProtocol_HLR2.def_SecureProtocol_HLR2
    bundle.ChannelConverterTypes
begin

instance def_Alice_HLR_Input.channels :: "tsynchan"
  by(intro_classes, case_tac "c", simp_all)

instance def_Alice_HLR_Input.channels :: "one_chan"
  by(intro_classes, auto)

end

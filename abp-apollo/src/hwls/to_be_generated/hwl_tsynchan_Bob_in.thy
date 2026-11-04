theory hwl_tsynchan_Bob_in
  imports
    sps_SecureProtocol_HLR2.def_SecureProtocol_HLR2
    bundle.ChannelConverterTypes
begin

instance def_Bob_HLR_Input.channels :: "tsynchan"
  by(intro_classes, case_tac "c", simp_all)


instance def_Bob_HLR_Input.channels :: "one_chan"
  by(intro_classes, auto)

end

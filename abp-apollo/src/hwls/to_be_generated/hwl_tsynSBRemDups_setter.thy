theory hwl_tsynSBRemDups_setter
  imports
    move_to_core.hwl_tsynSBRemDups

    tsynchans
begin



lemma def_SecureProtocol_HLR2_alice_Output_tsynSBRemDups_setter:
  "tsynSBRemDups\<cdot>(def_SecureProtocol_HLR2_alice_Output.SB.setter\<cdot>s) = def_SecureProtocol_HLR2_alice_Output.sbsetter\<cdot>(tsynRemDups\<cdot>s)"
  apply(rule sb_eqI)
  apply(subst tsynSBRemDups_getCh)
  apply(subst def_SecureProtocol_HLR2_alice_Output.SB.setter_getch)+
  apply(subst def_SecureProtocol_HLR2_alice_Output.buildSB_def)+
  by(case_tac c, simp_all add: tsynMsgToMStream_tsynRemDup_toTsynMsgStream)


lemma def_SecureProtocol_HLR2_bob_Output_tsynSBRemDups_setter:
  "tsynSBRemDups\<cdot>(def_SecureProtocol_HLR2_bob_Output.SB.setter\<cdot>(s1, s2)) = def_SecureProtocol_HLR2_bob_Output.sbsetter\<cdot>((tsynRemDups\<cdot>s1, tsynRemDups\<cdot>s2))"
  apply(rule sb_eqI)
  apply(subst tsynSBRemDups_getCh)
  apply(subst def_SecureProtocol_HLR2_bob_Output.SB.setter_getch)+
  apply(subst def_SecureProtocol_HLR2_bob_Output.buildSB_def)+
  by(case_tac c, simp_all add: tsynMsgToMStream_tsynRemDup_toTsynMsgStream)



lemma def_SecureProtocol_HLR2_eve1_Output_tsynSBRemDups_setter:
  "tsynSBRemDups\<cdot>(def_SecureProtocol_HLR2_eve1_Output.SB.setter\<cdot>s) = def_SecureProtocol_HLR2_eve1_Output.sbsetter\<cdot>(tsynRemDups\<cdot>s)"
  apply(rule sb_eqI)
  apply(subst tsynSBRemDups_getCh)
  apply(subst def_SecureProtocol_HLR2_eve1_Output.SB.setter_getch)+
  apply(subst def_SecureProtocol_HLR2_eve1_Output.buildSB_def)+
  by(case_tac c, simp_all add: tsynMsgToMStream_tsynRemDup_toTsynMsgStream)


lemma def_SecureProtocol_HLR2_eve2_Input_tsynSBRemDups_setter:
  "tsynSBRemDups\<cdot>(def_SecureProtocol_HLR2_eve2_Input.SB.setter\<cdot>s) = def_SecureProtocol_HLR2_eve2_Input.sbsetter\<cdot>(tsynRemDups\<cdot>s)"
  apply(rule sb_eqI)
  apply(subst tsynSBRemDups_getCh)
  apply(subst def_SecureProtocol_HLR2_eve2_Input.SB.setter_getch)+
  apply(subst def_SecureProtocol_HLR2_eve2_Input.buildSB_def)+
  by(case_tac c, simp_all add: tsynMsgToMStream_tsynRemDup_toTsynMsgStream)

lemma def_SecureProtocol_HLR2_eve2_Output_tsynSBRemDups_setter:
  "tsynSBRemDups\<cdot>(def_SecureProtocol_HLR2_eve2_Output.SB.setter\<cdot>s) = def_SecureProtocol_HLR2_eve2_Output.sbsetter\<cdot>(tsynRemDups\<cdot>s)"
  apply(rule sb_eqI)
  apply(subst tsynSBRemDups_getCh)
  apply(subst def_SecureProtocol_HLR2_eve2_Output.SB.setter_getch)+
  apply(subst def_SecureProtocol_HLR2_eve2_Output.buildSB_def)+
  by(case_tac c, simp_all add: tsynMsgToMStream_tsynRemDup_toTsynMsgStream)

end

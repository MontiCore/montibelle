theory def_Bob_LLR
  imports
    (* Core *) tscomponent.TsLocale
    (* Gen  *) bundle_Bob_HLR.def_Bob_HLR_Input bundle_Bob_HLR.def_Bob_HLR_Output def_Bob_LLR_States
    (* Hwl  *)

begin




fun Bob_h :: "bool \<Rightarrow> (nat \<times> bool) tsyn \<Rightarrow> (bool \<times> (nat tsyn \<times> bool tsyn)) set" where
B1:   "Bob_h Ack Eps = {(Ack, (Eps, Eps))}" |
B2_3: "Bob_h Ack (TSynMsg pair) = (if snd pair = Ack 
            then {( \<not>Ack,(TSynMsg (fst pair), TSynMsg Ack))} 
            else {( Ack, (Eps, (TSynMsg (\<not>Ack))))})"


fun Receiver_LLR_h_v2 :: "(nat tsyn \<times> bool) \<Rightarrow> Data_Bool_Tuple tsyn \<Rightarrow> ((nat tsyn \<times> bool) \<times> (bool tsyn \<times> nat tsyn)) set" where
R1: "Receiver_LLR_h_v2 state Eps = {(state, (Eps, Eps))}" |
R2: "Receiver_LLR_h_v2 (d_state, b_state) (TSynMsg input_tuple) = 
     (if (d_state, b_state) = (TSynMsg (Data_Bool_Tuple_get_fst input_tuple), Data_Bool_Tuple_get_snd input_tuple) 
      then {((TSynMsg (Data_Bool_Tuple_get_fst input_tuple), Data_Bool_Tuple_get_snd input_tuple), 
             (TSynMsg (Data_Bool_Tuple_get_snd input_tuple), Eps))}
      else {((TSynMsg (Data_Bool_Tuple_get_fst input_tuple), Data_Bool_Tuple_get_snd input_tuple), 
             (TSynMsg (Data_Bool_Tuple_get_snd input_tuple), TSynMsg (Data_Bool_Tuple_get_fst input_tuple)))})"

definition Bob_init :: "(bool \<times> nat tsyn \<times> bool tsyn) set" where
"Bob_init = {(True,Eps,Eps)}"

definition Receiver_LLR_h_init :: "((nat tsyn \<times> bool) \<times> bool tsyn \<times> nat tsyn) set" where
"Receiver_LLR_h_init = {((Eps, True),(Eps, Eps))}"

interpretation behavior: tsStrongGen "(\<lambda> (). Receiver_LLR_h_v2)" "(\<lambda> (). Receiver_LLR_h_init)" def_Bob_HLR_Input.buildSBE def_Bob_HLR_Output.buildSBE
  by standard


ML \<open>structure def_Bob_LLR = struct
end\<close>

definition Sps :: "unit \<Rightarrow> (def_Bob_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Bob_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end



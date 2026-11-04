theory Requirement
  imports
    (* Gen  *) sps_Inverter_LLR1.def_Inverter_LLR1
               code_Inverter_LLR1.code_Inverter_LLR1 
               bundle_Inverter_HLR1.def_Inverter_HLR1_Input 
               bundle_Inverter_HLR1.def_Inverter_HLR1_Output
    (* Hwl  *)
begin

lemma Requirement:
  assumes "def_Inverter_HLR1_Output.sbgetter\<cdot>
             (code_Inverter_LLR1.execsem ((), (x, y), z, s)
             (def_Inverter_HLR1_Input.sbsetter\<cdot>channel_input_val_pattern)) = channel_output_val_pattern"
    shows "(channel_input_val_pattern = (<[EventMsg var_a, Tick]>)) \<longrightarrow> (channel_output_val_pattern = (<[Tick, EventMsg (Not var_a), Tick]>))"
  (* autosledgi *) oops

end

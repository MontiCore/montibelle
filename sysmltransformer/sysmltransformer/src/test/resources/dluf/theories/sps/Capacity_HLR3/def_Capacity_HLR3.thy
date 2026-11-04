theory def_Capacity_HLR3
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Capacity_HLR3.def_Capacity_HLR3_Input bundle_Capacity_HLR3.def_Capacity_HLR3_Output
    (* Hwl  *)

begin


definition assumption_0 :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> (var_cap) (channel_input_data_pattern) (channel_control_data_pattern, channel_output_data_pattern) .
    (((slen\<cdot>channel_input_data_pattern) = \<infinity>))"

definition assumption_1 :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> bool" where
"assumption_1 \<equiv> \<lambda> (var_cap) (channel_input_data_pattern) (channel_control_data_pattern, channel_output_data_pattern) .
    (\<forall> v \<in> (eValues\<cdot>channel_input_data_pattern).(Packet_get_size v < var_cap))"

definition assumption_2 :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> bool" where
"assumption_2 \<equiv> \<lambda> (var_cap) (channel_input_data_pattern) (channel_control_data_pattern, channel_output_data_pattern) .
    ((\<forall> t.((((slen\<cdot>(esnth (t + 1)\<cdot>channel_control_data_pattern)) = (slen\<cdot>(esnth t\<cdot>channel_input_data_pattern)))) \<or> ((CtrlEnum.NAK\<in>(sValues\<cdot>(esnth (t + 1)\<cdot>channel_control_data_pattern)))))) \<longrightarrow> (\<forall> t.((slen\<cdot>(esnth t\<cdot>channel_input_data_pattern)) > 0)))"

definition predicate_0 :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> (var_cap) (channel_input_data_pattern) (channel_control_data_pattern, channel_output_data_pattern) .
    (((slen\<cdot>(e2ustream\<cdot>channel_output_data_pattern)) = \<infinity>))"

definition causality :: "(Packet event stream) \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_data_pattern) (channel_control_data_pattern, channel_output_data_pattern) .
    strongpred (channel_input_data_pattern) (channel_control_data_pattern, channel_output_data_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output\<and> assumption_1 para input output\<and> assumption_2 para input output)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "(nat) \<Rightarrow> (def_Capacity_HLR3_Input.channels\<^sup>\<Omega> \<rightarrow> def_Capacity_HLR3_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_cap). {spf | spf. \<forall>sb.
wholePredicate (var_cap) (def_Capacity_HLR3_Input.SB.getter\<cdot>sb) (def_Capacity_HLR3_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

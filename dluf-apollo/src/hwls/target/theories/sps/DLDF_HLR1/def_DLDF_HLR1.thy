theory def_DLDF_HLR1
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_DLDF_HLR1.def_DLDF_HLR1_Input bundle_DLDF_HLR1.def_DLDF_HLR1_Output
    (* Hwl  *)

begin


definition assumption_0 :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> (var_cap1, var_cap2, var_cap3, var_cap4) (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern) .
    ((((((slen\<cdot>channel_input1_data_pattern) = \<infinity>) \<and> ((slen\<cdot>channel_input2_data_pattern) = \<infinity>)) \<and> ((slen\<cdot>channel_input3_data_pattern) = \<infinity>)) \<and> ((slen\<cdot>channel_input4_data_pattern) = \<infinity>)))"

definition assumption_1 :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"assumption_1 \<equiv> \<lambda> (var_cap1, var_cap2, var_cap3, var_cap4) (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern) .
    (\<forall> t.(((((slen\<cdot>(esnth t\<cdot>channel_input1_data_pattern)) > 0) \<and> ((slen\<cdot>(esnth t\<cdot>channel_input2_data_pattern)) > 0)) \<and> ((slen\<cdot>(esnth t\<cdot>channel_input3_data_pattern)) > 0)) \<and> ((slen\<cdot>(esnth t\<cdot>channel_input4_data_pattern)) > 0)))"

definition assumption_2 :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"assumption_2 \<equiv> \<lambda> (var_cap1, var_cap2, var_cap3, var_cap4) (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern) .
    (((((\<forall> v \<in> (eValues\<cdot>channel_input1_data_pattern).(Packet_get_size v < var_cap1)) \<and> (\<forall> v \<in> (eValues\<cdot>channel_input2_data_pattern).(Packet_get_size v < var_cap2))) \<and> (\<forall> v \<in> (eValues\<cdot>channel_input3_data_pattern).(Packet_get_size v < var_cap3))) \<and> (\<forall> v \<in> (eValues\<cdot>channel_input4_data_pattern).(Packet_get_size v < var_cap4))))"

definition predicate_0 :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> (var_cap1, var_cap2, var_cap3, var_cap4) (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern) .
    (((((((slen\<cdot>(e2ustream\<cdot>channel_output1_data_pattern)) = \<infinity>)) \<and> (((slen\<cdot>(e2ustream\<cdot>channel_output2_data_pattern)) = \<infinity>))) \<and> (((slen\<cdot>(e2ustream\<cdot>channel_output3_data_pattern)) = \<infinity>))) \<and> (((slen\<cdot>(e2ustream\<cdot>channel_output4_data_pattern)) = \<infinity>))))"

definition causality :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern) .
    strongpred (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output\<and> assumption_1 para input output\<and> assumption_2 para input output)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (def_DLDF_HLR1_Input.channels\<^sup>\<Omega> \<rightarrow> def_DLDF_HLR1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_cap1, var_cap2, var_cap3, var_cap4). {spf | spf. \<forall>sb.
wholePredicate (var_cap1, var_cap2, var_cap3, var_cap4) (def_DLDF_HLR1_Input.SB.getter\<cdot>sb) (def_DLDF_HLR1_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

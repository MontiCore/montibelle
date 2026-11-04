theory def_Scheduler_HLR2
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Scheduler_HLR2.def_Scheduler_HLR2_Input bundle_Scheduler_HLR2.def_Scheduler_HLR2_Output
    (* Hwl  *)

begin


definition assumption_0 :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> (var_capacity) (channel_input_data_pattern) (channel_output_data_pattern) .
    (((slen\<cdot>channel_input_data_pattern) = \<infinity>))"

definition assumption_1 :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"assumption_1 \<equiv> \<lambda> (var_capacity) (channel_input_data_pattern) (channel_output_data_pattern) .
    (\<forall> t.((slen\<cdot>(esnth t\<cdot>channel_input_data_pattern)) > 0))"

definition assumption_2 :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"assumption_2 \<equiv> \<lambda> (var_capacity) (channel_input_data_pattern) (channel_output_data_pattern) .
    (\<forall> v \<in> (eValues\<cdot>channel_input_data_pattern).(Packet_get_size v < var_capacity))"

definition predicate_0 :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> (var_capacity) (channel_input_data_pattern) (channel_output_data_pattern) .
    (((slen\<cdot>(e2ustream\<cdot>channel_output_data_pattern)) = \<infinity>))"

definition causality :: "(Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_data_pattern) (channel_output_data_pattern) .
    strongpred (channel_input_data_pattern) (channel_output_data_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "(nat) \<Rightarrow> (Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output\<and> assumption_1 para input output\<and> assumption_2 para input output)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "(nat) \<Rightarrow> (def_Scheduler_HLR2_Input.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_HLR2_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_capacity). {spf | spf. \<forall>sb.
wholePredicate (var_capacity) (def_Scheduler_HLR2_Input.SB.getter\<cdot>sb) (def_Scheduler_HLR2_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

theory def_Buffer_HLR3
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Buffer_HLR3.def_Buffer_HLR3_Input bundle_Buffer_HLR3.def_Buffer_HLR3_Output
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (channel_control_data_pattern, channel_input_data_pattern) (channel_output_data_pattern) .
    ((((slen\<cdot>channel_input_data_pattern) = \<infinity>) \<and> ((slen\<cdot>channel_control_data_pattern) = \<infinity>)))"

definition assumption_1 :: "unit \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"assumption_1 \<equiv> \<lambda> () (channel_control_data_pattern, channel_input_data_pattern) (channel_output_data_pattern) .
    (\<forall> t.((slen\<cdot>(esnth t\<cdot>channel_input_data_pattern)) > 0))"

definition predicate_0 :: "unit \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_control_data_pattern, channel_input_data_pattern) (channel_output_data_pattern) .
    ((\<forall> t.((((slen\<cdot>(esnth (t + 1)\<cdot>channel_control_data_pattern)) = (slen\<cdot>(esnth t\<cdot>channel_output_data_pattern)))) \<or> ((CtrlEnum.NAK\<in>(sValues\<cdot>(esnth (t + 1)\<cdot>channel_control_data_pattern)))))) \<longrightarrow> (\<forall> t.((slen\<cdot>(esnth t\<cdot>channel_output_data_pattern)) > 0)))"

definition predicate_1 :: "unit \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"predicate_1 \<equiv> \<lambda> () (channel_control_data_pattern, channel_input_data_pattern) (channel_output_data_pattern) .
    (((eValues\<cdot>channel_output_data_pattern)\<subseteq>(eValues\<cdot>channel_input_data_pattern)))"

definition causality :: "(CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_control_data_pattern, channel_input_data_pattern) (channel_output_data_pattern) .
    weakpred (channel_control_data_pattern, channel_input_data_pattern) (channel_output_data_pattern)"

lemmas predAndCausality_defs = predicate_0_def predicate_1_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output\<and> assumption_1 para input output)
      \<longrightarrow> (predicate_0 para input output \<and> predicate_1 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Buffer_HLR3_Input.channels\<^sup>\<Omega> \<rightarrow> def_Buffer_HLR3_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Buffer_HLR3_Input.SB.getter\<cdot>sb) (def_Buffer_HLR3_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

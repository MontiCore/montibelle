theory def_Sorter
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Sorter.def_Sorter_Input bundle_Sorter.def_Sorter_Output
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_maniacIn_data_pattern, channel_mirmisIn_data_pattern) (channel_prio1_data_pattern, channel_prio2_data_pattern, channel_prio3_data_pattern, channel_prio4_data_pattern) .
    (((slen\<cdot>channel_b1In_data_pattern) = \<infinity>))"

definition causality :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_maniacIn_data_pattern, channel_mirmisIn_data_pattern) (channel_prio1_data_pattern, channel_prio2_data_pattern, channel_prio3_data_pattern, channel_prio4_data_pattern) .
    strongpred (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_maniacIn_data_pattern, channel_mirmisIn_data_pattern) (channel_prio1_data_pattern, channel_prio2_data_pattern, channel_prio3_data_pattern, channel_prio4_data_pattern)"

lemmas predAndCausality_defs = causality_def

definition wholePredicate :: "unit \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output)
      \<longrightarrow> True)
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Sorter_Input.channels\<^sup>\<Omega> \<rightarrow> def_Sorter_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Sorter_Input.SB.getter\<cdot>sb) (def_Sorter_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

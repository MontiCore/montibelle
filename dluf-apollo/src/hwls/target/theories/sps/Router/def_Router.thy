theory def_Router
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Router.def_Router_Input bundle_Router.def_Router_Output
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (channel_input_data_pattern) (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_maniacOut_data_pattern, channel_mirmisOut_data_pattern) .
    (((slen\<cdot>channel_input_data_pattern) = \<infinity>))"

definition causality :: "(Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_data_pattern) (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_maniacOut_data_pattern, channel_mirmisOut_data_pattern) .
    strongpred (channel_input_data_pattern) (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_maniacOut_data_pattern, channel_mirmisOut_data_pattern)"

lemmas predAndCausality_defs = causality_def

definition wholePredicate :: "unit \<Rightarrow> (Packet event stream) \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output)
      \<longrightarrow> True)
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Router_Input.channels\<^sup>\<Omega> \<rightarrow> def_Router_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Router_Input.SB.getter\<cdot>sb) (def_Router_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

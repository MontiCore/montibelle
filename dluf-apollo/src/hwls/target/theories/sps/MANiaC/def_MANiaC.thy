theory def_MANiaC
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_MANiaC.def_MANiaC_Input bundle_MANiaC.def_MANiaC_Output
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (channel_input_data_pattern) (channel_output_data_pattern) .
    (((slen\<cdot>channel_input_data_pattern) = \<infinity>))"

definition causality :: "(Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_data_pattern) (channel_output_data_pattern) .
    strongpred (channel_input_data_pattern) (channel_output_data_pattern)"

lemmas predAndCausality_defs = causality_def

definition wholePredicate :: "unit \<Rightarrow> (Packet event stream) \<Rightarrow> (Packet event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output)
      \<longrightarrow> True)
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_MANiaC_Input.channels\<^sup>\<Omega> \<rightarrow> def_MANiaC_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_MANiaC_Input.SB.getter\<cdot>sb) (def_MANiaC_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

theory def_Bob_HLR
  imports
    (* Core *) sps.SPSComp
    (* Gen  *) bundle_Bob_HLR.def_Bob_HLR_Input bundle_Bob_HLR.def_Bob_HLR_Output
    (* Hwl  *)

begin


definition causality :: "((nat\<times>bool) tsyn stream) \<Rightarrow> (bool tsyn stream \<times> string tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_control_val_pattern, channel_output_val_pattern) .
    strongpred (channel_input_val_pattern) (channel_control_val_pattern, channel_output_val_pattern)"

lemmas predAndCausality_defs = causality_def

definition wholePredicate :: "unit \<Rightarrow> ((nat\<times>bool) tsyn stream) \<Rightarrow> (bool tsyn stream \<times> string tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> True)
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Bob_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Bob_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Bob_HLR_Input.SB.getter\<cdot>sb) (def_Bob_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

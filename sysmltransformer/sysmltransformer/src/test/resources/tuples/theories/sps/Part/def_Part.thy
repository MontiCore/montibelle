theory def_Part
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Part.def_Part_Input bundle_Part.def_Part_Output
    (* Hwl  *)

begin


definition causality :: "((bool\<times>bool) event stream) \<Rightarrow> ((bool\<times>bool) event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_output_val_pattern) .
    strongpred (channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = causality_def

definition wholePredicate :: "unit \<Rightarrow> ((bool\<times>bool) event stream) \<Rightarrow> ((bool\<times>bool) event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> True)
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Part_Input.channels\<^sup>\<Omega> \<rightarrow> def_Part_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Part_Input.SB.getter\<cdot>sb) (def_Part_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

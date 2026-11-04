theory def_BoolInverter
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) hwl_Dummy.hwl_Dummy bundle_BoolInverter.def_BoolInverter_Output
    (* Hwl  *)

begin


definition predicate_0 :: "unit \<Rightarrow> (bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    ((channel_input_val_pattern = (<[EventMsg True]>)) \<longrightarrow> (channel_output_val_pattern = (<[EventMsg False]>)))"

definition causality :: "(bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_output_val_pattern) .
    strongpred (channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_BoolInverter_Input.channels\<^sup>\<Omega> \<rightarrow> def_BoolInverter_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_BoolInverter_Input.SB.getter\<cdot>sb) (def_BoolInverter_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

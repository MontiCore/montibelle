theory def_Inverter_HLR2
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Inverter_HLR1.def_Inverter_HLR1_Input bundle_Inverter_HLR1.def_Inverter_HLR1_Output
    (* Hwl  *)

begin


definition predicate_0 :: "unit \<Rightarrow> (bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    (\<forall> k.(channel_input_val_pattern = (sntimes k (<[EventMsg True]>))) \<longrightarrow> (channel_output_val_pattern = (sntimes k (<[EventMsg False]>))))"

definition causality :: "(bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_output_val_pattern) .
    strongpred (channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Inverter_HLR1_Input.channels\<^sup>\<Omega> \<rightarrow> def_Inverter_HLR1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Inverter_HLR1_Input.SB.getter\<cdot>sb) (def_Inverter_HLR1_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

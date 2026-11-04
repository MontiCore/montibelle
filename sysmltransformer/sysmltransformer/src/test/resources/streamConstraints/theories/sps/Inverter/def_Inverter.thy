theory def_Inverter
  imports
    (* Core *) sps.SPSComp
    (* Gen  *) bundle_Inverter.def_Inverter_Input bundle_Inverter.def_Inverter_Output
    (* Hwl  *)

begin


definition predicate_0 :: "unit \<Rightarrow> (bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_i_val_pattern) (channel_o_val_pattern) .
    ((channel_o_val_pattern = tsynMap (\<lambda> b. \<not>(b))\<cdot>channel_i_val_pattern))"

definition causality :: "(bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_i_val_pattern) (channel_o_val_pattern) .
    strongpred (channel_i_val_pattern) (channel_o_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Inverter_Input.channels\<^sup>\<Omega> \<rightarrow> def_Inverter_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Inverter_Input.SB.getter\<cdot>sb) (def_Inverter_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

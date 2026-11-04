theory def_Bob_HLR
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Bob_HLR.def_Bob_HLR_Input bundle_Bob_HLR.def_Bob_HLR_Output
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (Data_Bool_Tuple tsyn stream) \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_control_val_pattern, channel_output_val_pattern) .
    (True)"

definition predicate_0 :: "unit \<Rightarrow> (Data_Bool_Tuple tsyn stream) \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_control_val_pattern, channel_output_val_pattern) .
    channel_control_val_pattern = \<up> Eps \<Zcat> (tsynProjSnd oo (smap (map_tsyn Data_Bool_Tuple2tuple)))\<cdot>(channel_input_val_pattern)"

definition assumption_1 :: "unit \<Rightarrow> (Data_Bool_Tuple tsyn stream) \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> bool" where
"assumption_1 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_control_val_pattern, channel_output_val_pattern) .
    True"

definition predicate_1 :: "unit \<Rightarrow> (Data_Bool_Tuple tsyn stream) \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> bool" where
"predicate_1 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_control_val_pattern, channel_output_val_pattern) .
    channel_output_val_pattern = \<up> Eps \<Zcat> ((smap (map_tsyn Data_Bool_Tuple_get_fst)) oo tsynRemDups)\<cdot>(channel_input_val_pattern)"

definition causality :: "(Data_Bool_Tuple tsyn stream) \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_control_val_pattern, channel_output_val_pattern) .
    strongpred (channel_input_val_pattern) (channel_control_val_pattern, channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (Data_Bool_Tuple tsyn stream) \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output)
      \<longrightarrow> (predicate_0 para input output))
  \<and> ((wellformed input\<and> assumption_1 para input output)
      \<longrightarrow> (predicate_1 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Bob_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Bob_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Bob_HLR_Input.SB.getter\<cdot>sb) (def_Bob_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

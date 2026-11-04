theory EventBasedSpecification
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) io.EventInput io.EventOutput
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (beInChannel_pattern) (beOutChannel_pattern) .
    (True)"

definition predicate_0 :: "unit \<Rightarrow> (bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (beInChannel_pattern) (beOutChannel_pattern) .
    (True)"

definition predicate_1 :: "unit \<Rightarrow> (bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"predicate_1 \<equiv> \<lambda> () (beInChannel_pattern) (beOutChannel_pattern) .
    (((snth 0 (esnth 5\<cdot>beInChannel_pattern)) = False))"

definition causality :: "(bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (beInChannel_pattern) (beOutChannel_pattern) .
    strongpred (beInChannel_pattern) (beOutChannel_pattern)"

lemmas predAndCausality_defs = predicate_0_def predicate_1_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output)
      \<longrightarrow> (predicate_0 para input output \<and> predicate_1 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (EventInput.channels\<^sup>\<Omega> \<rightarrow> EventOutput.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (EventInput.SB.getter\<cdot>sb) (EventOutput.SB.getter\<cdot>(spf\<cdot>sb))}"


end

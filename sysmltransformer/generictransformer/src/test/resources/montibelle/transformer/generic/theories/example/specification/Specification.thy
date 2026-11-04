theory Specification
  imports
    (* Core *) sps.SPSComp
    (* Gen  *) io.Input io.Output
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) .
    (True)"

definition predicate_0 :: "unit \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) .
    (True)"

definition predicate_1 :: "unit \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> bool" where
"predicate_1 \<equiv> \<lambda> () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) .
    ((snth 5 bInChannel_pattern) = (TSynMsg False))"

definition causality :: "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) .
    strongpred (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"

lemmas predAndCausality_defs = predicate_0_def predicate_1_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output)
      \<longrightarrow> (predicate_0 para input output \<and> predicate_1 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (Input.channels\<^sup>\<Omega> \<rightarrow> Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (Input.SB.getter\<cdot>sb) (Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end

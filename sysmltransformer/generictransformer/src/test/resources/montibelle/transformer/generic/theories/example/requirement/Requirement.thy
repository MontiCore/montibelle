theory Requirement
  imports
    (* Gen *) specification.Specification
    (* Hwl  *)

begin


fun RequirementFun::"unit \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow> bool" where
"RequirementFun () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) = ((snth 5 bInChannel_pattern) = TSynMsg False)"

lemma Requirement:
  assumes "spf\<in> Sps ()"
      and "inputSB = Input.SB.setter\<cdot>(natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)"
      and "(natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) = Output.SB.getter\<cdot>(spf\<cdot>(inputSB))"
  shows "RequirementFun () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) = True"
  apply(auto simp add: assms)
  (* autosledgi *) oops


end

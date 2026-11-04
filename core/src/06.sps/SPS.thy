theory SPS

imports spf.SPF
begin


      section \<open>Stream Processing Specification\<close> text\<open>\label{sec:sps}\<close>
text\<open>For the definition of \gls{sps} we use the \<open>set\<close> datatype 
  already included in isabelle. A underspecified component with the input channels
\<open>'input\<close> and the output channels \<open>'output\<close> has the signature: 
  \<open>('input\<^sup>\<Omega> \<rightarrow> 'output\<^sup>\<Omega>) set\<close>\<close>




lemma spsref_empty_out:
  fixes F:: "('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set"
    and G:: "('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set"
assumes "G = {} \<Longrightarrow> F = {}"
    and "chDomEmpty TYPE('out)"
  shows "F \<subseteq> G"
proof (cases "F = {}", simp, rule subsetI)
  fix spf
  assume asm: "spf \<in> F"
  assume asm2: "F \<noteq> {}"
  obtain spf2 where spf2_in: "spf2 \<in> G"
    using assms(1) asm2 by blast
  have spf_eq: "spf = spf2"
    apply(rule cfun_eqI, rule sb_eqI)
    using assms(2) by blast
  show "spf \<in> G"
    apply(subst spf_eq)
    using spf2_in by blast
qed

end

theory SpecificationInstance3
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Instance3Input io.Instance3Output specification.Specification connector.InputMap3 connector.OutputMap3
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (Instance3Input.channels\<^sup>\<Omega> \<rightarrow> Instance3Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). InputMap3.Sps () \<then> Specification.Sps () \<then> OutputMap3.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> Specification.Sps () \<Longrightarrow> P (Input.SB.getter\<cdot>sb) (Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (Instance3Input.SB.getter\<cdot>sb) (Instance3Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def InputMap3.Sps_def OutputMap3.Sps_def
    oo_def InputMap3.connector.rep_eq OutputMap3.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis Input.SB.get_set)


end

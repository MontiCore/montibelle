theory SpecificationInstance2
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Instance2Input io.Instance2Output specification.Specification connector.InputMap2 connector.OutputMap2
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (Instance2Input.channels\<^sup>\<Omega> \<rightarrow> Instance2Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). InputMap2.Sps () \<then> Specification.Sps () \<then> OutputMap2.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> Specification.Sps () \<Longrightarrow> P (Input.SB.getter\<cdot>sb) (Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (Instance2Input.SB.getter\<cdot>sb) (Instance2Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def InputMap2.Sps_def OutputMap2.Sps_def
    oo_def InputMap2.connector.rep_eq OutputMap2.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis Input.SB.get_set)


end

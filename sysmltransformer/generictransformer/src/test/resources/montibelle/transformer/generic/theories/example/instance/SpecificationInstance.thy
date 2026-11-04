theory SpecificationInstance
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Instance1Input io.Instance1Output specification.Specification connector.InputMap connector.OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (Instance1Input.channels\<^sup>\<Omega> \<rightarrow> Instance1Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). InputMap.Sps () \<then> Specification.Sps () \<then> OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> Specification.Sps () \<Longrightarrow> P (Input.SB.getter\<cdot>sb) (Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (Instance1Input.SB.getter\<cdot>sb) (Instance1Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def InputMap.Sps_def OutputMap.Sps_def
    oo_def InputMap.connector.rep_eq OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis Input.SB.get_set)


end

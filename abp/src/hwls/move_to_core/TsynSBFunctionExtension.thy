theory TsynSBFunctionExtension
  imports bundle.TsynSBFunction hwl_core_ext
begin

theorem tsynSBlen_le_rule:
  fixes sba::"'ca::{tsynchan}\<^sup>\<Omega>"
  fixes sbb::"'cb::{tsynchan}\<^sup>\<Omega>"
  fixes ca::"'ca"
  fixes cb::"'cb"
  assumes "\<not>chDomEmpty TYPE('ca)"
      and "\<not>chDomEmpty TYPE('cb)"
      and "\<And>ca'. tsynLenM\<cdot>(sba  \<^enum>  ca) \<le> tsynLenM\<cdot>(sba  \<^enum>  ca')"
      and "\<And>cb'. tsynLenM\<cdot>(sbb  \<^enum>  cb) \<le> tsynLenM\<cdot>(sbb  \<^enum>  cb')"
      and "tsynLenM\<cdot>(sba  \<^enum>  ca) \<le> tsynLenM\<cdot>(sbb  \<^enum>  cb)"
  shows "tsynSBlen sba \<le> tsynSBlen sbb"
proof-
  have lhs: "(LEAST n::lnat. \<exists>c::'ca. n = tsynLenM\<cdot>(sba  \<^enum>  c)) = tsynLenM\<cdot>(sba  \<^enum>  ca) "
    by (smt LeastI Least_le nle_le assms)

  have rhs: "(LEAST n::lnat. \<exists>c::'cb. n = tsynLenM\<cdot>(sbb  \<^enum>  c)) = tsynLenM\<cdot>(sbb  \<^enum>  cb)"
    by (smt LeastI Least_le nle_le assms)

  show ?thesis
    by(auto simp add: tsynSBlen_def assms lhs rhs)
qed

lemma
  totsynmsgstream_tsynmsgtomstream:
  assumes "toTsynMsgStream\<cdot>sa = sb"
    and "sValues\<cdot>sa \<subseteq> range (Timed \<circ> Tsyn)"
  shows "sa = tsynMsgToMStream\<cdot>sb"
proof-
  obtain sb where sb_in: "sa = smap (Timed o Tsyn)\<cdot>sb"
    using assms(2) smap_obtainin by blast

  show ?thesis
    apply(subst assms(1)[symmetric])
    apply(simp add: toTsynMsgStream_def tsynMsgToMStream_def)
    apply(subst(2) sb_in)
    apply(simp add: smaps2smap)
    by(simp add: sb_in)
qed




definition is_lifted_stream_fn :: "('a::{chan}\<^sup>\<Omega> \<rightarrow> 'a\<^sup>\<Omega>) \<Rightarrow> (M stream \<rightarrow> M stream) \<Rightarrow> bool" where
  "is_lifted_stream_fn sbFn sFn \<equiv> \<forall>sb c. (sbFn\<cdot>sb) \<^enum> c = sFn\<cdot>(sb \<^enum> c)"

lemma is_lifted_stream_fn_apply: "is_lifted_stream_fn sbFn sFn \<Longrightarrow> (sbFn\<cdot>sb) \<^enum> c = sFn\<cdot>(sb \<^enum> c)"
  by(simp add: is_lifted_stream_fn_def)


lemma is_lifted_stream_fn_conc:
  assumes "is_lifted_stream_fn F f"
      and "is_lifted_stream_fn G g"
    shows "is_lifted_stream_fn (F oo G) (f oo g)"
  using assms by(auto simp add: is_lifted_stream_fn_def)


definition is_lifted_tsyn_stream_fn :: "('a::{chan}\<^sup>\<Omega> \<rightarrow> 'a\<^sup>\<Omega>) \<Rightarrow> (msg tsyn stream \<rightarrow> msg tsyn stream) \<Rightarrow> bool" where
  "is_lifted_tsyn_stream_fn sbFn sFn \<equiv> is_lifted_stream_fn sbFn (tsynMsgToMStream oo sFn oo toTsynMsgStream)"

lemma is_lifted_tsyn_stream_fn_conc:
  assumes "is_lifted_tsyn_stream_fn F f"
      and "is_lifted_tsyn_stream_fn G g"
    shows "is_lifted_tsyn_stream_fn (F oo G) (f oo g)"
proof-
  have 1: "is_lifted_stream_fn F (tsynMsgToMStream oo f oo toTsynMsgStream)"
    using assms(1) is_lifted_tsyn_stream_fn_def by blast
  have 2: "is_lifted_stream_fn G (tsynMsgToMStream oo g oo toTsynMsgStream)"
    using assms(2) is_lifted_tsyn_stream_fn_def by blast

  show ?thesis
    apply(subst is_lifted_tsyn_stream_fn_def)
    apply(insert is_lifted_stream_fn_conc[OF 1 2])
    by (simp add: oo_def tsynMsgToMStream_def toTsynMsgStream_def smaps2smap)
qed

lemma toTsynMsgStream_smap_Timed_Tsyn: "toTsynMsgStream\<cdot>(smap (Timed \<circ> Tsyn)\<cdot>s) = s"
  by(simp add: toTsynMsgStream_def smaps2smap)

lemma toTsynMsgStream_smap_Timed_Tsyn_f: "toTsynMsgStream\<cdot>(smap (Timed \<circ> Tsyn \<circ> f)\<cdot>s) = smap f\<cdot>s"
  by(simp add: toTsynMsgStream_def smaps2smap)

lemma toTsynMsgStream_tsynMsgToMStream_id[simp]: "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>s) = s"
  by (simp add: toTsynMsgStream_smap_Timed_Tsyn tsynMsgToMStream_def)



theorem tsynSBlen_rule_liftedSpf:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
    and f:: "M stream \<rightarrow> M stream"
  assumes "\<not>chDomEmpty TYPE('cs)" 
      and "\<And>c. k \<le> tsynLenM\<cdot>(f\<cdot>(sb \<^enum> c))"
      and "\<exists>c. tsynLenM\<cdot>(f\<cdot>(sb \<^enum> c)) = k"
      and "is_lifted_stream_fn F f"
    shows "tsynSBlen (F\<cdot>sb) = k"
  apply(rule tsynSBlen_rule)
    apply(simp add: assms)
   apply(insert is_lifted_stream_fn_apply[OF assms(4)])
  using assms(2) apply presburger
  apply(insert is_lifted_stream_fn_apply[OF assms(4)])
  using assms(3) by presburger

theorem tsynSBlen_rule_liftedTsynSpf:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
    and f:: "msg tsyn stream \<rightarrow> msg tsyn stream"
  assumes "\<not>chDomEmpty TYPE('cs)" 
      and "\<And>c. k \<le> tsynLen\<cdot>(f\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c)))"
      and "\<exists>c. tsynLen\<cdot>(f\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))) = k"
      and "is_lifted_tsyn_stream_fn F f"
    shows "tsynSBlen (F\<cdot>sb) = k"
  apply(rule tsynSBlen_rule)
    apply(simp add: assms)
   apply(insert is_lifted_stream_fn_apply[OF assms(4)[simplified is_lifted_tsyn_stream_fn_def]])
   apply (simp add: assms(2) tsynLenM_def)
  apply(insert is_lifted_stream_fn_apply[OF assms(4)[simplified is_lifted_tsyn_stream_fn_def]])
  by (metis assms(3) cfcomp2 toTsynMsgStream_tsynMsgToMStream_id tsynLenM_def)

end

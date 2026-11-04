theory SPSFun

imports SPS SPSComp SPSIO
begin



theorem spsimage_io: 
  "spsIO(f ` sps) = {(sb, (f spf)\<cdot>sb) | sb spf. spf\<in>sps}"
  by(auto simp add: spsIO_def)


definition spsRt::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set" where
"spsRt sps = spsCompSeq sps {sbRt}"



theorem spsrt_apply: assumes "f \<in> sps"
  shows "sbRt oo f \<in> (spsRt sps)"
  by(auto simp add: spsRt_def spsCompSeq_def assms oo_def spfCompSeq_def)


theorem spsrt_set: "spsRt sps = {sbRt oo f | f. f \<in> sps}"
  by(simp add: spsRt_def spsCompSeq_def spfCompSeq_def oo_def)

theorem spsrt_io: 
  "spsIO (spsRt sps) = {(sb, sbRt\<cdot>(spf\<cdot>sb)) | sb spf. spf\<in>sps}"
  apply(simp add: spsIO_def spsRt_def spsCompSeq_def spfCompSeq_def)
  apply auto[1]
  by force

lemma spsrt_io_h: 
  "spsIO (spsRt sps) = (\<lambda> x. (fst x, sbRt\<cdot>(snd x))) ` spsIO(sps)"
  apply(simp add: spsrt_io)
  by(auto simp add: spsIO_def image_Collect)


theorem spsrt_complete: 
  "spsIO(spsComplete (spsRt f)) = spsIO(spsRt (spsComplete f))"
  by(simp add: spscomplete_io spsrt_io_h)


theorem spsrt_mono: assumes "sps1 \<subseteq> sps2"  
  shows "spsRt sps1 \<subseteq> spsRt sps2"
  apply (simp add: spsRt_def spsCompSeq_def spfCompSeq_def oo_def assms image_mono)
  using assms by force


theorem spsrt_consistent: assumes "spsIsConsistent sps"  
  shows "spsIsConsistent (spsRt sps)"
  by (metis assms insert_not_empty spsIsConsistent_def spsRt_def spscfcomp_consistent)


lemma sbrt_len_h1: "x \<noteq> \<epsilon> \<Longrightarrow> lnsuc\<cdot>(#(sdrop (Suc n)\<cdot>x)) \<le> #x"
  apply(simp add: sdrop_def)
  apply(induction n)
  using eq_iff srt_decrements_length apply auto[1]
  by (metis (mono_tags, lifting) dual_order.trans iterate_Suc less_lnsuc srt_decrements_length stream.sel_rews(2))

lemma sbrt_len_h2: "(x \<^enum> c) \<noteq> \<epsilon> \<Longrightarrow> lnsuc\<cdot>(#(sbRt\<cdot>x \<^enum>  c)) \<le> #(x \<^enum>  c)"
  apply(simp add: sbdrop_insert sbgetch_insert2) 
  using sbrt_len_h1 sbdrop_well by (metis Abs_lsb_inverse mem_Collect_eq sbgetchid sbtypecast_well)

lemma sbrt_len_h3: "#x > 0 \<and> \<not>chDomEmpty TYPE('a) \<Longrightarrow> \<forall>c::'a. (x \<^enum> c) \<noteq> \<epsilon>"
  using dual_order.strict_implies_not_eq sbleast2sblenempty sbnleast_mex by blast

theorem sbrt_len: "#x > 0 \<Longrightarrow> lnsuc\<cdot>(#(sbRt\<cdot>x)) \<le> #x"
  apply(cases "chDomEmpty TYPE('a)")
  apply simp
  by (metis lnat_po_eq_conv neq_iff sbecons_eq sbecons_len)

lemma spsrt_len_h2:
  assumes "g \<in>  sps"
  shows "\<exists> f \<in> (spsRt sps). \<forall> b. f\<cdot>b = sbRt\<cdot>(g\<cdot>b)"
  using assms cfcomp2 spsrt_apply by blast

lemma spsrt_len_h1:
  assumes "f \<in> (spsRt sps)"
  shows "\<exists> g \<in> sps. \<forall> b. f\<cdot>b = sbRt\<cdot>(g\<cdot>b)"
proof - 
  have "spsRt sps = {sbRt oo f | f. f \<in> sps}"
    by(simp add: spsRt_def spsCompSeq_def spfCompSeq_def oo_def)
  thus ?thesis
    using assms by auto
qed


theorem spsrt_len: assumes "\<And>spf sb. spf\<in>sps \<Longrightarrow> lnsuc\<cdot>(#sb) \<le> #(spf\<cdot>sb)"
  shows "\<And>spf sb. spf\<in> (spsRt sps) \<Longrightarrow> #sb \<le> #(spf\<cdot>sb)"
proof -
  fix spf sb
  assume a1: "spf\<in> (spsRt sps)"
  obtain g where o1: "g\<in>sps" and o2: "(\<forall> b. spf\<cdot>b = sbRt\<cdot>(g\<cdot>b))"
    using a1 spsrt_len_h1 by blast
  have "lnsuc\<cdot>(#sb) \<le> #(g\<cdot>sb)"
    using assms o1 by blast
  thus "#sb \<le> #(spf\<cdot>sb)"
    apply(simp add: o2)
    by (metis One_nat_def lnmin_eqasmthmin lnsuc_lnle_emb lnsuc_neq_0_rev sbecons_eq sbecons_len strict_lnmin_snd)
qed

lemma spsrt_len2: assumes "f \<in> (spsRt sps)"
  shows "\<exists> g\<in>sps. \<forall> x. #(g\<cdot>x) > 0 \<longrightarrow> lnsuc\<cdot>(#(f\<cdot>x)) \<le> #(g\<cdot>x)"
proof - 
  obtain g where "g\<in>sps" and "(\<forall> b. f\<cdot>b = sbRt\<cdot>(g\<cdot>b))"
    using assms spsrt_len_h1 by blast
  then have "\<forall> x. #(g\<cdot>x) > 0 \<longrightarrow> lnsuc\<cdot>(#(f\<cdot>x)) \<le> #(g\<cdot>x)"
    using sbrt_len by auto
  then show ?thesis
    using \<open>(g::'a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>) \<in> (sps::('a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>) set)\<close> by blast
qed



end

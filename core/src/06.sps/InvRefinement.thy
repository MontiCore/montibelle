theory InvRefinement
  imports SPSComp
begin

default_sort chan



definition invRefined::"('in \<Rightarrow> bool) \<Rightarrow> ('in::cpo \<rightarrow> 'out::cpo) set \<Rightarrow> 
  ('in \<rightarrow> 'out) set \<Rightarrow> bool" where
"invRefined I F G = (\<forall>f\<in>F. \<exists>g\<in>G. (\<forall>sb. I sb \<longrightarrow> f\<cdot>sb = g\<cdot>sb))"

abbreviation invRefinement_abrev :: " ('in::cpo \<rightarrow> 'out::cpo) set \<Rightarrow> ('in \<Rightarrow> bool) \<Rightarrow>  ('in \<rightarrow> 'out) set \<Rightarrow> bool"
 ( "_ \<subseteq>\<^sub>_ _" 200) where "A \<subseteq>\<^sub>I B \<equiv> invRefined I A B"

abbreviation invEquality_abrev :: " ('in::cpo \<rightarrow> 'out::cpo) set \<Rightarrow> ('in \<Rightarrow> bool) \<Rightarrow>  ('in \<rightarrow> 'out) set \<Rightarrow> bool"
 ( "_ =\<^sub>_ _" 200) where "A =\<^sub>I B \<equiv> (A \<subseteq>\<^sub>I B) \<and> (B \<subseteq>\<^sub>I A)"

definition invRefined2::"('in\<^sup>\<Omega> \<Rightarrow> bool) \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set \<Rightarrow> 
  ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set \<Rightarrow> bool" where
"invRefined2 I F G = (\<forall>f\<in>F. \<forall>sb. \<exists>g\<in>G. (I sb \<longrightarrow> f\<cdot>sb = g\<cdot>sb))"



lemma invRefinedI:"(\<And>f. (f\<in>F \<Longrightarrow> (\<exists>g. g \<in> G \<and> (\<forall>sb. I sb \<longrightarrow> f\<cdot>sb = g\<cdot>sb)))) \<Longrightarrow> F \<subseteq>\<^sub>I G"
  unfolding invRefined_def
  by auto
  
lemma invrefine2: "invRefined I F G \<Longrightarrow> invRefined2 I F G"
  apply(simp add: invRefined_def invRefined2_def)
  by blast

lemma invrefine_complete: "invRefined I F (spsComplete G) \<Longrightarrow> invRefined2 I F G"
  apply(auto simp add: invRefined_def invRefined2_def spsComplete_def)[1]
  by fastforce

lemma shows "invRefined2 I F G \<Longrightarrow> invRefined I F (spsComplete G)"
  oops

lemma invref_reflexive [simp]: "A \<subseteq>\<^sub>I A"
  using invRefined_def by blast

lemma ref_impl_invref: "A \<subseteq> B \<Longrightarrow> A \<subseteq>\<^sub>I B"
  by(auto simp add: invRefined_def)

lemma invref_trans: "A \<subseteq>\<^sub>I B \<Longrightarrow> B \<subseteq>\<^sub>I C \<Longrightarrow> A \<subseteq>\<^sub>I C"
  by(auto simp add: invRefined_def)

lemma invref_trans1: "A \<subseteq> B \<Longrightarrow> B \<subseteq>\<^sub>I C \<Longrightarrow> A \<subseteq>\<^sub>I C"
  by(auto simp add: invRefined_def)

lemma invref_trans2: "A \<subseteq>\<^sub>I B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<subseteq>\<^sub>I C"
  by (meson invref_reflexive invref_trans invref_trans1)

lemma invref_true_iff: "invRefined (\<lambda>_. True) F G \<longleftrightarrow> F \<subseteq> G"
  apply(auto simp add: invRefined_def)[1]
  using cfun_eqI by blast

lemma inveq_true_iff: "invEquality_abrev F (\<lambda>_. True) G \<longleftrightarrow> F = G"
  by (simp add: dual_order.eq_iff invref_true_iff)

lemma invEqualityD1: "A =\<^sub>L B \<Longrightarrow> A \<subseteq>\<^sub>L B"
  by simp

lemma invEqualityD2: "A =\<^sub>L B \<Longrightarrow> B \<subseteq>\<^sub>L A"
  by simp

lemma inveq_sym: "F =\<^sub>I G \<Longrightarrow> G =\<^sub>I F"
  by blast

lemma eq_inveq: "F = G \<Longrightarrow> F =\<^sub>I G"
  by simp

lemma inveq_trans: "A =\<^sub>I B \<Longrightarrow> B =\<^sub>I C \<Longrightarrow> A =\<^sub>I C"
  by(auto simp add: invRefined_def)

lemma invrefine_singelton_mp:
assumes "F \<subseteq>\<^sub>I {g}"
    and "f \<in> F"
    and "I sb"
  shows "f\<cdot>sb = g\<cdot>sb"
  using assms by(auto simp add: invRefined_def)


lemma spsconvref_inv: 
assumes "\<And> sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "S1 \<subseteq>\<^sub>J S2"
  shows"spsConvert\<cdot>S1 \<subseteq>\<^sub>I spsConvert\<cdot>S2"
  using assms apply(simp add: spsConvert.rep_eq invRefined_def spfconvert_apply)
  by metis

lemma spsconveq_inv: 
assumes "\<And> sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "S1 =\<^sub>J S2"
  shows"spsConvert\<cdot>S1 =\<^sub>I spsConvert\<cdot>S2"
  using assms apply(simp add: spsConvert.rep_eq invRefined_def spfconvert_apply)
  by metis


lemma invrefine_compseq_left:
assumes "F' \<subseteq>\<^sub>I F"
  shows "(F' \<then> G) \<subseteq>\<^sub>I (F \<then> G)"
  using assms apply(simp add: seqcomp_insert invRefined_def)
  using cfun_eqI by fastforce

lemma inveq_compseq_left:
assumes "F' =\<^sub>I F"
  shows "(F' \<then> G) =\<^sub>I (F \<then> G)"
  using invrefine_compseq_left assms by blast

lemma invrefine_compseq_right:
assumes "G' \<subseteq>\<^sub>J G"
    and "\<And>f sb. f \<in> F \<Longrightarrow> I sb  \<Longrightarrow> J (f\<cdot>sb)"
  shows "(F \<then> G') \<subseteq>\<^sub>I (F \<then> G)"
  using assms apply(simp add: seqcomp_insert invRefined_def)
  using cfun_eqI by fastforce

lemma inveq_compseq_right:
assumes "G' =\<^sub>J G"
    and "\<And>f sb. f \<in> F \<Longrightarrow> I sb  \<Longrightarrow> J (f\<cdot>sb)"
  shows "(F \<then> G') =\<^sub>I (F \<then> G)"
  using invrefine_compseq_right assms by blast

lemma inveq_compseq:
assumes "F' =\<^sub>I F"
    and "G' =\<^sub>J G"
    and "\<And>f sb. f \<in> F' \<Longrightarrow> I sb  \<Longrightarrow> J (f\<cdot>sb)"
  shows "(F' \<then> G') =\<^sub>I (F \<then> G)"
  apply standard
  by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) invref_trans invrefine_compseq_left invrefine_compseq_right)+


lemma invrefine_compseq2:
  assumes "F \<subseteq>\<^sub>I G"
  and "\<forall>h\<in>H. \<forall>sb. I (h\<cdot>sb)"
shows "H OOO F \<subseteq> H OOO G"
proof(auto simp add: spscompseq_insert)
  fix h f
  assume a1: "h \<in> H"
  and a2: "f \<in> F"
  obtain ga where ga1: "ga \<in> G"
    and ga2: "\<forall>sb. I sb \<longrightarrow> ga\<cdot>sb = f\<cdot>sb"
    using assms(1) invRefined_def by (metis a2)
  show "\<exists>(ha::'c\<^sup>\<Omega> \<rightarrow> 'a\<^sup>\<Omega>) ga::'a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>. f oo h = ga oo ha \<and> ha \<in> H \<and> ga \<in> G"
    apply(rule_tac x="h" in exI)
    apply(rule_tac x="ga" in exI)
    apply(simp add: ga1 a1)
    apply(rule cfun_eqI)
    by (simp add: ga2 a1 assms(2))
qed


lemma invrefine_comp_feedback:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "F' \<subseteq>\<^sub>J F"
    and "G' \<subseteq>\<^sub>L G"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> G \<Longrightarrow> I sb \<Longrightarrow> J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> G \<Longrightarrow> I sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
  shows "(F' \<Otimes> G') \<subseteq>\<^sub>I (F \<Otimes> G)"
proof (auto simp add: spsComp_def invRefined_def)
  fix f' g'
  assume f'_in: "f' \<in> F'" and g'_in: "g' \<in> G'"
  obtain f where f'_eq_f: "(\<And>sb. J sb \<longrightarrow> f'\<cdot>sb = f\<cdot>sb)" and f_in: "f \<in> F"
    using assms(1) invRefined_def f'_in by metis
  obtain g where g'_eq_g: "(\<And>sb. L sb \<longrightarrow> g'\<cdot>sb = g\<cdot>sb)" and g_in: "g \<in> G"
    using assms(2) invRefined_def g'_in by metis
  have "\<And>sb. I sb \<Longrightarrow> (f' \<otimes> g')\<cdot>sb = (f \<otimes> g)\<cdot>sb"
    apply(rule spfcomp_invariant_eq[OF f'_eq_f g'_eq_g])
    using assms(3) f_in g_in apply blast
    using assms(4) f_in g_in by blast
  then show "\<exists>spf. (\<exists>f g. spf = f \<otimes> g \<and> f \<in> F \<and> g \<in> G) \<and> (\<forall>sb. I sb \<longrightarrow> (f' \<otimes> g')\<cdot>sb = spf\<cdot>sb)"
    using f_in g_in by blast
qed

lemma invref_wellformed:
  fixes F::"('fIn::tchan\<^sup>\<Omega> \<rightarrow> 'fOut::tchan\<^sup>\<Omega>) set"
    and G::"('gIn::tchan\<^sup>\<Omega> \<rightarrow> 'gOut::tchan\<^sup>\<Omega>) set"
assumes "F' \<subseteq>\<^sub>\<bbbW> F"
    and "G' \<subseteq>\<^sub>\<bbbW> G"
    and "\<And>f. f \<in> F \<Longrightarrow> weak f"
    and "\<And>g. g \<in> G \<Longrightarrow> weak g"
  shows "(F' \<Otimes> G') \<subseteq>\<^sub>\<bbbW> (F \<Otimes> G)"
  apply(rule invrefine_comp_feedback[OF assms(1,2)]; rule wellformed_union_minus_star; simp?)
  apply(rule wellformed_spfcomp_iterate[OF assms(3,4)]; simp)
  by(rule wellformed_spfcomp_iterate[OF assms(3,4)]; simp)

lemma invequality:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "F' =\<^sub>J F"
    and "G' =\<^sub>L G"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> G \<Longrightarrow> I sb \<Longrightarrow> J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "\<And>f g sb i. f \<in> F' \<Longrightarrow> g \<in> G' \<Longrightarrow> I sb \<Longrightarrow> J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> G \<Longrightarrow> I sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
    and "\<And>f g sb i. f \<in> F' \<Longrightarrow> g \<in> G' \<Longrightarrow> I sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
  shows "(F' \<Otimes> G') =\<^sub>I (F \<Otimes> G)"
  apply(standard)
  apply(rule invrefine_comp_feedback)
  using assms(1,2) apply auto[2]
  using assms(3,5) apply auto[2]
  apply(rule invrefine_comp_feedback)
  using assms(1,2) apply auto[2]
  using assms(4,6) by auto[2]

lemma invequality_wellformed:
  fixes F::"('fIn::tchan\<^sup>\<Omega> \<rightarrow> 'fOut::tchan\<^sup>\<Omega>) set"
    and G::"('gIn::tchan\<^sup>\<Omega> \<rightarrow> 'gOut::tchan\<^sup>\<Omega>) set"
assumes "F' =\<^sub>\<bbbW> F"
    and "G' =\<^sub>\<bbbW> G"
    and "\<And>f. f \<in> F \<Longrightarrow> weak f"
    and "\<And>g. g \<in> G \<Longrightarrow> weak g"
    and "\<And>f. f \<in> F' \<Longrightarrow> weak f"
    and "\<And>g. g \<in> G' \<Longrightarrow> weak g"
  shows "(F' \<Otimes> G') =\<^sub>\<bbbW> (F \<Otimes> G)"
  apply(rule invequality[OF assms(1,2)]; rule wellformed_union_minus_star; simp?)
  apply(rule wellformed_spfcomp_iterate[OF assms(3,4)]; simp)
  apply(rule wellformed_spfcomp_iterate[OF assms(5,6)]; simp)
  apply(rule wellformed_spfcomp_iterate[OF assms(3,4)]; simp)
  by(rule wellformed_spfcomp_iterate[OF assms(5,6)]; simp)

lemma invrefine_comp_feedback: assumes "S1' \<subseteq>\<^sub>J S1" and "S2' \<subseteq>\<^sub>L S2"
  and "\<And>sb sbOut f g. f \<in> S1 \<Longrightarrow> g \<in> S2 \<Longrightarrow> I sb \<Longrightarrow> J (sb \<uplus>\<^sub>- (f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<star>\<^sub>1)"
  and "\<And>sb sbOut f g. f \<in> S1 \<Longrightarrow> g \<in> S2 \<Longrightarrow> I sb \<Longrightarrow> L (sb \<uplus>\<^sub>- (f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<star>\<^sub>2)"
  shows "(S1' \<Otimes> S2') \<subseteq>\<^sub>I (S1 \<Otimes> S2)"
proof(auto simp add: spsComp_def invRefined_def)
  fix f g
  assume a1: "f \<in> S1'"
  and a2: "g \<in> S2'"
  obtain fa where f_def: "fa\<in>S1" and f_inv: "(\<forall>sb. J sb \<longrightarrow> f\<cdot>sb = fa\<cdot>sb)"
    using assms(1) invRefined_def a1 by metis
  obtain ga where g_def: "ga\<in>S2" and g_inv: "(\<forall>sb. L sb \<longrightarrow> g\<cdot>sb = ga\<cdot>sb)"
    using assms(2) invRefined_def a2 by metis
  show "\<exists>ga.
          (\<exists>(f) g. ga = f \<otimes> g \<and> f \<in> S1 \<and> g \<in> S2) \<and>
          (\<forall>sb. I sb \<longrightarrow> (f \<otimes> g)\<cdot>sb = ga\<cdot>sb)"
    apply(rule_tac x="fa \<otimes> ga" in exI)
    apply(rule conjI)
    using f_def g_def apply auto[1]
    apply(simp add: spfComp_def2)
    apply(simp add: oo_def fix_def2)
    oops

lemma invrefine_comp_nofeedback:
  fixes I :: "(('a \<union> 'c) - 'b \<union> 'd)\<^sup>\<Omega> \<Rightarrow> bool"
  assumes "S1' \<subseteq>\<^sub>J S1" and "S2' \<subseteq>\<^sub>L S2"
  and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
  and "\<And>sb. I sb \<Longrightarrow> L (sb\<star>)"
  and "chDomEmpty TYPE ('b \<union> 'd)"
  shows "(S1' \<Otimes> S2') \<subseteq>\<^sub>I (S1 \<Otimes> S2)"
  apply(rule invrefine_comp_feedback [where J="J", where L="L"])
  apply(simp_all add: assms)
  using assms(3) assms(5) apply (simp add: sbtypecast_reduce1) 
  using assms(4) assms(5) by (simp add: sbtypecast_reduce2)


lemma invrefine_comp1:
assumes "F' \<subseteq>\<^sub>J F" 
    and "\<And>f g sb i. f \<in> F \<longrightarrow> g \<in> G \<longrightarrow> I sb \<longrightarrow> J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
  shows "(F' \<Otimes> G) \<subseteq>\<^sub>I (F \<Otimes> G)"
  apply(rule invrefine_comp_feedback [where L="\<lambda>x . True", where J="J"])
  by(simp_all add: assms)

lemma invrefine_comp2:
assumes "G' \<subseteq>\<^sub>J G" 
    and "\<And>f g sb i. f \<in> F \<longrightarrow> g \<in> G \<longrightarrow> I sb \<longrightarrow> J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
  shows "(F \<Otimes> G') \<subseteq>\<^sub>I (F \<Otimes> G)"
  apply(rule invrefine_comp_feedback [where J="\<lambda>x . True", where L="J"])
  by(simp_all add: assms)


lemma sps_add_input_channels_refI_left:
  fixes F1::"('fIn1\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and F2::"('fIn2\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "F1 \<subseteq>\<^sub>J ({sbTypeCast} \<then> F2)"
    and "\<And>sb. I sb \<Longrightarrow> L (sb\<star>)"
    and "\<And>(f::'fIn1\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) g sb i. f \<in> spsConvert\<cdot>F2 \<Longrightarrow> g \<in> G \<Longrightarrow> L sb \<Longrightarrow> J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "chDom TYPE('fIn2) \<subseteq> chDom TYPE('fIn1)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
  shows "spsConvert\<cdot>(F1 \<Otimes> G) \<subseteq>\<^sub>I (spsConvert\<cdot>(F2 \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst(2) spscomp_convert_left_simple_merge[symmetric, where ?'fIn2.0="'fIn1" and ?'fOut2.0="'fOut"])
  apply simp
  apply(rule assms(4))
  apply fastforce
  apply fastforce
  apply fastforce
  apply(rule assms(5))
  apply(rule spsconvref_inv)
  apply(erule assms(2))
  apply(rule invrefine_comp_feedback[where L="\<lambda>_.True" and J=J])
  apply(subst spsconvert_output_id_eq)
  apply(rule assms(1))
  apply simp
  using assms(3) apply blast
  by simp

lemma sps_add_input_channels_refI_right:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G1::"('gIn1\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and G2::"('gIn2\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "G1 \<subseteq>\<^sub>L ({sbTypeCast} \<then> G2)"
    and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "\<And>f (g::'gIn1\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) sb i. f \<in> F \<Longrightarrow> g \<in> spsConvert\<cdot>G2 \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
    and "chDom TYPE('gIn2) \<subseteq> chDom TYPE('gIn1)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
  shows "spsConvert\<cdot>(F \<Otimes> G1) \<subseteq>\<^sub>I (spsConvert\<cdot>(F \<Otimes> G2)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst(2) spscomp_convert_right_simple_merge[symmetric, where ?'gIn2.0="'gIn1" and ?'gOut2.0="'gOut"])
  apply simp
  apply(rule assms(4))
  apply fastforce
  apply fastforce
  apply(rule assms(5))
  apply(rule spsconvref_inv)
  apply(erule assms(2))
  apply(rule invrefine_comp_feedback[where L=L and J="\<lambda>_.True"], simp)
  apply(subst spsconvert_output_id_eq)
  apply(rule assms(1))
  apply simp
  using assms(3) by blast

lemma add_input_channel_refI:
  fixes F1::"('fIn1\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and F2::"('fIn2\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and m::"'fIn1 \<Rightarrow> 'fIn2"
assumes "\<And>f. f \<in> F1 \<Longrightarrow> f oo sbRenameCh m \<in> F2"
    and "\<And>c. ctype (Rep (m c)) \<subseteq> ctype (Rep c)"
    and "\<And>sb c. \<not>chDomEmpty TYPE('fOut) \<Longrightarrow> I sb \<Longrightarrow> Rep c \<in> chDom TYPE('fIn1) \<Longrightarrow> sb  \<^enum>  c = sb  \<^enum>\<^sub>\<star>  m c"
  shows "F1 \<subseteq>\<^sub>I ({sbTypeCast} \<then> F2)"
proof (auto simp add: invRefined_def seqcomp_image)
  fix f
  assume asm: "f \<in> F1"
  obtain g where g_def: "g = f oo sbRenameCh m"
    by simp
  have "g \<in> F2"
    using assms(1) asm g_def by blast
  moreover have "\<And>sb. I sb \<longrightarrow> f\<cdot>sb = g\<cdot>(sb\<star>)"
    apply(simp add: g_def)
    apply(rule impI)
    apply(rule sb_eqI)
    apply(rule spf_arg_cong)
    apply(subst sbrenamech_getch[OF assms(2)])
    apply simp
    using assms(3) by blast
  ultimately show "\<exists>g \<in> F2. \<forall>sb. I sb \<longrightarrow> f\<cdot>sb = g\<cdot>(sb\<star>)"
    by blast
qed


lemma sps_remove_input_channels_refI_left:
  fixes F1::"('fIn1\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and F2::"('fIn2\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "({sbTypeCast} \<then> F1) \<subseteq>\<^sub>J F2"
    and "\<And>sb. I sb \<Longrightarrow> L (sb\<star>)"
    and "\<And>f g sb i. f \<in> F2 \<Longrightarrow> g \<in> G \<Longrightarrow> L sb \<Longrightarrow> J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "chDom TYPE('fIn1) \<subseteq> chDom TYPE('fIn2)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
  shows "spsConvert\<cdot>(F1 \<Otimes> G) \<subseteq>\<^sub>I (spsConvert\<cdot>(F2 \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst(1) spscomp_convert_left_simple_merge[symmetric, where ?'fIn2.0="'fIn2" and ?'fOut2.0="'fOut"])
  apply simp
  apply(rule assms(4))
  apply fastforce
  apply fastforce
  apply fastforce
  apply(rule assms(5))
  apply(rule spsconvref_inv)
  apply(erule assms(2))
  apply(rule invrefine_comp_feedback[where L="\<lambda>_.True" and J=J])
  apply(subst spsconvert_output_id_eq)
  apply(rule assms(1))
  apply simp
  using assms(3) apply blast
  by simp

lemma sps_remove_input_channels_refI_right:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G1::"('gIn1\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and G2::"('gIn2\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "({sbTypeCast} \<then> G1) \<subseteq>\<^sub>L G2"
    and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> G2 \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
    and "chDom TYPE('gIn1) \<subseteq> chDom TYPE('gIn2)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
  shows "spsConvert\<cdot>(F \<Otimes> G1) \<subseteq>\<^sub>I (spsConvert\<cdot>(F \<Otimes> G2)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_convert_right_simple_merge[symmetric, where ?'gIn2.0="'gIn2" and ?'gOut2.0="'gOut"])
  apply simp
  apply(rule assms(4))
  apply fastforce
  apply fastforce
  apply(rule assms(5))
  apply(rule spsconvref_inv)
  apply(erule assms(2))
  apply(rule invrefine_comp_feedback[where L=L and J="\<lambda>_.True"], simp)
  apply(subst spsconvert_output_id_eq)
  apply(rule assms(1))
  apply simp
  using assms(3) by blast

lemma remove_input_channel_refI:
assumes "\<And>g1. g1 \<in> F1 \<Longrightarrow> \<exists>g2 \<in> F2. \<forall>sb. I sb \<longrightarrow> g1\<cdot>(sb\<star>) = g2\<cdot>sb"
  shows "({sbTypeCast} \<then> F1) \<subseteq>\<^sub>I F2"
  by(auto simp add: invRefined_def seqcomp_image assms(1))

lemma remove_input_channel_ref:
assumes "\<And>g1. g1 \<in> F1 \<Longrightarrow> g1 oo sbTypeCast \<in> F2"
shows "{sbTypeCast} \<then> F1 \<subseteq> F2"
  by(auto simp add: invRefined_def seqcomp_image assms(1))


lemma sps_add_remove_input_channels_eq_left:
  fixes F1::"('fIn1\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and F2::"('fIn2\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "F1 =\<^sub>J ({sbTypeCast} \<then> F2)"
    and "\<And>sb. I sb \<Longrightarrow> L (sb\<star>)"
    and "\<And>f g sb i. f \<in> F1 \<Longrightarrow> g \<in> G \<Longrightarrow> L sb \<Longrightarrow> J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "\<And>f g sb i. f \<in> spsConvert\<cdot>F2 \<Longrightarrow> g \<in> G \<Longrightarrow> L sb \<Longrightarrow> J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "chDom TYPE('fIn2) \<subseteq> chDom TYPE('fIn1)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
  shows "spsConvert\<cdot>(F1 \<Otimes> G) =\<^sub>I (spsConvert\<cdot>(F2 \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  using sps_remove_input_channels_refI_left[where J=J and I =I]
        sps_add_input_channels_refI_left[where J=J and I =I] assms by blast

lemma sps_add_remove_input_channels_eq_right:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G1::"('gIn1\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and G2::"('gIn2\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "({sbTypeCast} \<then> G1) =\<^sub>L G2"
    and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> spsConvert\<cdot>G1 \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> G2 \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
    and "chDom TYPE('gIn1) \<subseteq> chDom TYPE('gIn2)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
  shows "spsConvert\<cdot>(F \<Otimes> G1) =\<^sub>I (spsConvert\<cdot>(F \<Otimes> G2)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  using sps_remove_input_channels_refI_right[where J=J and I =I]
        sps_add_input_channels_refI_right[where J=J and I =I] assms by blast


lemma sps_add_output_channels_refI_left:
  fixes F1::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut1\<^sup>\<Omega>) set"
    and F2::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "(F1 \<then> {sbTypeCast}) \<subseteq>\<^sub>L F2"
    and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "\<And>f g sb i. f \<in> F2 \<Longrightarrow> g \<in> G \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "chDom TYPE('fOut2) \<subseteq> chDom TYPE('fOut1)"
    and "chDom TYPE('fOut1) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut2)"
    and "\<not>chDomEmpty TYPE('gOut) \<longrightarrow> chDom TYPE('fOut1) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut1 \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut1) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
  shows "spsConvert\<cdot>(F1 \<Otimes> G) \<subseteq>\<^sub>I (spsConvert\<cdot>(F2 \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_convert_left_simple_merge[symmetric, where ?'fIn2.0="'fIn" and ?'fOut2.0="'fOut2"])
  apply(rule assms(4))
  apply simp
  apply(rule assms(5))
  apply(rule assms(6))
  apply(rule assms(7))
  apply(rule assms(8))
  apply(rule spsconvref_inv)
  apply(erule assms(2))
  apply(rule invrefine_comp_feedback[where J=L and L="\<lambda>_.True"])
  apply(subst spsconvert_input_id_eq)
  apply(rule assms(1))
  apply simp
  using assms(3) apply blast
  by simp

lemma sps_add_output_channels_refI_right:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G1::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut1\<^sup>\<Omega>) set"
    and G2::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) set"
assumes "(G1 \<then> {sbTypeCast}) \<subseteq>\<^sub>L G2"
    and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> G2 \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
    and "chDom TYPE('gOut2) \<subseteq> chDom TYPE('gOut1)"
    and "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut1) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gOut1) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
  shows "spsConvert\<cdot>(F \<Otimes> G1) \<subseteq>\<^sub>I (spsConvert\<cdot>(F \<Otimes> G2)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_convert_right_simple_merge[symmetric, where ?'gIn2.0="'gIn" and ?'gOut2.0="'gOut2"])
  apply(rule assms(4))
  apply simp
  apply(rule assms(5))
  apply(rule assms(6))
  apply(rule assms(7))
  apply(rule spsconvref_inv)
  apply(erule assms(2))
  apply(rule invrefine_comp_feedback[where L=L and J="\<lambda>_.True"], simp)
  apply(subst spsconvert_input_id_eq)
  apply(rule assms(1))
  apply simp
  using assms(3) by blast

lemma add_output_channel_refI:
assumes "\<And>f. f \<in> F1 \<Longrightarrow> \<exists>g \<in> F2. \<forall>sb. I sb \<longrightarrow> (f\<cdot>sb\<star>) = g\<cdot>sb"
  shows "(F1 \<then> {sbTypeCast}) \<subseteq>\<^sub>I F2"
  by(auto simp add: invRefined_def seqcomp_image2 assms(1))

lemma add_output_channel_ref:
assumes "\<And>f. f \<in> F1 \<Longrightarrow> sbTypeCast oo f \<in> F2"
  shows "F1 \<then> {sbTypeCast} \<subseteq> F2"
  by (auto simp add: seqcomp_image2 assms(1))


lemma sps_remove_output_channels_refI_left:
  fixes F1::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut1\<^sup>\<Omega>) set"
    and F2::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "F1 \<subseteq>\<^sub>L (F2 \<then> {sbTypeCast})"
    and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "\<And>(f::'fIn\<^sup>\<Omega> \<rightarrow> 'fOut1\<^sup>\<Omega>) g sb i. f \<in> spsConvert\<cdot>F2 \<Longrightarrow> g \<in> G \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "chDom TYPE('fOut1) \<subseteq> chDom TYPE('fOut2)"
    and "chDom TYPE('fOut2) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut1)"
    and "\<not>chDomEmpty TYPE('gOut) \<longrightarrow> chDom TYPE('fOut2) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut1 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut2 \<union> 'fOut1) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut2) \<subseteq> chDom TYPE('fOut1 \<union> 'gOut)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut1 \<union> 'gOut)"
  shows "spsConvert\<cdot>(F1 \<Otimes> G) \<subseteq>\<^sub>I (spsConvert\<cdot>(F2 \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst(2) spscomp_convert_left_simple_merge[symmetric, where ?'fIn2.0="'fIn" and ?'fOut2.0="'fOut1"])
  apply(rule assms(4))
  apply simp
  apply(rule assms(5))
  apply(rule assms(6))
  apply(rule assms(7))
  apply(rule assms(8))
  apply(rule spsconvref_inv)
  apply(erule assms(2))
  apply(rule invrefine_comp_feedback[where J=L and L="\<lambda>_.True"])
  apply(subst spsconvert_input_id_eq)
  apply(rule assms(1))
  apply simp
  using assms(3) apply blast
  by simp

lemma sps_remove_output_channels_refI_right:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G1::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut1\<^sup>\<Omega>) set"
    and G2::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) set"
assumes "G1 \<subseteq>\<^sub>L (G2 \<then> {sbTypeCast})"
    and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "\<And>f (g::'gIn\<^sup>\<Omega> \<rightarrow> 'gOut1\<^sup>\<Omega>) sb i. f \<in> F \<Longrightarrow> g \<in> spsConvert\<cdot>G2 \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
    and "chDom TYPE('gOut1) \<subseteq> chDom TYPE('gOut2)"
    and "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut2) \<subseteq> chDom TYPE('fOut \<union> 'gOut1)"
    and "\<not>chDomEmpty TYPE('gOut1) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gOut2) \<subseteq> chDom TYPE('fOut \<union> 'gOut1)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut1)"
  shows "spsConvert\<cdot>(F \<Otimes> G1) \<subseteq>\<^sub>I (spsConvert\<cdot>(F \<Otimes> G2)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst(2) spscomp_convert_right_simple_merge[symmetric, where ?'gIn2.0="'gIn" and ?'gOut2.0="'gOut1"])
  apply(rule assms(4))
  apply simp
  apply(rule assms(5))
  apply(rule assms(6))
  apply(rule assms(7))
  apply(rule spsconvref_inv)
  apply(erule assms(2))
  apply(rule invrefine_comp_feedback[where L=L and J="\<lambda>_.True"], simp)
  apply(subst spsconvert_input_id_eq)
  apply(rule assms(1))
  apply simp
  using assms(3) by blast

lemma remove_output_channel_refI:
fixes F1::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut1\<^sup>\<Omega>) set"
  and F2::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set"
  and m::"'fOut2 \<Rightarrow> 'fOut1"
assumes "\<And>f. f \<in> F1 \<Longrightarrow> \<exists>g \<in> F2. \<forall>sb. I sb \<longrightarrow> (sbRenameCh m oo f)\<cdot>sb = g\<cdot>sb"
    and "\<And>c. ctype (Rep (m c)) \<subseteq> ctype (Rep c)"
    and "chDom TYPE('fOut1) \<subseteq> chDom TYPE('fOut2)"
    and "\<And>c. Rep c \<in> chDom TYPE('fOut1) \<Longrightarrow> m (Abs (Rep c)) = c"
  shows "F1 \<subseteq>\<^sub>I (F2 \<then> {sbTypeCast})"
proof (auto simp add: invRefined_def seqcomp_image2)
  fix f
  assume a1: "f \<in> F1"
  have a2: "\<And>sb. f\<cdot>sb = (sbTypeCast oo sbRenameCh m oo f)\<cdot>sb"
    apply(rule sb_eqI)
    apply simp
    apply(subst sbrenamech_getch2[OF _ assms(2)])
    using assms(3) apply blast
    by(subst assms(4); simp)
  show "\<exists>g \<in> F2. \<forall>sb. I sb \<longrightarrow> f\<cdot>sb = (g\<cdot>sb\<star>)"
    apply(subst a2)
    using assms(1) by (metis a1 cfcomp2)
qed

lemma remove_output_channel_ref:
fixes F1::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut1\<^sup>\<Omega>) set"
  and F2::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set"
  and m::"'fOut2 \<Rightarrow> 'fOut1"
assumes "\<And>f. f \<in> F1 \<Longrightarrow> sbRenameCh m oo f \<in> F2"
    and "\<And>c. ctype (Rep (m c)) \<subseteq> ctype (Rep c)"
    and "chDom TYPE('fOut1) \<subseteq> chDom TYPE('fOut2)"
    and "\<And>c. Rep c \<in> chDom TYPE('fOut1) \<Longrightarrow> m (Abs (Rep c)) = c"
  shows "F1 \<subseteq> F2 \<then> {sbTypeCast}"
  apply(subst invref_true_iff[symmetric])
  apply(rule remove_output_channel_refI[OF _ assms(2-4)]; simp)
  using assms(1) by force


lemma sps_add_remove_output_channels_eq_left:
  fixes F1::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut1\<^sup>\<Omega>) set"
    and F2::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "F1 =\<^sub>L (F2 \<then> {sbTypeCast})"
    and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "\<And>f g sb i. f \<in> F1 \<Longrightarrow> g \<in> G \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "\<And>f g sb i. f \<in> spsConvert\<cdot>F2 \<Longrightarrow> g \<in> G \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "chDom TYPE('fOut1) \<subseteq> chDom TYPE('fOut2)"
    and "chDom TYPE('fOut2) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut1)"
    and "\<not>chDomEmpty TYPE('gOut) \<longrightarrow> chDom TYPE('fOut2) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut1 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut2 \<union> 'fOut1) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut2) \<subseteq> chDom TYPE('fOut1 \<union> 'gOut)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut1 \<union> 'gOut)"
shows "spsConvert\<cdot>(F1 \<Otimes> G) =\<^sub>I (spsConvert\<cdot>(F2 \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  using sps_remove_output_channels_refI_left[where J=J and I =I]
        sps_add_output_channels_refI_left[where J=J and I =I] assms by blast

lemma sps_add_remove_output_channels_eq_right:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G1::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut1\<^sup>\<Omega>) set"
    and G2::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) set"
assumes "(G1 \<then> {sbTypeCast}) =\<^sub>L G2"
    and "\<And>sb. I sb \<Longrightarrow> J (sb\<star>)"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> spsConvert\<cdot>G1 \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
    and "\<And>f g sb i. f \<in> F \<Longrightarrow> g \<in> G2 \<Longrightarrow> J sb \<Longrightarrow> L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
    and "chDom TYPE('gOut2) \<subseteq> chDom TYPE('gOut1)"
    and "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut1) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gOut1) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
  shows "spsConvert\<cdot>(F \<Otimes> G1) =\<^sub>I (spsConvert\<cdot>(F \<Otimes> G2)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  using sps_remove_output_channels_refI_right[where J=J and I =I]
        sps_add_output_channels_refI_right[where J=J and I =I] assms by blast


end

theory SPSConvRef

imports sps.SPSComp bundlelocale.SBRenameGen "HOL-Eisbach.Eisbach"

begin

lemma spsconvert_subset_rename[simp]:
  fixes S1::"('I1\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  and S2::"('I2\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  assumes "spsConvert\<cdot>S1 \<subseteq> S2"
  and "\<And>sb. ((sbGen_surjrename.rename f1\<cdot>sb::'b\<^sup>\<Omega>)\<star>::'Out\<^sup>\<Omega>) = (sbGen_surjrename.rename f3\<cdot>sb)"
  shows "((spsConvert\<cdot>{(sbGen_surjrename.rename f1) oo spf | spf. spf\<in> S1})::('I2\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)set)
      \<subseteq> {(sbGen_surjrename.rename f3) oo spf | spf. spf\<in> S2}"
  apply(auto simp add: spsConvert_def assms)[1]
  apply(rule_tac x="spfConvert\<cdot>spf" in exI,auto)
  apply(rule cfun_eqI,simp add: spfConvert.rep_eq)
  apply (simp add: assms(2))
  by (metis assms(1) imageI spsConvert.rep_eq subset_iff)

lemma spsconvert_subset_rename_alt[simp]:
  fixes S1::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  and S2::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  assumes "S1 \<subseteq> S2"
  and "\<And>sb. sbGen_surjrename.invRename f2\<cdot>((sb::'In\<^sup>\<Omega>)\<star>::'a\<^sup>\<Omega>) = sbGen_surjrename.invRename f4\<cdot>(sb)"
  and "\<And>sb. ((sbGen_surjrename.rename f1\<cdot>sb::'b\<^sup>\<Omega>)\<star>::'Out\<^sup>\<Omega>) = (sbGen_surjrename.rename f3\<cdot>sb)"
  shows "((spsConvert\<cdot>{(sbGen_surjrename.rename f1) oo spf oo (sbGen_surjrename.invRename f2) | spf. spf\<in> S1})::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)set)
      \<subseteq> {(sbGen_surjrename.rename f3) oo spf oo (sbGen_surjrename.invRename f4) | spf. spf\<in> S2}"
  apply (auto simp add: spsConvert.rep_eq spfConvert.rep_eq)[1]
  apply(rule_tac x="spf" in exI,auto)
  apply(rule cfun_eqI,simp)
  apply (simp add: assms(2) assms(3))
  using assms(1) by auto

lemma spsconvert_getterref:
  assumes "\<And>sb. sbGen.getter f1\<cdot>(sb\<star>) = sbGen.getter f3\<cdot>sb"
  and "\<And>sb. sbGen.getter f2\<cdot>sb = sbGen.getter f4\<cdot>(sb\<star>)"
  and "P1 = P2"
  shows "spsConvert\<cdot>{spf::'I1\<^sup>\<Omega>\<rightarrow>'O1\<^sup>\<Omega> | spf. \<forall>sb. P1 (sbGen.getter f1\<cdot>sb) (sbGen.getter f2\<cdot>(spf\<cdot>sb))}
      \<subseteq> {spf::'I2\<^sup>\<Omega>\<rightarrow>'O2\<^sup>\<Omega> | spf. \<forall>sb. P2 (sbGen.getter f3\<cdot>sb) (sbGen.getter f4\<cdot>(spf\<cdot>sb))}"
  apply(auto simp add: spsConvert_def spfConvert_def assms(2,3))
  by (metis assms(1))

lemma spsconvert_subset_rename_noin[simp]:
  fixes S1::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  and S2::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  assumes "S1 \<subseteq> S2"
  and "\<And>sb. ((sbGen_surjrename.rename f1\<cdot>sb)\<star>::'Out\<^sup>\<Omega>) = (sbGen_surjrename.rename f3\<cdot>sb)"
shows "(spsConvert\<cdot>{(sbGen_surjrename.rename f1) oo spf | spf. spf\<in> S1}::('I\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)
      \<subseteq> {(sbGen_surjrename.rename f3) oo spf | spf. spf\<in> S2}"
  apply (auto simp add: spsConvert.rep_eq spfConvert.rep_eq)[1]
  apply(rule_tac x="spf" in exI,auto)
  apply(rule cfun_eqI,simp)
  apply(subst assms(2))
  apply simp
  using assms(1) by auto

lemma spsconvert_subset_rename_noout[simp]:
  fixes S1::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  and S2::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  assumes "S1 \<subseteq> S2"
  and "\<And>sb. sbGen_surjrename.invRename f2\<cdot>((sb::'In\<^sup>\<Omega>)\<star>::'a\<^sup>\<Omega>) = sbGen_surjrename.invRename f4\<cdot>(sb)"
  shows "((spsConvert\<cdot>{spf oo (sbGen_surjrename.invRename f2) | spf. spf\<in> S1})::('In\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)set)
      \<subseteq> { spf oo (sbGen_surjrename.invRename f4) | spf. spf\<in> S2}"
  apply (auto simp add: spsConvert.rep_eq spfConvert.rep_eq)[1]
  apply(rule_tac x="spf" in exI,auto)
  apply(rule cfun_eqI,simp)
  apply (simp add: assms(2))
  using assms(1) by auto

lemma spsconvert_subset_ren[simp]:
  fixes S1::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  and S2::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set"
  and f1::"'b \<Rightarrow> 'O"
  and f2::"'a \<Rightarrow> 'I"
  assumes "S1 \<subseteq> S2"
  and "\<And>c. f2 (Abs (Rep c)) = f4 c"
  and "\<And>c. f1 (Abs (Rep c)) = f3 c"
  and "sbGen_rename f1 cons1"
  and "sbGen_rename f2 cons2"
  and "sbGen_rename f3 cons3"
  and "sbGen_rename f4 cons4"
  and "chDom TYPE('a) = chDom TYPE('In)"
  and "chDom TYPE('b) = chDom TYPE('Out)"
  shows "((spsConvert\<cdot>{(sbGen_surjrename.rename f1) oo spf oo (sbGen_surjrename.invRename f2) | spf. spf\<in> S1})::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)set)
      \<subseteq> {(sbGen_surjrename.rename f3) oo spf oo (sbGen_surjrename.invRename f4) | spf. spf\<in> S2}"
  apply(rule spsconvert_subset_rename_alt,simp add: assms)
  apply(rule invrename_eq[of f2 cons2 f4 cons4],simp_all add: assms) 
  by(rule rename_eq[of f1 cons1 f3 cons3],simp_all add: assms)



method spsconvref uses sps1_def sps2_def 
                       convconv1_def convconv2_def 
                       rawconv1_def rawconv2_def
                       conv1_def conv2_def =
  (rule spscomp_hidingref,(auto)[6]
  ,simp add: sps1_def sps2_def
  ,( rule spsconvert_subset_rename)
  ,simp add: spsconvert_merge convconv1_def convconv2_def rawconv1_def rawconv2_def
  ,((rule spscomp_hidingref)
  ,(auto)[6]
  ,simp only: conv1_def conv2_def
  ,rule spsconvert_getterref, rule sbgetter_eq
  ,(auto)[6])?)

method spsconvref_last uses sps1_def sps2_def 
                       convconv1_def convconv2_def 
                       rawconv1_def rawconv2_def
                       conv1_def conv2_def  =
  (simp add: sps1_def sps2_def
  ,(rule spsconvert_subset_rename_noin | rule spsconvert_subset_rename | rule spsconvert_subset_rename_noout)
  ,simp add: spsconvert_merge convconv1_def convconv2_def rawconv1_def rawconv2_def
  ,((rule spscomp_hidingref)
  ,(auto)[6]
  ,simp only: conv1_def conv2_def
  ,rule spsconvert_getterref, rule sbgetter_eq
  ,(auto)[6])?)


declare forall2all [simp add]

end

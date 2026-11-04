theory SPSComp

imports SPS spf.SPFComp
begin


definition spsComp::
"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set \<Rightarrow> 
  ((('I1 \<union> 'I2) - 'O1 \<union> 'O2)\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>) set" (infixr "\<Otimes>" 70) 
where "spsComp F G = {f \<otimes> g | f g. f\<in>F \<and> g\<in>G }"

definition %invisible sbSameEq:: "'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> bool" where
"sbSameEq sb1 sb2 \<equiv> \<forall>c\<in>chDom TYPE('cs1) \<inter> chDom TYPE('cs2). 
                         sb1 \<^enum> (Abs c) = sb2 \<^enum> (Abs c) "

lemma spsComp_nempty_mp1: "F \<Otimes> G \<noteq> {} \<Longrightarrow> F \<noteq> {}"
  using spsComp_def by auto

lemma spsComp_nempty_mp2: "F \<Otimes> G \<noteq> {} \<Longrightarrow> G \<noteq> {}"
  using spsComp_def by auto

lemma spscomp_singeltons: "{f} \<Otimes> {g} = {f \<otimes> g}"
  by(simp add: spsComp_def)

lemma "(spsComplete sps1) \<Otimes> (spsComplete sps2) \<subseteq> 
        spsComplete (sps1 \<Otimes> sps2)"
proof(rule spscomplete_belowI)
  fix spf sb
  assume as: "spf\<in>(spsComplete sps1) \<Otimes> (spsComplete sps2)"
(*
  obtain spf1 spf2 where "spf = spf1\<otimes>\<^sub>\<star>spf2" 
      and spf1_def: "spf1 \<in>(spsComplete sps1)"
      and spf2_def: "spf2 \<in>(spsComplete sps2)"
    using as by(auto simp add: spsComp_def spscomplete_set)

  obtain spf1' where spf1'_eq: "spf1'\<cdot>(sb\<uplus>\<^sub>\<star>(spf\<cdot>sb)) = spf1\<cdot>(sb\<uplus>\<^sub>\<star>(spf\<cdot>sb))" and "spf1'\<in>sps1"
    using spf1_def apply(auto simp add: spscomplete_set) by metis
  obtain spf2' where spf2'_eq: "spf2'\<cdot>(sb\<uplus>\<^sub>\<star>(spf\<cdot>sb)) = spf2\<cdot>(sb\<uplus>\<^sub>\<star>(spf\<cdot>sb))" and "spf2'\<in>sps2"
    using spf2_def apply(auto simp add: spscomplete_set) by metis

  have "(spf1' \<otimes>\<^sub>\<star> spf2') \<in> (sps1 \<Otimes>\<^sub>\<star> sps2)" 
      using spsComp_def \<open>spf1'\<in>sps1\<close> \<open>spf2'\<in>sps2\<close> by blast
    moreover have "(spf1' \<otimes>\<^sub>\<star> spf2')\<cdot>sb = spf\<cdot>sb"*)
      oops
(*
      apply(rule spfcomp_eqI)
       apply((subst spf1'_eq | subst spf2'_eq), simp add: \<open>spf = spf1\<otimes>\<^sub>\<star>spf2\<close>)
      apply(subst spfcomp_l, simp)
  ultimately show "\<exists>spf2\<in>sps1 \<Otimes>\<^sub>\<star> sps2. spf\<cdot>sb = spf2\<cdot>sb"
      by (metis)
qed
*)

text\<open>\fbox{\parbox{\textwidth}{Refinement of a component in a decomposed structure automatically
leads to refinement of the composition @{cite "Broy.2007"}.}} \<close>

theorem spscomp_refinement[simp]:
fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
  and F_ref::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  and G_ref::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
assumes "F_ref \<subseteq> F"
    and "G_ref \<subseteq> G"
shows "(F_ref \<Otimes> G_ref) \<subseteq> (F \<Otimes> G)"
  apply(simp add: spsComp_def)
  using assms by blast

theorem spscomp_equality: "F = F' \<Longrightarrow> G = G' \<Longrightarrow> (F \<Otimes> G) = (F' \<Otimes> G')"
  by(simp add: spsComp_def)



theorem assumes "\<forall>f\<in>S. P f" and "S' \<subseteq> S"
  shows "\<forall>f'\<in>S'. P f'"
  using assms(1) assms(2) by auto


definition spsIsConsistent :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> bool" where
"spsIsConsistent sps \<equiv> (sps \<noteq> {})"


theorem spscomp_consistent:
 fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
   and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
 assumes "spsIsConsistent F"
     and "spsIsConsistent G"
   shows "spsIsConsistent (F \<Otimes> G)"
proof -
  have f1: "G \<noteq> {}"
    using assms(2) spsIsConsistent_def by blast
  have "F \<noteq> {}"
    by (metis assms(1) spsIsConsistent_def)
  then have "{c \<otimes> ca |c ca. c \<in> F \<and> ca \<in> G} \<noteq> {}"
    using f1 by blast
  then show ?thesis
    by (simp add: spsComp_def spsIsConsistent_def)
qed


theorem spscomp_subpred: 
 fixes P::"'I1\<^sup>\<Omega> \<Rightarrow> 'O1\<^sup>\<Omega> \<Rightarrow> bool"
   and H::"'I2\<^sup>\<Omega> \<Rightarrow> 'O2\<^sup>\<Omega> \<Rightarrow> bool"
 assumes "chDom TYPE ('O1) \<inter> chDom TYPE ('O2) = {}"
     and "\<forall>spf\<in>S1. \<forall>sb. P sb (spf\<cdot>sb)"
     and "\<forall>spf\<in>S2. \<forall>sb. H sb (spf\<cdot>sb)"
  shows  "S1 \<Otimes> S2 \<subseteq>   
          {g. \<forall>sb. 
               let all = sb \<uplus> g\<cdot>sb in 
                P (all\<star>) (all\<star>) \<and> H (all\<star>) (all\<star>)
          }"
  apply (auto simp add: spsComp_def Let_def)[1]
  apply (simp add: spfcomp_extract_l)
  by (simp add: assms spfcomp_extract_r)+

lemma spscomp_predicate: 
      fixes P::"'I1\<^sup>\<Omega> \<Rightarrow> 'O1\<^sup>\<Omega> \<Rightarrow> bool"
        and H::"'I2\<^sup>\<Omega> \<Rightarrow> 'O2\<^sup>\<Omega> \<Rightarrow> bool"
      assumes "chDom TYPE ('O1) \<inter> chDom TYPE ('O2) = {}"
      shows  "{p . \<forall>sb. P sb (p\<cdot>sb)} \<Otimes> {h . \<forall>sb. H sb (h\<cdot>sb)} \<subseteq>   
            {g. \<forall>sb. 
                  let all = sb \<uplus> g\<cdot>sb in 
                    P (all\<star>) (all\<star>) \<and> H (all\<star>) (all\<star>)
            }"
  apply(rule spscomp_subpred)
  apply (simp_all add: assms)
  done

lemma spscomp_predicatel: 
    fixes SPS1::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
      and SPS2::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
    assumes
              "\<And>spf sb. spf\<in>SPS1 \<Longrightarrow> P sb (spf\<cdot>sb)"
        and "spf\<in>(SPS1 \<Otimes> SPS2)"
    shows  "P (sb \<uplus>\<^sub>\<star> spf\<cdot>sb) (sb \<uplus>\<^sub>\<star> spf\<cdot>sb)"
proof - 
  obtain spf1 and spf2 where "spf = spf1 \<otimes> spf2"
    and "spf1 \<in> SPS1"
    using assms(2) spsComp_def by blast
  thus ?thesis
    by (simp add: assms(1) spfcomp_extract_l) 
qed

lemma spscomp_predicatel2:
  fixes SPS1::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  and   SPS2::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
  assumes "spf \<in> (SPS1 \<Otimes> SPS2)"
  and "\<And>sb spf. spf\<in> SPS1 \<Longrightarrow> P sb (spf\<cdot>sb)"
shows  "P ((sbIn \<uplus>\<^sub>- (spf\<cdot>sbIn))\<star>) ((spf\<cdot>sbIn)\<star>\<^sub>1)"
proof -
   obtain spf1 and spf2 where spf_comp: "spf = spf1 \<otimes> spf2"
    and spf1_set:"spf1 \<in> SPS1"
     using assms(1) spsComp_def by blast 
   have spf_unfold: "spf\<cdot>sbIn =  spf1\<cdot>((sbIn \<uplus>\<^sub>- spf\<cdot>sbIn)\<star>\<^sub>1) \<uplus> spf2\<cdot>((sbIn \<uplus>\<^sub>- spf\<cdot>sbIn)\<star>\<^sub>2)"
     using spf_comp spfcomp_unfold by blast
   thus ?thesis 
     by (metis assms(2) sbunion_fst spf1_set)
 qed

lemma spscomp_predicater: 
    fixes SPS1::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
      and SPS2::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
    assumes "chDom TYPE ('O1) \<inter> chDom TYPE ('O2) = {}"
        and "\<And>spf sb. spf\<in>SPS2 \<Longrightarrow> H sb (spf\<cdot>sb)"
        and "spf\<in>(SPS1 \<Otimes> SPS2)"
    shows  "H (sb \<uplus>\<^sub>\<star> spf\<cdot>sb) (sb \<uplus>\<^sub>\<star> spf\<cdot>sb)"
proof - 
  obtain spf1 and spf2 where "spf = spf1 \<otimes> spf2"
    and "spf2 \<in> SPS2"
    using assms(3) spsComp_def by blast
  thus ?thesis
    by (simp add: assms(1) assms(2) spfcomp_extract_r)
qed

lemma spscomp_predicater2:
  fixes SPS1::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
    and SPS2::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
assumes "spf \<in> (SPS1 \<Otimes> SPS2)"
    and "chDom TYPE('O1) \<inter> chDom TYPE('O2) = {}"
    and "\<And>sb spf. spf\<in> SPS2 \<Longrightarrow> P sb (spf\<cdot>sb)"
  shows "P ((sbIn \<uplus>\<^sub>- (spf\<cdot>sbIn))\<star>) ((spf\<cdot>sbIn)\<star>\<^sub>2)"
proof -
   obtain spf1 and spf2 where spf_comp: "spf = spf1 \<otimes> spf2"
    and spf2_set:"spf2 \<in> SPS2"
     using assms(1) spsComp_def by blast 
   have spf_unfold: "spf\<cdot>sbIn =  spf1\<cdot>((sbIn \<uplus>\<^sub>- spf\<cdot>sbIn)\<star>\<^sub>1) \<uplus> spf2\<cdot>((sbIn \<uplus>\<^sub>- spf\<cdot>sbIn)\<star>\<^sub>2)"
     using spf_comp spfcomp_unfold by blast
   thus ?thesis
     apply(subst assms(3) spf_unfold, subst sbunion_snd)
     by(simp add: assms spf2_set)+    
 qed



lemma spscomp_praedicate2: 
      fixes P::"'I1\<^sup>\<Omega> \<Rightarrow> 'O1\<^sup>\<Omega> \<Rightarrow> bool"
        and H::"'I2\<^sup>\<Omega> \<Rightarrow> 'O2\<^sup>\<Omega> \<Rightarrow> bool"
      assumes "chDom TYPE ('O1) \<inter> chDom TYPE ('O2) = {}"
      shows  "  
            {g. \<forall>sb. 
                  let all = sb \<uplus> g\<cdot>sb in 
                    P (all\<star>) (all\<star>) \<and> H (all\<star>) (all\<star>)
            } \<subseteq> spsComp {p . \<forall>sb. P sb (p\<cdot>sb)} 
                        {h . \<forall>sb. H sb (h\<cdot>sb)}" (is "?LHS \<subseteq> ?RHS")
  oops
(*
proof 
  fix g
  assume "g\<in>?LHS"
  hence "\<And>sb. P ((sb\<uplus>g\<cdot>sb)\<star>) ((sb\<uplus>g\<cdot>sb)\<star>)"
    by (metis (mono_tags, lifting) mem_Collect_eq)
  have "\<exists>p h. p\<otimes>h = g" oops*)
(*  from this obtain p h where "p\<otimes>h = g" by auto
  have "\<And>sb. P (sb) (p\<cdot>sb)" oops *)
(*  show "g\<in>?RHS" oops *)



  

lift_definition spsConvert :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set" is
"\<lambda> sps . (Rep_cfun spfConvert) ` sps"
  by (intro cont2cont)

lemma spsConvert_nempty_mp: "spsConvert\<cdot>(F) \<noteq> {} \<Longrightarrow> F \<noteq> {}"
  by(simp add: spsConvert_def)

lemma spsconvert_input_id_eq: "spsConvert\<cdot>F = F \<then> {sbTypeCast}"
  apply(simp add: spsConvert_def seqcomp_image2)
  using spfconvert_input_id_eq by fastforce

lemma spsconvert_output_id_eq: "spsConvert\<cdot>F = {sbTypeCast} \<then> F"
  apply(simp add: spsConvert_def seqcomp_image)
  using spfconvert_output_id_eq by fastforce

lemma spsconvert_eq[simp]:
  shows "spsConvert\<cdot>sps = sps"
  by(simp add: spsConvert_def)

lemma spsconvert_symmetric:
  fixes sps1::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  and sps2::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
assumes "chDom TYPE('I1) = chDom TYPE('I2)"
  and "chDom TYPE('O1) = chDom TYPE('O2)"
  assumes "sps1 = spsConvert\<cdot>sps2"
  shows "sps2 = spsConvert\<cdot>sps1"
  apply(subst assms)
  apply(simp add: spsConvert.rep_eq image_def)
  apply(auto)[1]
proof -
  fix x
  assume a2: "x \<in> sps2"
  show "\<exists>xa::'I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega> . (\<exists>x::'I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>\<in>sps2. xa = spfConvert\<cdot>x) \<and> x = spfConvert\<cdot>xa"
  proof -
    obtain xa::"('I1\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)" where a3: "spfConvert\<cdot>x = xa"
      by simp
    obtain x2::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)" where a4: "spfConvert\<cdot>xa = x2" by simp
    have h1: "(xa = spfConvert\<cdot>x) \<and> x = spfConvert\<cdot>xa"
      apply(subst spfconvert_symmetric[of "xa" "x"])
      using assms apply auto[1]
      using assms apply auto[1]
      using a3 by auto
    have h2: "x2 \<in> sps2"
      apply(subst a4[symmetric])
      apply(subst a3[symmetric])
      apply(subst spfconvert_closed)
      using assms apply auto[2]
      apply(subst spfconvert_eq)
      by (simp add: a2)
    have h3: "x2 \<in> sps2 \<and> xa = spfConvert\<cdot>x2 \<and>  x = spfConvert\<cdot>xa"
      using h2 h1 a3 a4 by simp
    show ?thesis
      using assms h3 by auto
  qed
next
  show "\<And>xb. xb \<in> sps2 \<Longrightarrow> (spfConvert::('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<rightarrow> 'I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)\<cdot>((spfConvert)\<cdot>xb) \<in> sps2"
    apply (subst spfconvert_closed)
    using assms by auto
qed

lemma spsconvref[simp]: assumes "S1 \<subseteq> S2"
  shows"spsConvert\<cdot>S1 \<subseteq> spsConvert\<cdot>S2"
  apply(simp add: spsConvert.rep_eq)
  using assms by force

lemma spsconveq: 
assumes "S1 = S2"
  shows "spsConvert\<cdot>S1 = spsConvert\<cdot>S2"
  by(simp add: assms(1) spsConvert.rep_eq)

lemma spsconvert_merge:
  fixes SPS::"('I1\<^sup>\<Omega> \<rightarrow>'O1\<^sup>\<Omega>) set"
assumes "chDom TYPE('I3) \<inter> chDom TYPE('I1 - 'I2) = {}"
    and "chDom TYPE('O1) \<inter> chDom TYPE('O3 - 'O2) = {}" 
  shows"spsConvert\<cdot>(spsConvert\<cdot>SPS::('I2\<^sup>\<Omega>\<rightarrow>'O2\<^sup>\<Omega>) set) = (spsConvert\<cdot>SPS ::('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>) set)" 
  apply(simp add: spsConvert.rep_eq)
  using spfconvert_merge[OF assms] image_cong by fastforce

lemma spsconvert_merge_simple:
  fixes SPS::"('I1\<^sup>\<Omega> \<rightarrow>'O1\<^sup>\<Omega>) set"
assumes "chDom TYPE('I1) \<subseteq> chDom TYPE('I2)"
    and "chDom TYPE('O3) \<subseteq> chDom TYPE('O2)" 
  shows"spsConvert\<cdot>(spsConvert\<cdot>SPS::('I2\<^sup>\<Omega>\<rightarrow>'O2\<^sup>\<Omega>) set) = (spsConvert\<cdot>SPS ::('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>) set)" 
  apply(rule spsconvert_merge)
  using assms by(fastforce)+

lemma spscomp_hidingref:
  fixes S1::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  and S2::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
  fixes S3::"('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>) set"
  and S4::"('I4\<^sup>\<Omega> \<rightarrow> 'O4\<^sup>\<Omega>) set"
  assumes "chDom TYPE ('I1) = chDom TYPE('I3)"
  assumes "chDom TYPE ('O1) = chDom TYPE('O3)"
  assumes "chDom TYPE ('I2) = chDom TYPE('I4)"
  assumes "chDom TYPE ('O2) = chDom TYPE('O4)"
  assumes "chDom TYPE ((('I1 \<union> 'I2) - 'O1 \<union> 'O2)) = chDom TYPE ('I)" 
  assumes "chDom TYPE ('O) \<subseteq> chDom TYPE ('O1 \<union> 'O2) "
  assumes "((spsConvert\<cdot>S1)::('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>) set) \<subseteq> S3"
  assumes "((spsConvert\<cdot>S2)::('I4\<^sup>\<Omega> \<rightarrow> 'O4\<^sup>\<Omega>) set) \<subseteq> spsConvert\<cdot>S4"
  shows "((spsConvert\<cdot>(S1 \<Otimes> S2))::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set) \<subseteq> (spsConvert\<cdot>(S3 \<Otimes> S4))"
  apply (auto simp add: spsConvert_def)[1]
proof-
  fix xa::"(('I1 \<union> 'I2) - 'O1 \<union> 'O2)\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>"
  assume a1:"xa \<in> S1 \<Otimes> S2"
  then obtain f g where f_def: "xa = f \<otimes> g \<and> f \<in> S1 \<and> g\<in> S2"
    using a1 spsComp_def by blast
  then obtain f2 where f2_def:"((spfConvert\<cdot>f)::('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>)) = spfConvert\<cdot>f2 \<and> f2 \<in> S3"
    by(insert assms,auto simp add: spsConvert_def)
  obtain g2 where g2_def:"((spfConvert\<cdot>g)::('I4\<^sup>\<Omega> \<rightarrow> 'O4\<^sup>\<Omega>)) = spfConvert\<cdot>g2 \<and> g2 \<in> S4"
    by(insert assms f_def,auto simp add: spsConvert_def)
  have ftof2:"spfConvert\<cdot>f = f2"
    using f2_def by auto
  have gtog2:"spfConvert\<cdot>g = g2"
    using g2_def by auto
  have h:"spfConvert\<cdot>f \<in> S3 \<and> spfConvert\<cdot>g\<in> S4"
    by(simp add: f2_def g2_def ftof2 gtog2)
  then have "spfConvert\<cdot>f \<otimes> spfConvert\<cdot>g \<in> (S3 \<Otimes> S4)"
    by(auto simp add: spsComp_def)
  have "((spfConvert\<cdot>xa)::'I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) =spfConvert\<cdot>(f2 \<otimes> g2)"
    apply(rule spfconvert2hiding,simp_all add: assms)
    using assms apply auto[2]
    apply(simp add: f_def)
    apply(simp add: ftof2[symmetric] gtog2[symmetric])
    apply(rule cfun_eqI)
    apply(auto simp add: spfConvert_def spfComp_def2 assms)[1]
    apply(simp add: assms sbtypecast_fix_cont)
    apply(rule cfun_arg_cong)
    apply(rule cfun_eqI)
    apply(simp)
    by(rule sb_eqI,auto simp add: sbgetch_insert sbunion_rep_eq assms)
  then show "((spfConvert\<cdot>xa)::'I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<in> Rep_cfun spfConvert ` (S3 \<Otimes> S4)"
    apply(simp add: spsComp_def)
    using f2_def g2_def by blast
qed

definition spsEq::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set \<Rightarrow> bool" where
"spsEq F G \<equiv> chDom TYPE('I1) = chDom TYPE('I2) \<and>
             chDom TYPE('O1) = chDom TYPE('O2) \<and>
             (\<forall> f \<in> F. \<exists> g \<in> G. f \<triangleq>\<^sub>f g) \<and> (\<forall> g \<in> G. \<exists> f \<in> F. f \<triangleq>\<^sub>f g)"

abbreviation sbseq_abbr :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set \<Rightarrow> bool"
(infixr "\<triangleq>\<^sub>F" 101) where "F \<triangleq>\<^sub>F G \<equiv> spsEq F G"

lemma spseq_refl: "F \<triangleq>\<^sub>F F"
  apply (auto simp add: spsEq_def spfEq_def)[1]
  using arg_congsbeq by auto

lemma spseq_symmetric:
  fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
  assumes "F \<triangleq>\<^sub>F G"
  shows "G \<triangleq>\<^sub>F F"
  using assms apply(auto simp add: spsEq_def)[1]
  using spfeq_symmetric by blast+

lemma spseq_trans:
  fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
  and H::"('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>) set"
  assumes "F \<triangleq>\<^sub>F G" and "G \<triangleq>\<^sub>F H"
  shows "F \<triangleq>\<^sub>F H"
  using assms apply(auto simp add: spsEq_def)[1]
  using spfeq_trans apply blast 
  using spfeq_trans
  by metis

lemma spseq_smallest:
  fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
  assumes "chDom TYPE('I1) \<noteq> chDom TYPE('I2) \<or>
           chDom TYPE('O1) \<noteq> chDom TYPE('O2) \<or>
           (\<exists> f \<in> F. \<forall> g \<in> G. \<not>(f \<triangleq>\<^sub>f g)) \<or>
           (\<exists> g \<in> G. \<forall> f \<in> F. \<not>(f \<triangleq>\<^sub>f g))"
  shows "\<not>(F \<triangleq>\<^sub>F G)"
  using assms by (simp add: spsEq_def)

lemma spsconvert2spseq:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
  and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
  assumes "chDom TYPE ('fIn) = chDom TYPE('gIn)"
  and "chDom TYPE('fOut) = chDom TYPE('gOut)"
  shows"F = spsConvert\<cdot>G \<Longrightarrow> F \<triangleq>\<^sub>F G"
  apply(auto simp add: spsEq_def spsConvert.rep_eq assms)[1]
proof -
  fix g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assume a1: "F = Rep_cfun spfConvert ` G"
  assume a2: "g \<in> G"
  have h1: "(spfConvert\<cdot>g::'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) \<triangleq>\<^sub>f g"
    by (subst spfconvert2spfeq, auto simp add: assms)
  show "\<exists>x::'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>\<in>G. (spfConvert\<cdot>g::'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) \<triangleq>\<^sub>f x" using h1 a2 by auto
next
  fix g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assume a1: "F = Rep_cfun spfConvert ` G"
  assume a2: "g \<in> G"
  obtain f where "f \<in> F" and f_def: "f = spfConvert\<cdot>g" using a1 a2 by auto
  have h1: "f = spfConvert\<cdot>g \<and> g \<in> G" using a1 a2 f_def by auto
  have h2: "f \<triangleq>\<^sub>f g" by (subst f_def, subst spfconvert2spfeq, auto simp add: assms)
  show "\<exists>f::'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>\<in>G. (spfConvert\<cdot>f::'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) \<triangleq>\<^sub>f g"
    using a1 h1 h2 by auto
qed

theorem spscomp_commut_convert_general:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('Out) \<inter> chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and "\<not>chDomEmpty TYPE('Out \<union> 'fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut \<union> 'gOut) \<subseteq> chDom TYPE('Out)"
    and "\<not>chDomEmpty TYPE('Out \<union> 'gOut) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('fOut \<union> 'gOut) \<subseteq> chDom TYPE('Out)"
  shows "spsConvert\<cdot>(F \<Otimes> G) = (spsConvert\<cdot>(G \<Otimes> F)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using spfcomp_commut_convert_general[OF assms] image_cong by fastforce

theorem spscomp_commut_convert:
  fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
    and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
assumes "chDom TYPE('O1) \<inter> chDom TYPE('O2) = {}"
shows "F \<Otimes> G = spsConvert\<cdot>(G \<Otimes> F)"
  apply(subst spscomp_commut_convert_general)
  using assms by fastforce+

corollary spscomp_commut:
  fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
assumes "chDom TYPE('O1) \<inter> chDom TYPE('O2) = {}"
shows "(F \<Otimes> G) \<triangleq>\<^sub>F (G \<Otimes> F)"
  apply(rule spsconvert2spseq)
  apply(auto)[2]
  apply(rule spscomp_commut_convert)
  using assms by simp

theorem spscomp_assoc_convertl:
  fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
    and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
    and H::"('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>) set"
assumes "chDom TYPE('O1) \<inter> chDom TYPE('O2) = {}"
    and "chDom TYPE('O1) \<inter> chDom TYPE('O3) = {}"
  shows "F \<Otimes> G \<Otimes> H = spsConvert\<cdot>((F \<Otimes> G) \<Otimes> H)"
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using spfcomp_assoc_convertl[OF assms] image_cong by fastforce

theorem spscomp_assoc_convertr:
  fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
    and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
    and H::"('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>) set"
assumes "chDom TYPE('O1) \<inter> chDom TYPE('O2) = {}"
    and "chDom TYPE('O1) \<inter> chDom TYPE('O3) = {}"
  shows "(F \<Otimes> G) \<Otimes> H = spsConvert\<cdot>(F \<Otimes> G \<Otimes> H)"
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using spfcomp_assoc_convertr[OF assms, symmetric] image_cong by fastforce

corollary spscomp_assoc:
  fixes F::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
    and G::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set"
    and H::"('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>) set"
assumes "chDom TYPE('O1) \<inter> chDom TYPE('O2) = {}"
    and "chDom TYPE('O1) \<inter> chDom TYPE('O3) = {}"
  shows "((F \<Otimes> G) \<Otimes> H) \<triangleq>\<^sub>F (F \<Otimes> (G \<Otimes> H))"
  apply(rule spsconvert2spseq)
  apply(auto)[2]
  apply(rule spscomp_assoc_convertr)
  using assms by (simp_all)

lemma spscomp_weak:
  fixes fs::"('fIn::tchan\<^sup>\<Omega> \<rightarrow> 'fOut::tchan\<^sup>\<Omega>) set"
  and gs::"('gIn::tchan\<^sup>\<Omega> \<rightarrow> 'gOut::tchan\<^sup>\<Omega>) set"
  assumes "\<And>f g. f \<in> fs\<Longrightarrow>  g \<in> gs \<Longrightarrow> weak (f \<otimes> g)"
      and "spf \<in> (spsConvert\<cdot>(fs \<Otimes> gs)::('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set)"
      and "chDom TYPE('O2::tchan) \<subseteq> ((chDom TYPE('fOut)) \<union> (chDom TYPE('gOut)))"
      and "(chDom TYPE('I2::tchan)) = ((chDom TYPE('fIn)) \<union> (chDom TYPE('gIn))) - ((chDom TYPE('fOut)) \<union> (chDom TYPE('gOut)))"
    shows "weak spf"
proof (rule weakI) 
  obtain spf1 spf2 where ob: "spf1 \<in> fs"  "spf2 \<in> gs" "spf = spfConvert\<cdot>(spf1 \<otimes> spf2)"
    using assms by (auto simp add: spsConvert_def spsComp_def)
  then have comp_weak: "weak (spf1 \<otimes> spf2)"
    using assms(1) by blast
  fix sb::"'I2\<^sup>\<Omega>"
  have "#\<^sub>\<surd>((spf1 \<otimes> spf2)\<cdot>(sb\<star>)) \<le> #\<^sub>\<surd>(((spf1 \<otimes> spf2)\<cdot>(sb\<star>))\<star>::'O2\<^sup>\<Omega>)"
    by (simp add: sbtypecast_tlen assms(3))
  moreover have "#\<^sub>\<surd>((sb\<star>)::(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)\<^sup>\<Omega>) \<le> #\<^sub>\<surd>((spf1 \<otimes> spf2)\<cdot>(sb\<star>))"
    using comp_weak weak_def by blast
  moreover have "#\<^sub>\<surd>sb \<le> #\<^sub>\<surd>((sb\<star>)::(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)\<^sup>\<Omega>)"
    apply (rule sbtypecast_tlen)
    using assms(4) by auto
  ultimately have "#\<^sub>\<surd>sb \<le> #\<^sub>\<surd>(((spf1 \<otimes> spf2)\<cdot>(sb\<star>))\<star>::'O2\<^sup>\<Omega>)"
    by auto
  then show "#\<^sub>\<surd>sb \<le> #\<^sub>\<surd>(spf\<cdot>sb)"
    by (simp add: ob spfconvert_apply)
qed

lemma spscomp_strong:
  fixes fs::"('fIn::tchan\<^sup>\<Omega> \<rightarrow> 'fOut::tchan\<^sup>\<Omega>) set"
  and gs::"('gIn::tchan\<^sup>\<Omega> \<rightarrow> 'gOut::tchan\<^sup>\<Omega>) set"
  assumes "\<And>f g. f \<in> fs\<Longrightarrow>  g \<in> gs \<Longrightarrow> strong (f \<otimes> g)"
      and "spf \<in> (spsConvert\<cdot>(fs \<Otimes> gs)::('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set)"
      and "chDom TYPE('O2::tchan) \<subseteq> ((chDom TYPE('fOut)) \<union> (chDom TYPE('gOut)))"
      and "(chDom TYPE('I2::tchan)) = ((chDom TYPE('fIn)) \<union> (chDom TYPE('gIn))) - ((chDom TYPE('fOut)) \<union> (chDom TYPE('gOut)))"
    shows "strong spf"
proof (rule strongI) 
  obtain spf1 spf2 where ob: "spf1 \<in> fs"  "spf2 \<in> gs" "spf = spfConvert\<cdot>(spf1 \<otimes> spf2)"
    using assms by (auto simp add: spsConvert_def spsComp_def)
  then have comp_strong: "strong (spf1 \<otimes> spf2)"
    using assms(1) by blast
  fix sb::"'I2\<^sup>\<Omega>"
  have "#\<^sub>\<surd>((spf1 \<otimes> spf2)\<cdot>(sb\<star>)) \<le> #\<^sub>\<surd>(((spf1 \<otimes> spf2)\<cdot>(sb\<star>))\<star>::'O2\<^sup>\<Omega>)"
    by (simp add: sbtypecast_tlen assms(3))
  moreover have "lnsuc\<cdot>(#\<^sub>\<surd>((sb\<star>)::(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)\<^sup>\<Omega>)) \<le> #\<^sub>\<surd>((spf1 \<otimes> spf2)\<cdot>(sb\<star>))"
    using comp_strong strong_def by blast
  moreover have "lnsuc\<cdot>(#\<^sub>\<surd>sb) \<le> lnsuc\<cdot>(#\<^sub>\<surd>((sb\<star>)::(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)\<^sup>\<Omega>))"
    apply (simp,rule sbtypecast_tlen)
    using assms(4) by auto
  ultimately have "lnsuc\<cdot>(#\<^sub>\<surd>sb) \<le> #\<^sub>\<surd>(((spf1 \<otimes> spf2)\<cdot>(sb\<star>))\<star>::'O2\<^sup>\<Omega>)"
    using dual_order.trans by blast
  then show "lnsuc\<cdot>(#\<^sub>\<surd>sb) \<le> #\<^sub>\<surd>(spf\<cdot>sb)"
    by (simp add: ob spfconvert_apply)
qed

lemma sps_comp_unfold:
  assumes "spf \<in> spsConvert\<cdot>(sps1 \<Otimes> sps2)"
      and "\<And> spf1 spf2. spf1 \<in> sps1 \<Longrightarrow> spf2 \<in> sps2 \<Longrightarrow>
           P (spfConvert\<cdot>(spf1 \<otimes> spf2))"
  shows "P spf"
  using assms by (auto simp add: spsConvert.rep_eq spsComp_def)

text\<open>Next we lift the sequential composition (@{const spfCompSeq})
 to compose two \glspl{sps}.\<close> 

definition spsCompSeq  :: "(('In\<^sup>\<Omega> \<rightarrow> 'Intern\<^sup>\<Omega>) set) \<Rightarrow> (('Intern\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set) 
    \<Rightarrow> (('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)" where
"spsCompSeq = (\<lambda> sps1 sps2 . {spfCompSeq\<cdot>spf1\<cdot>spf2 | spf1 spf2. 
                                spf1 \<in> sps1 \<and> spf2 \<in> sps2})"

abbreviation spsCompSeq_abbr :: 
"('In\<^sup>\<Omega> \<rightarrow> 'Intern\<^sup>\<Omega>) set \<Rightarrow> ('Intern\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set 
  \<Rightarrow> ('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set"  (infixr "OOO" 100)
  where "f OOO g == spsCompSeq f g"

theorem spscompseq_assoc:
  shows "(F OOO G) OOO H = F OOO (G OOO H)"
  unfolding spsCompSeq_def apply auto[1]
  using spfcompseq_assoc_spfconvert apply fastforce
  using spfcompseq_assoc_spfconvert[symmetric] by fastforce

lemma spscomp_to_sequential:
  fixes f::"('In\<^sup>\<Omega> \<rightarrow> 'Intern\<^sup>\<Omega>) set"
    and g::"('Intern\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set"
  assumes "chDom TYPE ('In) \<inter> chDom TYPE ('Intern) = {}"
    and "chDom TYPE('In) \<inter> chDom TYPE('Out) = {}"
    and "chDom TYPE('Intern) \<inter> chDom TYPE('Out) = {}"
  shows "(spsConvert\<cdot>(f \<Otimes> g) ) = spsCompSeq f g"
  apply (simp add: spsCompSeq_def spsComp_def assms)
  apply (rule set_eqI)
  using mem_Collect_eq apply (simp add: spsConvert_def spsConvert.rep_eq)
  apply (subst image_def,simp)
  apply (simp add: spfConvert_def)
  apply auto[1]
  apply (subgoal_tac "sbTypeCast oo (fa \<otimes> ga) oo sbTypeCast = spfCompSeq\<cdot>fa\<cdot>ga")
  apply blast
  apply (rule cfun_eqI)
  apply (subst spfcomp_to_sequential[symmetric])
  apply (simp_all add: assms)
  apply (subgoal_tac "\<exists>x::(('In \<union> 'Intern) - 'Intern \<union> 'Out)\<^sup>\<Omega> \<rightarrow> ('Intern \<union> 'Out)\<^sup>\<Omega>. (x =  spf1 \<otimes> spf2) \<and>
         spfCompSeq\<cdot>spf1\<cdot>spf2 = sbTypeCast oo x oo sbTypeCast")
  apply blast
  apply auto[1]
  apply (rule cfun_eqI)
  apply (subst spfcomp_to_sequential[symmetric])
  by (simp_all add: assms)

lemma spsconvert_predicate:
  fixes SPS::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set"
  assumes "spf\<in> ((spsConvert\<cdot>SPS)::('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set)"
      and "\<And>(sb::'I1\<^sup>\<Omega>) spf. spf\<in>SPS \<Longrightarrow> P (sb\<star>) (spf\<cdot>sb\<star>)"
      and "chDom TYPE('O2) \<subseteq> chDom TYPE('O1)"
      and "chDom TYPE('I2) = chDom TYPE('I1)"
    shows "P sb (spf\<cdot>sb)"
proof -
  obtain spfRaw where "spfRaw\<in>SPS" and "spfConvert\<cdot>spfRaw = spf"
    by (metis assms(1) image_iff spsConvert.rep_eq)
  then show ?thesis
    apply(subst spfconvert_predicate, blast)
    by(simp add: assms)+
qed


theorem spscfcomp_set: 
  assumes "spf1 \<in> sps1"
      and "spf2 \<in> sps2"
  shows "spfCompSeq\<cdot>spf1\<cdot>spf2 \<in> spsCompSeq sps1 sps2"
  apply(simp add: spsCompSeq_def)
  using assms(1) assms(2) by auto


theorem spscfcomp_consistent: 
    assumes "spsIsConsistent sps1"
        and "spsIsConsistent sps2"
      shows "spsIsConsistent (spsCompSeq sps1 sps2)"
  apply(simp add: spsIsConsistent_def spsCompSeq_def)
  using assms spsIsConsistent_def by (metis neq_emptyD)


theorem spscfcomp_mono: assumes "sps1_ref \<subseteq> sps1"
  and "sps2_ref \<subseteq> sps2"
  shows "(spsCompSeq sps1_ref sps2_ref) \<subseteq> (spsCompSeq sps1 sps2)"
  apply(simp add: spsCompSeq_def)
  using assms by blast

lemma spscompseq_ex: assumes "x \<in> F1 OOO F2"
  shows "\<exists> x1\<in>F1. \<exists> x2\<in>F2. x = x2 oo x1"
  using assms apply(simp add: spsCompSeq_def spfCompSeq_def)
  by (metis cfcomp1)

lemma spscompseq_id1: "{ID} OOO F = F"
  by(simp add: spsCompSeq_def spfcompseq_insert)

lemma spscompseq_id2: "F OOO {ID} = F"
  by(simp add: spsCompSeq_def spfcompseq_insert)

lemma spscompseq_insert: "F OOO G = 
      { g oo f | f g. f \<in> F \<and> g \<in> G}"
  by(simp add: spsCompSeq_def spfcompseq_insert)

lemma seqcomp_spscompseq_eq: "F OOO G = F \<then> G"
  by (simp add: seqcomp_insert spscompseq_insert)

lemma spscompseq_asso: "(F OOO G) OOO H = F OOO (G OOO H)"
  apply(auto simp add: spsCompSeq_def spfcompseq_insert)[1]
  using cfun_eq_iff by fastforce+


definition spsCompPar  :: "('In1\<^sup>\<Omega> \<rightarrow> 'Out1\<^sup>\<Omega>)set \<Rightarrow> ('In2\<^sup>\<Omega> \<rightarrow> 'Out2\<^sup>\<Omega>)set \<Rightarrow> 
  (('In1 \<union> 'In2)\<^sup>\<Omega> \<rightarrow> ('Out1 \<union> 'Out2)\<^sup>\<Omega>) set" where 
"spsCompPar sps1 sps2 = {spfCompPar\<cdot>spf1\<cdot>spf2 | spf1 spf2. 
                                spf1 \<in> sps1 \<and> spf2 \<in> sps2}"

abbreviation spsCompPar_abbr :: 
"('In1\<^sup>\<Omega> \<rightarrow> 'Out1\<^sup>\<Omega>)set \<Rightarrow> ('In2\<^sup>\<Omega> \<rightarrow> 'Out2\<^sup>\<Omega>)set \<Rightarrow> 
  (('In1 \<union> 'In2)\<^sup>\<Omega> \<rightarrow> ('Out1 \<union> 'Out2)\<^sup>\<Omega>) set"  (infixr "\<parallel>" 100)
  where "f \<parallel> g == spsCompPar f g"

lemma spsconvert_spfconvert_id:
  assumes "chDom TYPE('a) \<subseteq> chDom TYPE('c)"
  assumes "chDom TYPE('b) \<subseteq> chDom TYPE('d)"
  shows "(spsConvert\<cdot>{(spfConvert::('a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>) \<rightarrow> ('c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>))\<cdot>x | x . P x}) = {x | x .P x}"
  apply(subst spsConvert_def, auto)
   apply(subst spfconvert_id)
  using assms apply auto[4]
  by (subst image_def, auto)

lemma spsconvert_spfconvert_cong:
  assumes "chDom TYPE('a) \<subseteq> chDom TYPE('c)"
  assumes "chDom TYPE('b) \<subseteq> chDom TYPE('d)"
  shows "(spsConvert\<cdot>{(spfConvert::('a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>) \<rightarrow> ('c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>))\<cdot>(F x) | x . P x}) = {(F x) | x .P x}"
  apply(subst spsConvert_def, auto)
   apply(subst spfconvert_id)
  using assms apply auto[4]
  by (subst image_def, auto)

theorem spscomppar_commu_spsconvert:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
  shows "spsCompPar F G = spsConvert\<cdot>(spsCompPar G F)"
  apply(auto simp add: spsCompPar_def spsConvert.rep_eq image_def)[1]
proof -
  fix f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>" and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assume fF: "f \<in> F" and  gG: "g \<in> G"
  obtain x where x_def: "x = spfCompPar\<cdot>g\<cdot>f" by simp
  have h1: "spfCompPar\<cdot>f\<cdot>g = spfConvert\<cdot>x"
    apply (simp add:  x_def)
    apply (rule spfcomppar_commu_spfconvert)
    by (simp add: assms)
  show "\<exists>x::('gIn \<union> 'fIn)\<^sup>\<Omega> \<rightarrow> ('gOut \<union> 'fOut)\<^sup>\<Omega>.
          (\<exists>(spf1::'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) spf2::'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>.
              x = spfCompPar\<cdot>spf1\<cdot>spf2 \<and> spf1 \<in> G \<and> spf2 \<in> F) \<and>
          spfCompPar\<cdot>f\<cdot>g = spfConvert\<cdot>x"
    using fF gG x_def h1 by auto
next
  fix f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>" and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assume fF: "f \<in> F" and gG: "g \<in> G"
  have h1: "spfConvert\<cdot>(spfCompPar\<cdot>g\<cdot>f) = spfCompPar\<cdot>f\<cdot>g"
    apply (subst spfcomppar_commu_spfconvert[symmetric])
    using assms by simp_all
  show " \<exists>(spf1a::'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) spf2a::'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>.
          spfConvert\<cdot>(spfCompPar\<cdot>g\<cdot>f) = spfCompPar\<cdot>spf1a\<cdot>spf2a \<and>
          spf1a \<in> F \<and> spf2a \<in> G"
    using fF gG h1 by auto
qed

corollary spscomppar_commu:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
  shows "spsCompPar F G \<triangleq>\<^sub>F spsCompPar G F"
  apply(rule spsconvert2spseq)
  using assms by (auto simp add: spscomppar_commu_spsconvert)

definition spsCompFeed  :: "('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)set \<Rightarrow> 
  (('In-'Out)\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)set" where 
"spsCompFeed sps = {spfCompFeed\<cdot>spf | spf. spf \<in> sps}"

lemma spscomp_parallel_serial:
  fixes F1 :: "('fin\<^sup>\<Omega> \<rightarrow> 'fintern\<^sup>\<Omega>) set"
  and   G1 :: "('gin\<^sup>\<Omega> \<rightarrow> 'gintern\<^sup>\<Omega>) set"
  and   F2 :: "('fintern\<^sup>\<Omega> \<rightarrow> 'fout\<^sup>\<Omega>) set"
  and   G2 :: "('gintern\<^sup>\<Omega> \<rightarrow> 'gout\<^sup>\<Omega>) set"
  assumes "chDom TYPE ('gintern) \<inter> chDom TYPE ('fintern) = {}"
  shows "spsCompPar (F1 OOO F2) (G1 OOO G2) 
      = (spsCompPar F1 G1) OOO (spsCompPar F2 G2)"
  apply(simp add: spscompseq_insert spsCompPar_def)
  using assms spfcomp_parallel_serial by (metis (no_types, opaque_lifting)) 

theorem spscomppar_mono: assumes "sps1_ref \<subseteq> sps1"
  and "sps2_ref \<subseteq> sps2"
  shows "(spsCompPar sps1_ref sps2_ref) \<subseteq> (spsCompPar sps1 sps2)"
  apply(simp add: spsCompPar_def)
  using assms by blast

method pred_solver uses inst2def assms =
((rule spscomp_predicatel2, simp,rule inst2def, (intro assms,blast, simp)+; fail) 
  | (rule spscomp_predicater2, simp, simp))+

lemma wrapped_sps_convert_eq: 
  fixes inputMapping::"'In \<Rightarrow> 'WrappedIn"
    and outputMapping::"'WrappedOut \<Rightarrow> 'Out"
assumes inputMapping_well: "\<And>c. ctype (Rep (inputMapping c)) \<subseteq> ctype (Rep c)"
    and inputMapping_req1: "\<And>c::'In. \<not>chDomEmpty TYPE('ConvOut) \<longrightarrow> Rep c \<in> chDom TYPE('In) \<longrightarrow> Rep c \<in> chDom TYPE('ConvIn) \<longrightarrow> Rep (inputMapping c) = Rep c"
    and inputMapping_req2: "\<And>c::'In. \<not>chDomEmpty TYPE('ConvOut) \<longrightarrow> Rep c \<in> chDom TYPE('In) \<longrightarrow> Rep c \<notin> chDom TYPE('ConvIn) \<longrightarrow> Rep (inputMapping c) \<notin> chDom TYPE('ConvIn)"
    and outputMapping_well: "\<And>c. ctype (Rep (outputMapping c)) \<subseteq> ctype (Rep c)"
    and outputMapping_req1: "\<And>c::'WrappedOut. \<not>chDomEmpty TYPE('Out) \<longrightarrow> Rep c \<in> chDom TYPE('ConvOut) \<longrightarrow> Rep (outputMapping c) = Rep c"
    and outputMapping_req2: "\<And>c::'ConvOut. \<not>chDomEmpty TYPE('Out) \<longrightarrow> \<not>chDomEmpty TYPE('ConvOut) \<longrightarrow>  Rep c \<notin> chDom TYPE('WrappedOut) \<longrightarrow> Rep c \<notin> chDom TYPE('Out)"
  shows "(spsConvert\<cdot>({sbRenameCh inputMapping} \<then> SPS \<then> {sbRenameCh outputMapping})::(('ConvIn\<^sup>\<Omega> \<rightarrow> 'ConvOut\<^sup>\<Omega>) set)) = spsConvert\<cdot>(SPS)"
  apply(subst seqcomp_image_sps)
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using wrapped_spf_convert_eq[OF assms] image_cong by fastforce

lemma sbrenamech_spsconv_swap:
  fixes F::"('In1\<^sup>\<Omega>\<rightarrow>'Out1\<^sup>\<Omega>) set"
    and inputMapping1::"'In2 \<Rightarrow> 'In3"
    and outputMapping1::"'Out3 \<Rightarrow> 'Out2"
    and inputMapping2::"'In1 \<Rightarrow> 'In4"
    and outputMapping2::"'Out4 \<Rightarrow> 'Out1"
assumes "\<And> c. ctype (Rep (outputMapping2 c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. ctype (Rep (outputMapping1 c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. ctype (Rep (inputMapping1 c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. ctype (Rep (inputMapping2 c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. Rep c \<in> chDom TYPE('Out3) \<longrightarrow> Rep c \<in> chDom TYPE('Out4) \<longrightarrow> Rep (outputMapping2 (Abs (Rep c))) = Rep (outputMapping1 c)"
    and "\<And> c. Rep c \<in> chDom TYPE('Out3) \<longrightarrow> Rep c \<notin> chDom TYPE('Out4) \<longrightarrow> Rep (outputMapping1 c) \<notin> chDom TYPE('Out1)"
    and "\<And> c. Rep c \<in> chDom TYPE('In1) \<longrightarrow> Rep c \<in> chDom TYPE('In2) \<longrightarrow> Rep (inputMapping1 (Abs (Rep c))) = Rep (inputMapping2 c)"
    and "\<And> c. Rep c \<in> chDom TYPE('In1) \<longrightarrow> Rep c \<notin> chDom TYPE('In2) \<longrightarrow> Rep (inputMapping2 c) \<notin> chDom TYPE('In3)"
  shows "{sbRenameCh inputMapping1} \<then> spsConvert\<cdot>F \<then> {sbRenameCh outputMapping1} = spsConvert\<cdot>({sbRenameCh inputMapping2} \<then> F \<then> {sbRenameCh outputMapping2})"
  apply(simp only: seqcomp_image_sps spsConvert.rep_eq image_image)
  apply(rule image_cong, simp)
  using sbrenamech_spfconv_swap[OF assms] by fastforce

lemma wrapped_sps_comp_set: "{i1} \<then> F \<then> {o1} \<Otimes> {i2} \<then> G \<then> {o2} = {(o1 oo f oo i1) \<otimes> (o2 oo g oo i2) | f g . f \<in> F \<and> g \<in> G}"
  apply(subst seqcomp_image_sps)+
  apply(simp add: spsComp_def)
  by blast

lemma context_refine_feedback:
  assumes "\<And>c a. c\<in>C \<Longrightarrow> a\<in>A \<Longrightarrow> \<exists>b\<in>B. a\<otimes>c = b\<otimes>c"
  shows "A \<Otimes> C \<subseteq> B \<Otimes> C"
  unfolding spsComp_def
  using assms by blast

lemma wrapped_sps_comp_eq:
  fixes i1::"'wIn1\<^sup>\<Omega> \<rightarrow> 'In1\<^sup>\<Omega>"
    and i2::"'wIn2\<^sup>\<Omega> \<rightarrow> 'In2\<^sup>\<Omega>"
    and i3::"(('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega> \<rightarrow> (('In1 \<union> 'In2) - 'Out1 \<union> 'Out2)\<^sup>\<Omega>"
    and o1::"'Out1\<^sup>\<Omega> \<rightarrow> 'wOut1\<^sup>\<Omega>"
    and o2::"'Out2\<^sup>\<Omega> \<rightarrow> 'wOut2\<^sup>\<Omega>"
    and o3::"('Out1 \<union> 'Out2)\<^sup>\<Omega> \<rightarrow> ('wOut1 \<union> 'wOut2)\<^sup>\<Omega>"
assumes "o3\<cdot>\<bottom> = \<bottom>"
    and "\<And>c out1 out2. Rep c \<in> chDom TYPE('wOut1) \<longrightarrow> o3\<cdot>(out1 \<uplus> out2) \<^enum> c = o1\<cdot>out1 \<^enum>\<^sub>\<star> c"
    and "\<And>c out1 out2. Rep c \<notin> chDom TYPE('wOut1) \<longrightarrow> o3\<cdot>(out1 \<uplus> out2) \<^enum> c = o2\<cdot>out2 \<^enum>\<^sub>\<star> c"
    and "\<And>c y (x:: (('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega>). \<not>chDomEmpty TYPE('In1) \<and> \<not>chDomEmpty TYPE('Out1) \<longrightarrow> Rep c \<in> chDom TYPE('Out1 \<union> 'Out2) \<longrightarrow> i1\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>1)  \<^enum>  c = y  \<^enum>\<^sub>\<star>  c"
    and "\<And>c y (x:: (('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega>). \<not>chDomEmpty TYPE('In2) \<and> \<not>chDomEmpty TYPE('Out2) \<longrightarrow> Rep c \<in> chDom TYPE('Out1 \<union> 'Out2) \<longrightarrow> i2\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>2)  \<^enum>  c = y  \<^enum>\<^sub>\<star>  c"
    and "\<And>c y (x:: (('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega>). \<not>chDomEmpty TYPE('In1) \<and> \<not>chDomEmpty TYPE('Out1) \<longrightarrow> Rep c \<notin> chDom TYPE('Out1 \<union> 'Out2) \<longrightarrow> i1\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>1)  \<^enum>  c = i3\<cdot>x  \<^enum>\<^sub>\<star>  c"
    and "\<And>c y (x:: (('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega>). \<not>chDomEmpty TYPE('In2) \<and> \<not>chDomEmpty TYPE('Out2) \<longrightarrow> Rep c \<notin> chDom TYPE('Out1 \<union> 'Out2) \<longrightarrow> i2\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>2)  \<^enum>  c = i3\<cdot>x  \<^enum>\<^sub>\<star>  c"
  shows "({i1} \<then> F \<then> {o1}) \<Otimes> ({i2} \<then> G \<then> {o2}) = {i3} \<then> (F \<Otimes> G) \<then> {o3}"
  apply(subst wrapped_sps_comp_set)
  apply(subst seqcomp_image_sps)
  apply(simp add: spsComp_def)
  using wrapped_spf_comp_eq[OF assms] by fastforce

lemma spscomp_convert_left: 
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut2) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut)"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut2)"
    and "\<not>chDomEmpty TYPE('gOut) \<longrightarrow> chDom TYPE('fOut) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut \<union> 'gOut) \<inter> chDom TYPE('fOut2 \<union> 'gOut) \<subseteq> chDom TYPE('fIn2)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut \<union> 'gOut \<union> 'fIn2 \<union> 'fOut2)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fIn2) \<inter> chDom TYPE('fOut2) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
  shows "(spsConvert\<cdot>(F)::('fIn2\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set) \<Otimes> G = spsConvert\<cdot>(F \<Otimes> G)"
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using spfcomp_convert_left[OF assms] apply auto[1] 
  by (metis image_eqI)

lemma spscomp_convert_right: 
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)" 
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('fOut \<union> 'gOut2) \<inter> chDom TYPE('fOut \<union> 'gOut) \<subseteq> chDom TYPE('gIn2)" 
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut \<union> 'gOut \<union> 'gIn2 \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gIn2) \<inter> chDom TYPE('gOut2) \<subseteq> chDom TYPE('fOut \<union> 'gOut)" 
  shows "F \<Otimes> (spsConvert\<cdot>(G)::('gIn2\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) set) = spsConvert\<cdot>(F \<Otimes> G)"
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using spfcomp_convert_right[OF assms] apply auto[1] 
  by (metis image_eqI)

lemma spscomp_convert_refinement_left:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and F'::"('fIn2\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "F' \<subseteq> spsConvert\<cdot>(F)"
    and "chDom TYPE('fOut2) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut)"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gOut \<union> 'Out) \<subseteq> chDom TYPE('fOut2)"
    and "\<not>chDomEmpty TYPE('gOut) \<longrightarrow> chDom TYPE('fOut) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut \<union> 'gOut) \<inter> chDom TYPE('fOut2 \<union> 'gOut) \<subseteq> chDom TYPE('fIn2)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut \<union> 'gOut \<union> 'fIn2 \<union> 'fOut2)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fIn2) \<inter> chDom TYPE('fOut2) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
    and "chDom TYPE('In) \<inter> chDom TYPE('fIn \<union> 'gIn) \<subseteq> chDom TYPE('fOut \<union> 'gOut \<union> ('fIn2 \<union> 'gIn) - 'fOut2)"
  shows "spsConvert\<cdot>(F' \<Otimes> G) \<subseteq> (spsConvert\<cdot>(F \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
proof -
  have a1: "spsConvert\<cdot>(F' \<Otimes> G) \<subseteq> spsConvert\<cdot>((spsConvert\<cdot>(F)::('fIn2\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set) \<Otimes> G)"
    apply(rule spsconvref)
    apply(rule spscomp_refinement[OF assms(1)])
    by simp
  show "?thesis"
    apply(rule subset_trans[OF a1])
    apply(subst spscomp_convert_left[OF assms(2) _ assms(4-8)])
    using assms(3) apply fastforce
    apply(subst spsconvert_merge)
    using assms(9) apply fastforce
    using assms(3) apply fastforce
    by simp
qed

lemma spscomp_move_left:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
assumes "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut \<union> 'hOut) \<subseteq> chDom TYPE('Out)"
    and "\<not>chDomEmpty TYPE('Out) \<longrightarrow> chDom TYPE('gIn \<union> 'hIn) \<inter> chDom TYPE('fOut) \<subseteq> chDom TYPE('In)"
    and "\<not>chDomEmpty TYPE('Out) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gIn \<union> 'hIn) \<subseteq> chDom TYPE('fOut \<union> 'gOut \<union> 'hOut \<union> 'In \<union> 'Out)"
    and "\<not>chDomEmpty TYPE('Out) \<longrightarrow> chDom TYPE('gIn \<union> 'hIn) \<inter> chDom TYPE('In) \<inter> chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut \<union> 'hOut)"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('hOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('hOut) = {}"
  shows "F \<Otimes> (spsConvert\<cdot>(G \<Otimes> H)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set) = spsConvert\<cdot>(G \<Otimes> F \<Otimes> H)"
  apply(subst spscomp_convert_right)
  using assms(1) apply fastforce
  using assms(2) apply fastforce
  apply fastforce
  using assms(3) apply fastforce
  using assms(4) apply fastforce
  apply(subst spscomp_assoc_convertl[OF assms(5-6)])
  apply(subst spsconvert_merge)
  apply fastforce+
  apply(subst spscomp_commut_convert)
  using assms(5) apply fastforce
  apply(subst spscomp_convert_left)
  apply fastforce+
  apply(subst spsconvert_merge)
  apply fastforce+
  apply(subst spscomp_assoc_convertr)
  using assms(5, 7) apply fastforce+
  apply(rule spsconvert_merge)
  by fastforce+

lemma spscomp_move_left2:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('hOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('hOut) = {}"
  shows "F \<Otimes> G \<Otimes> H = spsConvert\<cdot>(G \<Otimes> F \<Otimes> H)"
  apply(subst(4) spsconvert_eq[symmetric])
  apply(rule spscomp_move_left[OF _ _ _ _ assms])
  apply fastforce
  using assms(1,2) apply fastforce
  by fastforce+

lemma spscomp_commut2_convert:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut \<union> 'hOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('hOut) = {}"
  shows "spsConvert\<cdot>(F \<Otimes> G \<Otimes> H) = spsConvert\<cdot>(H \<Otimes> F \<Otimes> G)"
  apply(subst(2) spscomp_commut_convert)
  using assms(2) apply fastforce
  apply(subst spscomp_move_left)
  apply fastforce
  using assms(1) apply auto[5]
  using assms(2) apply fastforce
  apply(rule spsconvert_merge)
  by fastforce+

lemma spscomp_commut3_convert:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
    and I::"('iIn\<^sup>\<Omega> \<rightarrow> 'iOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut \<union> 'hOut \<union> 'iOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('hOut \<union> 'iOut) = {}"
    and "chDom TYPE('hOut) \<inter> chDom TYPE('iOut) = {}"
  shows "spsConvert\<cdot>(F \<Otimes> G \<Otimes> H \<Otimes> I) = spsConvert\<cdot>(I \<Otimes> F \<Otimes> G \<Otimes> H)"
  apply(subst(3) spscomp_commut_convert)
  using assms(3) apply fastforce
  apply(subst spscomp_move_left)
  apply fastforce
  using assms(2) apply auto[5]
  using assms(3) apply fastforce
  apply(subst spscomp_move_left)
  apply fastforce
  using assms(1) apply auto[5]
  using assms(2,3) apply fastforce
  apply(rule spsconvert_merge)
  by fastforce+

lemma spscomp_commut4_convert:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
    and I::"('iIn\<^sup>\<Omega> \<rightarrow> 'iOut\<^sup>\<Omega>) set"
    and J::"('jIn\<^sup>\<Omega> \<rightarrow> 'jOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut \<union> 'hOut \<union> 'iOut \<union> 'jOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('hOut \<union> 'iOut \<union> 'jOut) = {}"
    and "chDom TYPE('hOut) \<inter> chDom TYPE('iOut \<union> 'jOut) = {}"
    and "chDom TYPE('iOut) \<inter> chDom TYPE('jOut) = {}"
  shows "spsConvert\<cdot>(F \<Otimes> G \<Otimes> H \<Otimes> I \<Otimes> J) = spsConvert\<cdot>(J \<Otimes> F \<Otimes> G \<Otimes> H \<Otimes> I)"
  apply(subst(4) spscomp_commut_convert)
  using assms(4) apply fastforce
  apply(subst spscomp_move_left)
  apply fastforce
  using assms(3) apply auto[5]
  using assms(4) apply fastforce
  apply(subst spscomp_move_left)
  apply fastforce
  using assms(2) apply auto[5]
  using assms(3,4) apply fastforce
  apply(subst spscomp_move_left)
  apply fastforce
  using assms(1) apply auto[5]
  using assms(2,3,4) apply fastforce
  apply(rule spsconvert_merge)
  by fastforce+

lemma spscomp_convert_left_simple:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut2) \<subseteq> chDom TYPE('fOut)"
    and "chDom TYPE('fIn) \<subseteq> chDom TYPE('fIn2)"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut2)"
    and "\<not>chDomEmpty TYPE('gOut) \<longrightarrow> chDom TYPE('fOut) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
  shows "(spsConvert\<cdot>(F)::('fIn2\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set) \<Otimes> G = spsConvert\<cdot>(F \<Otimes> G)"
  apply(rule spscomp_convert_left[OF _ assms(3,4)  _ assms(5)])
  using assms(1,2) by fastforce+

lemma spscomp_convert_right_simple:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('gOut2) \<subseteq> chDom TYPE('gOut)"
    and "chDom TYPE('gIn) \<subseteq> chDom TYPE('gIn2)"
    and "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
  shows "F \<Otimes> (spsConvert\<cdot>(G)::('gIn2\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) set) = spsConvert\<cdot>(F \<Otimes> G)"
  apply(rule spscomp_convert_right[OF assms(3) _ assms(4)])
  using assms(1,2) by fastforce+

lemma spscomp_convert_left_simple_merge:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut2) \<subseteq> chDom TYPE('fOut)"
    and "chDom TYPE('fIn) \<subseteq> chDom TYPE('fIn2)"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut2)"
    and "\<not>chDomEmpty TYPE('gOut) \<longrightarrow> chDom TYPE('fOut) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
  shows "spsConvert\<cdot>((spsConvert\<cdot>(F)::('fIn2\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) set) \<Otimes> G) = (spsConvert\<cdot>(F \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_convert_left_simple[OF assms(1-5)])
  apply(rule spsconvert_merge_simple[OF _ assms(6)])
  using assms(1-2) by fastforce

lemma spscomp_convert_right_simple_merge:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('gOut2) \<subseteq> chDom TYPE('gOut)"
    and "chDom TYPE('gIn) \<subseteq> chDom TYPE('gIn2)"
    and "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
  shows "spsConvert\<cdot>(F \<Otimes> (spsConvert\<cdot>(G)::('gIn2\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) set)) = (spsConvert\<cdot>(F \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_convert_right_simple[OF assms(1-4)])
  apply(rule spsconvert_merge_simple[OF _ assms(5)])
  using assms(1-2) by fastforce

lemma spscomp_convert_right2_simple_merge:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('gOut2) \<subseteq> chDom TYPE('gOut)"
    and "chDom TYPE('gIn) \<subseteq> chDom TYPE('gIn2)"
    and "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('hOut) \<longrightarrow> chDom TYPE('hIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('hOut \<union> 'gOut2)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('hOut \<union> 'fOut \<union> 'gOut2)"
  shows "spsConvert\<cdot>(H \<Otimes> F \<Otimes> (spsConvert\<cdot>(G)::('gIn2\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) set)) = (spsConvert\<cdot>(H \<Otimes> F \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_convert_right_simple[OF assms(1-4)])
  apply(subst spscomp_convert_right_simple)
  using assms(1) apply fastforce
  using assms(1-2) apply fastforce
  using assms(5) apply fastforce
  apply fastforce
  apply(rule spsconvert_merge_simple[OF _ assms(6)])
  using assms(1-2) by fastforce

lemma spscomp_convert_right3_simple_merge:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
    and I::"('iIn\<^sup>\<Omega> \<rightarrow> 'iOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('gOut2) \<subseteq> chDom TYPE('gOut)"
    and "chDom TYPE('gIn) \<subseteq> chDom TYPE('gIn2)"
    and "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('hOut) \<longrightarrow> chDom TYPE('hIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('hOut \<union> 'gOut2)"
    and "\<not>chDomEmpty TYPE('iOut) \<longrightarrow> chDom TYPE('iIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('iOut \<union> 'gOut2)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('iOut \<union> 'hOut \<union> 'fOut \<union> 'gOut2)"
  shows "spsConvert\<cdot>(I \<Otimes> H \<Otimes> F \<Otimes> (spsConvert\<cdot>(G)::('gIn2\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) set)) = (spsConvert\<cdot>(I \<Otimes> H \<Otimes> F \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_convert_right_simple[OF assms(1-4)])
  apply(subst spscomp_convert_right_simple)
  using assms(1) apply fastforce
  using assms(1-2) apply fastforce
  using assms(5) apply fastforce
  apply fastforce
  apply(subst spscomp_convert_right_simple)
  using assms(1) apply fastforce
  using assms(1-2) apply fastforce
  using assms(6) apply fastforce
  apply fastforce
  apply(rule spsconvert_merge_simple[OF _ assms(7)])
  using assms(1-2) by fastforce

lemma spscomp_swap_left:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('hOut) = {}"
    and "chDom TYPE('hOut) \<inter> chDom TYPE('gOut) = {}"
  shows "spsConvert\<cdot>(F \<Otimes> G \<Otimes> H) = spsConvert\<cdot>(G \<Otimes> F \<Otimes> H)"
  apply(subst spscomp_assoc_convertl[OF assms(1-2)])
  apply(subst spsconvert_merge)
  apply auto[2]
  apply(subst spscomp_commut_convert[OF assms(1)])
  apply(subst spscomp_convert_left)
  apply auto[7]
  apply(subst spsconvert_merge)
  apply auto[2]
  apply(subst spscomp_assoc_convertr)
  using assms(1, 3) apply auto[2]
  apply(subst spsconvert_merge)
  by fastforce+

lemma spscomp_swap_right: 
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('hOut) \<inter> chDom TYPE('gOut) = {}"
  shows "spsConvert\<cdot>(F \<Otimes> G \<Otimes> H) = spsConvert\<cdot>(F \<Otimes> H \<Otimes> G)"
  apply(subst(4) spscomp_commut_convert)
  using assms(1) apply simp
  apply(subst spscomp_convert_right)
  apply auto[5]
  apply(subst spsconvert_merge)
  by fastforce+

lemma spscomp_add_left_ref:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('Out) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
  shows "spsConvert\<cdot>(F \<Otimes> G) \<subseteq> (spsConvert\<cdot>(G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using spfcomp_add_remove_left[OF assms] by fastforce

lemma spscomp_add_right_ref: 
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('gOut) \<inter> chDom TYPE('Out) \<subseteq> chDom TYPE('fOut)"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
  shows "spsConvert\<cdot>(F \<Otimes> G) \<subseteq> (spsConvert\<cdot>(F)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using spfcomp_add_remove_right[OF assms] by fastforce

lemma spscomp_add_mid_ref:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('hOut) = {}"
    and "chDom TYPE('hOut) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('Out \<union> 'fIn \<union> 'hIn) \<subseteq> chDom TYPE('fOut \<union> 'hOut)"
  shows "spsConvert\<cdot>(F \<Otimes> G \<Otimes> H) \<subseteq> (spsConvert\<cdot>(F \<Otimes> H)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_swap_right[OF assms(3)])
  apply(subst spscomp_assoc_convertl[OF assms(2,1)])
  apply(subst spsconvert_merge; force?)
  apply(rule spscomp_add_right_ref)
  using assms(4) apply fastforce
  using assms(4) apply fastforce
  by simp

lemma spscomp_add_remove_left_eq: 
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('Out) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    and "F \<noteq> {}"
  shows "spsConvert\<cdot>(F \<Otimes> G) = (spsConvert\<cdot>(G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(rule subset_antisym)
  apply(rule spscomp_add_left_ref[OF assms(1-3)])
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using assms(4) spfcomp_add_remove_left[OF assms(1-3), symmetric] by fastforce

lemma spscomp_add_remove_right_eq: 
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('gOut) \<inter> chDom TYPE('Out) \<subseteq> chDom TYPE('fOut)"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
    and "G \<noteq> {}"
  shows "spsConvert\<cdot>(F \<Otimes> G) = (spsConvert\<cdot>(F)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(rule subset_antisym)
  apply(rule spscomp_add_right_ref[OF assms(1-3)])
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using assms(4) spfcomp_add_remove_right[OF assms(1-3), symmetric] by fastforce

lemma spscomp_add_remove_mid_eq:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('hOut) = {}"
    and "chDom TYPE('hOut) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('Out \<union> 'fIn \<union> 'hIn) \<subseteq> chDom TYPE('fOut \<union> 'hOut)"
    and "G \<noteq> {}"
  shows "spsConvert\<cdot>(F \<Otimes> G \<Otimes> H) = (spsConvert\<cdot>(F \<Otimes> H)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_swap_right[OF assms(3)])
  apply(subst spscomp_assoc_convertl[OF assms(2,1)])
  apply(subst spsconvert_merge; force?)
  apply(rule spscomp_add_remove_right_eq[OF _ _ _ assms(5)])
  using assms(4) apply fastforce
  using assms(4) apply fastforce
  by simp

lemma unfold_subarchitecture:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and H::"('hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>) set"
    and I::"('iIn\<^sup>\<Omega> \<rightarrow> 'iOut\<^sup>\<Omega>) set"
assumes "chDom TYPE('Out2) \<subseteq> chDom TYPE('gOut \<union> 'hOut)"
    and "chDom TYPE('gIn \<union> 'hIn) \<subseteq> chDom TYPE('In2 \<union> 'gOut \<union> 'hOut)"
    and "\<not>chDomEmpty TYPE('iOut) \<longrightarrow> chDom TYPE('gOut \<union> 'hOut) \<inter> chDom TYPE('iIn) \<subseteq> chDom TYPE('Out2)"
    and "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('gOut \<union> 'hOut) \<inter> chDom TYPE('fIn) \<subseteq> chDom TYPE('Out2)"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('fOut \<union> 'Out2 \<union> 'iOut)"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('hOut) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('iOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('hOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('iOut) = {}"
    and "chDom TYPE('hOut) \<inter> chDom TYPE('iOut) = {}"
  shows "spsConvert\<cdot>(F \<Otimes> (spsConvert\<cdot>(G \<Otimes> H)::('In2\<^sup>\<Omega> \<rightarrow> 'Out2\<^sup>\<Omega>) set) \<Otimes> I) = (spsConvert\<cdot>((G \<Otimes> F) \<Otimes> H \<Otimes> I)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set)"
  apply(subst spscomp_convert_left_simple[OF assms(1)])
  using assms(2) apply fastforce
  using assms(10, 11) apply fastforce
  using assms(3) apply fastforce
  apply fastforce
  apply(subst spscomp_convert_right_simple)
  using assms(1) apply fastforce
  using assms(1-2) apply fastforce
  using assms(4) apply fastforce
  apply fastforce
  apply(subst spsconvert_merge_simple[OF _ assms(5)])
  using assms(1-2) apply fastforce
  apply(subst spscomp_assoc_convertl)
  using assms(6, 7) apply fastforce
  using assms(8) apply fastforce
  apply(subst spsconvert_merge_simple)
  apply fastforce
  using assms(1, 5) apply fastforce
  apply(subst spscomp_assoc_convertl)
  using assms(6) apply fastforce
  using assms(7) apply fastforce
  apply(subst spscomp_convert_left_simple) 
  apply fastforce+
  apply(subst spsconvert_merge_simple)
  apply fastforce
  using assms(1, 5) apply fastforce
  apply(subst(2) spscomp_assoc_convertr)
  using assms(7, 9) apply fastforce
  using assms(8, 10) apply fastforce
  apply(subst spscomp_commut_convert[OF assms(6)])
  apply(subst spscomp_convert_left_simple_merge)
  apply fastforce+
  apply(rule spsconvert_merge_simple)
  apply fastforce
  using assms(1, 5) by fastforce

lemma sps_connector_replace:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and m1::"'Out1 \<Rightarrow> 'In1"
    and m2::"'Out2 \<Rightarrow> 'In2"
assumes "\<And>c. ctype (Rep (m1 c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (m2 c)) \<subseteq> ctype (Rep c)"
    and "\<And>c::'Out2. Rep c \<in> chDom TYPE('Out1) \<longrightarrow> Rep c \<in> chDom TYPE('Out2) \<longrightarrow> Rep (m1 (Abs (Rep c))) = Rep (m2 c)"
    and "chDom TYPE('In2) \<subseteq> chDom TYPE('In1)"
    and "chDom TYPE('Out2) \<subseteq> chDom TYPE('Out1)"
    and "chDom TYPE('Out1) \<inter> chDom TYPE('fIn \<union> 'fOut \<union> 'Out) \<subseteq> chDom TYPE('Out2)"
    and "chDom TYPE('In1) \<inter> chDom TYPE('Out1) = {}"
  shows "(spsConvert\<cdot>({sbRenameCh m1} \<Otimes> F)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set) = spsConvert\<cdot>({sbRenameCh m2} \<Otimes> F)"
  apply(simp add: spsConvert.rep_eq spsComp_def)
  using spf_connector_replace[OF assms] image_cong by fastforce

lemma spscomp_connect_component:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and m1::"'mOut \<Rightarrow> 'mIn"
    and m2::"'fIn \<Rightarrow> 'fIn2"
assumes "\<And>c. ctype (Rep (m1 c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (m2 c)) \<subseteq> ctype (Rep c)"
    and "chDom TYPE('fIn) \<subseteq> chDom TYPE('mOut)"
    and "chDom TYPE('fIn2) \<subseteq> chDom TYPE('mIn)"
    and "chDom TYPE('fIn2) \<inter> chDom TYPE('mOut \<union> 'fOut) = {}"
    and "chDom TYPE('mIn) \<inter> chDom TYPE('mOut) = {}"
    and "\<And>c::'mOut. Rep c \<in> chDom TYPE('mOut) \<Longrightarrow> Rep (m1 c) \<in> chDom TYPE('mIn)"
    and "\<And>c::'fIn. Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (m1 (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'fIn) - 'mOut \<union> 'fOut)"
    and "\<And>c. Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (m2 c) = Rep (m1 (Abs (Rep c)))"
  shows "{sbRenameCh m1} \<Otimes> {sbRenameCh m2} \<then> F = spsConvert\<cdot>({sbRenameCh m1} \<Otimes> F)"
  apply(simp add: spsConvert.rep_eq spsComp_def seqcomp_image)
  using spfcomp_connect_component[OF assms] image_cong by fastforce

lemma spscomp_connect_component_with_context:
  fixes F::"('fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>) set"
    and G::"('gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) set"
    and m1::"'mOut \<Rightarrow> 'mIn"
    and m2::"'fIn \<Rightarrow> 'fIn2"
assumes "\<And>c. ctype (Rep (m1 c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (m2 c)) \<subseteq> ctype (Rep c)"
    and "chDom TYPE('mOut) \<inter> chDom TYPE('fOut) = {}"
    and "chDom TYPE('mOut) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('Out) \<subseteq> chDom TYPE('mOut \<union> 'fOut \<union> 'gOut)"
    and "chDom TYPE('fIn) \<subseteq> chDom TYPE('mOut)"
    and "chDom TYPE('fIn2) \<subseteq> chDom TYPE('mIn)"
    and "chDom TYPE('fIn2) \<inter> chDom TYPE('mOut \<union> 'fOut) = {}"
    and "chDom TYPE('mIn) \<inter> chDom TYPE('mOut) = {}"
    and "\<And>c::'mOut. Rep c \<in> chDom TYPE('mOut) \<Longrightarrow> Rep (m1 c) \<in> chDom TYPE('mIn)"
    and "\<And>c::'fIn. Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (m1 (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'fIn) - 'mOut \<union> 'fOut)"
    and "\<And>c. Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (m2 c) = Rep (m1 (Abs (Rep c)))"
  shows "(spsConvert\<cdot>({sbRenameCh m1} \<Otimes> {sbRenameCh m2} \<then> F \<Otimes> G)::('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set) = spsConvert\<cdot>({sbRenameCh m1} \<Otimes> F \<Otimes> G)"
  apply(subst spscomp_assoc_convertl[OF assms(3,4)])
  apply(subst spscomp_assoc_convertl[OF assms(3,4)])
  apply(subst spsconvert_merge_simple[OF _ assms(5)], fastforce)
  apply(subst spsconvert_merge_simple[OF _ assms(5)], fastforce)
  apply(subst spscomp_connect_component[OF assms(1,2,6-12)], simp, simp)
  apply(rule spscomp_convert_left_simple_merge, fastforce)
  using assms(6,8) apply auto[1]
  apply auto[3]
  using assms(5) by auto[1]

end

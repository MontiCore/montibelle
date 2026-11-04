theory USimulation
  imports SPSComp
begin


definition isCHRP :: "('abstr\<^sup>\<Omega> \<rightarrow> 'conc\<^sup>\<Omega>) set \<Rightarrow> ('conc\<^sup>\<Omega> \<rightarrow> 'abstr\<^sup>\<Omega>) set \<Rightarrow> bool" where
"isCHRP R A \<equiv> R \<noteq> {} \<and> A \<noteq> {} \<and> (\<forall>r\<in>R. \<forall>a\<in>A. a oo r = ID)"

lemma chrp_rep_inj: assumes "isCHRP R A"
  shows "\<forall>r\<in>R. inj (Rep_cfun r)"
  using assms isCHRP_def
  by (metis (mono_tags, opaque_lifting) ID1 cfcomp2 inj_on_inverseI neq_emptyD)

lemma chrp_abs_surj:assumes "isCHRP R A"
  shows "\<forall>a\<in>A. surj (Rep_cfun a)"
  using assms isCHRP_def
  by (metis (no_types, opaque_lifting) ID1 cfcomp2 neq_emptyD surjI)

lemma chrp_spscompseq_id: assumes "isCHRP R A"
  shows "R OOO A = {ID}"
  apply(auto simp add: spsCompSeq_def spfcompseq_insert)[1]
  using assms apply (simp add: isCHRP_def)
  using assms isCHRP_def by (metis ex_in_conv)

lemma chrp_compseq: 
  assumes "isCHRP R1 A1"
      and "isCHRP R2 A2"
    shows "isCHRP (R2 OOO R1) (A1 OOO A2)"
  using assms apply(auto simp add: isCHRP_def spscompseq_insert assoc_oo)[1]
  by (metis (no_types, opaque_lifting) assoc_oo ID1 cfcomp2 cfun_eqI)



definition isUSim where
"isUSim RI F' AO F \<equiv> (RI OOO F' OOO AO \<subseteq> F)"

definition isU1Sim where
"isU1Sim F' AI F RO \<equiv> (F' \<subseteq> AI OOO F OOO RO)"

definition isDownwardSim where
"isDownwardSim RI F' F RO \<equiv> (RI OOO F' \<subseteq> F OOO RO)"

definition isUpwardSim where
"isUpwardSim F' AO AI F \<equiv> (F' OOO AO \<subseteq> AI OOO F)"



lemma u1sim2downsim: assumes "isCHRP RI AI"
  and "isU1Sim F' AI F RO"
shows "isDownwardSim RI F' F RO"
proof(simp add: isDownwardSim_def) 
  have "RI OOO F' \<subseteq> RI OOO AI OOO F OOO RO"
    using assms(2)
    by (simp add: isU1Sim_def spscfcomp_mono)
  then show "RI OOO F' \<subseteq> F OOO RO"
    using chrp_spscompseq_id assms(1) spscompseq_asso
    by (metis spscompseq_id1)
qed

lemma u1sim2upsim: assumes "isCHRP RO AO"
  and "isU1Sim F' AI F RO"
shows "isUpwardSim F' AO AI F"
proof(simp add: isUpwardSim_def) 
  have "F' OOO AO \<subseteq> AI OOO F OOO RO OOO AO"
    using assms(2) isU1Sim_def spscfcomp_mono
    by (metis order_refl spscompseq_asso)
  then show "F' OOO AO \<subseteq> AI OOO F" 
    using chrp_spscompseq_id assms(1)
    by (metis spscompseq_id2)
qed

lemma downsim2usim: assumes "isCHRP RO AO"
  and "isDownwardSim RI F' F RO"
shows "isUSim RI F' AO F"
proof(simp add: isUSim_def) 
  have "RI OOO F' OOO AO \<subseteq> F OOO RO OOO AO"
    using assms(2) isDownwardSim_def spscfcomp_mono
    by (metis order_refl spscompseq_asso)
  then show "RI OOO F' OOO AO \<subseteq> F"  
    using chrp_spscompseq_id assms(1)
    by (metis spscompseq_id2)
qed

lemma upsim2usim: assumes "isCHRP RI AI"
  and "isUpwardSim F' AO AI F"
shows "isUSim RI F' AO F"
proof(simp add: isUSim_def) 
  have "RI OOO F' OOO AO \<subseteq> RI OOO AI OOO F"
    using assms(2) isUpwardSim_def spscfcomp_mono
    by (metis order_refl) 
  then show "RI OOO F' OOO AO \<subseteq> F"  
    using chrp_spscompseq_id assms(1) spscompseq_asso
    by (metis spscompseq_id1)
qed



lemma spscompseq_insert3: "F OOO G OOO H = 
      { h oo g oo f | f g h. f \<in> F \<and> g \<in> G \<and> h \<in> H}"
  apply(auto simp add: spscompseq_insert)[1]
  using cfun_eq_iff by fastforce+


lemma u1sim_parcomp_h:
  fixes F :: "('fAbsIn\<^sup>\<Omega> \<rightarrow> 'fAbsOut\<^sup>\<Omega>) set"
  and   G :: "('gAbsIn\<^sup>\<Omega> \<rightarrow> 'gAbsOut\<^sup>\<Omega>) set"
  and   F' :: "('fConcIn\<^sup>\<Omega> \<rightarrow> 'fConcOut\<^sup>\<Omega>) set"
  and   G' :: "('gConcIn\<^sup>\<Omega> \<rightarrow> 'gConcOut\<^sup>\<Omega>) set"
  assumes "F' \<subseteq> AInF OOO F OOO ROutF"
  and "G' \<subseteq> AInG OOO G OOO ROutG"
  and "chDom TYPE('gAbsIn) \<inter> chDom TYPE('fAbsIn) = {}"  
  and "chDom TYPE('gAbsOut) \<inter> chDom TYPE('fAbsOut) = {}"  
shows "(spsCompPar F' G') \<subseteq> (spsCompPar AInF AInG) OOO (spsCompPar F G) OOO (spsCompPar ROutF ROutG)"
proof - 
  have h1: "(spsCompPar F' G') \<subseteq> (spsCompPar (AInF OOO F OOO ROutF) ( AInG OOO G OOO ROutG))"
    apply(simp add: spsCompPar_def)
    using assms(1) assms(2) by blast
  have h2: "(spsCompPar (AInF OOO F OOO ROutF) ( AInG OOO G OOO ROutG))
        = (spsCompPar AInF AInG) OOO (spsCompPar F G) OOO (spsCompPar ROutF ROutG)"
    using assms(3) assms(4)
    by (simp add: spscomp_parallel_serial)
  show ?thesis
    using h1 h2 by simp 
qed

lemma u1sim_parcomp:
  fixes F :: "('fAbsIn\<^sup>\<Omega> \<rightarrow> 'fAbsOut\<^sup>\<Omega>) set"
  and   G :: "('gAbsIn\<^sup>\<Omega> \<rightarrow> 'gAbsOut\<^sup>\<Omega>) set"
  and   F' :: "('fConcIn\<^sup>\<Omega> \<rightarrow> 'fConcOut\<^sup>\<Omega>) set"
  and   G' :: "('gConcIn\<^sup>\<Omega> \<rightarrow> 'gConcOut\<^sup>\<Omega>) set"
  assumes "isU1Sim F' AInF F ROutF"
  and "isU1Sim G' AInG G ROutG"
  and "chDom TYPE('gAbsIn) \<inter> chDom TYPE('fAbsIn) = {}"  
  and "chDom TYPE('gAbsOut) \<inter> chDom TYPE('fAbsOut) = {}"  
  shows "isU1Sim (spsCompPar F' G') (spsCompPar AInF AInG) (spsCompPar F G) (spsCompPar ROutF ROutG)"
  using assms apply(simp add: isU1Sim_def)
  using u1sim_parcomp_h by blast

lemma downsim_parcomp:
  fixes F1 :: "('absIn1\<^sup>\<Omega> \<rightarrow> 'absOut1\<^sup>\<Omega>) set"
  and   F2 :: "('absIn2\<^sup>\<Omega> \<rightarrow> 'absOut2\<^sup>\<Omega>) set"
  and   F1' :: "('concIn1\<^sup>\<Omega> \<rightarrow> 'concOut1\<^sup>\<Omega>) set"
  and   F2' :: "('concIn2\<^sup>\<Omega> \<rightarrow> 'concOut2\<^sup>\<Omega>) set"
  assumes "isDownwardSim RI1 F1' F1 RO1"
  and "isDownwardSim RI2 F2' F2 RO2"
  and "chDom TYPE('concIn1) \<inter> chDom TYPE('concIn2) = {}"
  and "chDom TYPE('absOut1) \<inter> chDom TYPE('absOut2) = {}"
  shows "isDownwardSim (spsCompPar RI1 RI2) (spsCompPar F1' F2') 
                     (spsCompPar F1 F2) (spsCompPar RO1 RO2)"
  using assms(1) assms(2) apply(simp add: isDownwardSim_def)
  apply(subst spscomp_parallel_serial [symmetric])
  using assms(3) apply auto[1]
  apply(subst spscomp_parallel_serial [symmetric])
  using assms(4) apply auto[1]
  by (simp add: spscomppar_mono)


lemma downsim_seqcomp:
  assumes "isDownwardSim R0 F1' F1 R1"
  and "isDownwardSim R1 F2' F2 R2"
shows "isDownwardSim R0 (F1' OOO F2') (F1 OOO F2) R2"
proof -
  have "R0 OOO F1' OOO F2' \<subseteq> F1 OOO R1 OOO F2'"
    using assms(1) isDownwardSim_def spscfcomp_mono
    by (metis order_refl spscompseq_asso)
  then show ?thesis
    apply(simp add: isDownwardSim_def)
    using spscompseq_asso by (metis (no_types, opaque_lifting) assms(2) 
          dual_order.trans isDownwardSim_def order_refl spscfcomp_mono)
qed


lemma u1sim_feedcomp_h:
  fixes A  :: "('concIn\<^sup>\<Omega> \<rightarrow> 'absIn\<^sup>\<Omega>) set"
  and   R  :: "('absOut\<^sup>\<Omega> \<rightarrow> 'concOut\<^sup>\<Omega>) set"
  and   F  :: "('absIn\<^sup>\<Omega> \<rightarrow> 'absOut\<^sup>\<Omega>) set"  
  and   F' :: "('concIn\<^sup>\<Omega> \<rightarrow> 'concOut\<^sup>\<Omega>) set"
assumes "isU1Sim F' A F R"
shows "(spsCompFeed F') \<subseteq> spsCompFeed (A OOO F OOO R)"
  using assms apply(simp add: isU1Sim_def spsCompFeed_def)
  by auto

lemma u1sim_feedcomp_spf:
  fixes A  :: "('conc\<^sup>\<Omega> \<rightarrow> 'abs\<^sup>\<Omega>)"
  and   R  :: "('abs\<^sup>\<Omega> \<rightarrow> 'conc\<^sup>\<Omega>)"
  and   F  :: "('abs\<^sup>\<Omega> \<rightarrow> 'abs\<^sup>\<Omega>)"  
  and   G  :: "('conc\<^sup>\<Omega> \<rightarrow> 'conc\<^sup>\<Omega>)"
  assumes "A oo R = ID"
  and "G = R oo F oo A"
shows "(spfCompFeed\<cdot>G)\<cdot>z = (R oo spfCompFeed\<cdot>F)\<cdot>(z\<star>)"
proof - 
  have h1: "(\<Squnion>i::nat. iterate i\<cdot>((F oo A) oo R)\<cdot>\<bottom>) = (\<Squnion>i::nat. iterate i\<cdot>F\<cdot>\<bottom>)"
    by (metis assms(1) ID2 assoc_oo)
  show ?thesis
    apply(simp add: spfCompFeed_def assms(2))
    apply(subst fix_rolling [symmetric])
    by(simp add: fix_def2 h1)
qed

lemma u1sim_feedcomp:
  fixes A  :: "('conc\<^sup>\<Omega> \<rightarrow> 'abs\<^sup>\<Omega>) set"
  and   R  :: "('abs\<^sup>\<Omega> \<rightarrow> 'conc\<^sup>\<Omega>) set"
  and   F  :: "('abs\<^sup>\<Omega> \<rightarrow> 'abs\<^sup>\<Omega>) set"  
  and   G  :: "('conc\<^sup>\<Omega> \<rightarrow> 'conc\<^sup>\<Omega>) set"
  assumes "isCHRP R A"
  and "isU1Sim G A F R"
shows "(spsCompFeed G) \<subseteq> spsConvert\<cdot>((spsCompFeed F) OOO R)"
proof(auto)
  fix x
  assume a1: "x \<in> spsCompFeed G"
  then obtain g where x_def: "x = spfCompFeed\<cdot>g"
        and g_def: "g\<in>G"
    by(auto simp add: spsCompFeed_def)
  then obtain a f r where g_comp: "g = r oo f oo a"
        and a_def: "a\<in>A"
        and f_def: "f\<in>F"
        and r_def: "r\<in>R"
    using assms(2) by(auto simp add: isU1Sim_def spscompseq_insert3)
  have h1: "a oo r = ID"
    using assms(1) by(simp add: isCHRP_def a_def r_def)
  have "x = (r oo spfCompFeed\<cdot>f) oo sbTypeCast"
    apply(simp add: x_def)
    apply(rule cfun_eqI)
    using u1sim_feedcomp_spf h1 g_comp by fastforce
  then have h2: "x = sbTypeCast oo (r oo spfCompFeed\<cdot>f) oo sbTypeCast"
    by (simp add: cfun_eqI)
  show "x \<in> spsConvert\<cdot>(spsCompFeed F OOO R)"
    apply(auto simp add: h2 spsConvert_def spfConvert.rep_eq spsCompFeed_def spscompseq_insert)[1]
    apply(rule imageI)
    using f_def r_def by auto
qed

lemma spfcompfeed_insert: "spfCompFeed\<cdot>spf\<cdot>sb = fix\<cdot>(spf oo (\<Lambda> x. (sb \<uplus>\<^sub>- x)))"
  by(simp add: spfCompFeed_def oo_def)

lemma u1sim_feedcomp_general_spf:
  fixes F  :: "(('absIn \<union> 'absFeed)\<^sup>\<Omega> \<rightarrow> ('absOut \<union> 'absFeed)\<^sup>\<Omega>)"  
  and   G  :: "(('concIn \<union> 'concFeed)\<^sup>\<Omega> \<rightarrow> ('concOut \<union> 'concFeed)\<^sup>\<Omega>)"
  and   A\<^sub>I  :: "('concIn\<^sup>\<Omega> \<rightarrow> 'absIn\<^sup>\<Omega>)"
  and   R\<^sub>O  :: "('absOut\<^sup>\<Omega> \<rightarrow> 'concOut\<^sup>\<Omega>)"
  and   A  :: "('concFeed\<^sup>\<Omega> \<rightarrow> 'absFeed\<^sup>\<Omega>)"
  and   R  :: "('absFeed\<^sup>\<Omega> \<rightarrow> 'concFeed\<^sup>\<Omega>)"
  assumes "A oo R = ID"
  and "G = (spfCompPar\<cdot>R\<^sub>O\<cdot>R) oo F oo (spfCompPar\<cdot>A\<^sub>I\<cdot>A)"
  and "chDom TYPE('absIn) \<inter> chDom TYPE('absFeed) = {}"
  and "chDom TYPE('concIn) \<inter> chDom TYPE('concFeed) = {}"
  and "chDom TYPE('concOut) \<inter> chDom TYPE('concFeed) = {}"
  and "chDom TYPE('concIn) \<inter> chDom TYPE('concOut) = {}"
  and "chDom TYPE('absIn) \<inter> chDom TYPE('absOut) = {}"
shows "(spfCompFeed\<cdot>G)\<cdot>z = ((spfCompPar\<cdot>R\<^sub>O\<cdot>R) oo (spfCompFeed\<cdot>F) oo (spfConvert\<cdot>A\<^sub>I))\<cdot>z"
proof - 
  have h01: "\<And>x. (z \<uplus>\<^sub>- (R\<^sub>O\<cdot>(x\<star>\<^sub>1) \<uplus> R\<cdot>(x\<star>\<^sub>2))\<star>\<^sub>2) = R\<cdot>(x\<star>\<^sub>2)"
    apply(rule sb_eqI, simp)
    by (meson assms(5) disjoint_iff_not_equal sbunion_getchr)
  have h02: "\<And>x. A\<cdot>(z \<uplus>\<^sub>- (R\<^sub>O\<cdot>(x\<star>\<^sub>1) \<uplus> R\<cdot>(x\<star>\<^sub>2))\<star>\<^sub>2) = (x\<star>\<^sub>2)"
    apply(simp add: h01)
    by (metis assms(1) ID1 cfcomp2)

  have h03: "\<And>x. z \<uplus>\<^sub>- (R\<^sub>O\<cdot>(x\<star>\<^sub>1) \<uplus> R\<cdot>(x\<star>\<^sub>2))\<star>\<^sub>1 = (z\<star>)"
    apply(rule sb_eqI, simp)
    apply(subst sbunion_getchl)
    using assms(4) assms(6) by auto
  have h04: "\<And>x.  A\<^sub>I\<cdot>(z \<uplus>\<^sub>- (R\<^sub>O\<cdot>(x\<star>\<^sub>1) \<uplus> R\<cdot>(x\<star>\<^sub>2))\<star>\<^sub>1) = spfConvert\<cdot>A\<^sub>I\<cdot>z"
    by(simp add: h03 spfConvert_def)

  have h05: "\<And>x::('absOut \<union> 'absFeed)\<^sup>\<Omega>. ((spfConvert\<cdot>A\<^sub>I\<cdot>z \<uplus> (x\<star>\<^sub>2))::('absIn \<union> 'absFeed)\<^sup>\<Omega>) 
               = ((spfConvert\<cdot>A\<^sub>I\<cdot>z \<uplus>\<^sub>- x)::('absIn \<union> 'absFeed)\<^sup>\<Omega>)"
    apply(rule sb_eqI, simp)  
    apply(case_tac "Rep c \<in> chDom TYPE('absIn)")
     apply(simp)
     apply(subst sbunion_getchl) 
    using assms(3) assms(7) apply(auto)[1]
    apply(auto simp add: spfConvert_def)[1]
    apply(subst sbtypecast_getch2)
    using assms by auto

  have h2: "fix\<cdot>(F oo spfCompPar\<cdot>A\<^sub>I\<cdot>A oo (\<Lambda> x. z \<uplus>\<^sub>- x) oo spfCompPar\<cdot>R\<^sub>O\<cdot>R) =
            fix\<cdot>(F oo (\<Lambda> x. spfConvert\<cdot>A\<^sub>I\<cdot>z \<uplus>\<^sub>- x))"
    apply(simp add: oo_def spfCompPar_def h02 h04)
    by (simp add: h05)

  show ?thesis
    apply(simp add: spfcompfeed_insert assms(2))
    apply(simp add: assoc_oo[symmetric])
    apply(subst fix_rolling [symmetric])
    apply(simp add: assoc_oo [symmetric])
    by(simp add: h2)
qed

lemma u1sim_feedcomp_general:
  fixes F  :: "(('absIn \<union> 'absFeed)\<^sup>\<Omega> \<rightarrow> ('absOut \<union> 'absFeed)\<^sup>\<Omega>) set"  
  and   G  :: "(('concIn \<union> 'concFeed)\<^sup>\<Omega> \<rightarrow> ('concOut \<union> 'concFeed)\<^sup>\<Omega>) set"
  and   A\<^sub>I  :: "('concIn\<^sup>\<Omega> \<rightarrow> 'absIn\<^sup>\<Omega>) set"
  and   R\<^sub>O  :: "('absOut\<^sup>\<Omega> \<rightarrow> 'concOut\<^sup>\<Omega>) set"
  and   A  :: "('concFeed\<^sup>\<Omega> \<rightarrow> 'absFeed\<^sup>\<Omega>) set"
  and   R  :: "('absFeed\<^sup>\<Omega> \<rightarrow> 'concFeed\<^sup>\<Omega>) set"
  assumes "isCHRP R A"
  and "isU1Sim G (spsCompPar A\<^sub>I A) F (spsCompPar R\<^sub>O R)"
  and "chDom TYPE('absIn) \<inter> chDom TYPE('absFeed) = {}"
  and "chDom TYPE('concIn) \<inter> chDom TYPE('concFeed) = {}"
  and "chDom TYPE('concOut) \<inter> chDom TYPE('concFeed) = {}"
  and "chDom TYPE('concIn) \<inter> chDom TYPE('concOut) = {}"
  and "chDom TYPE('absIn) \<inter> chDom TYPE('absOut) = {}"
  shows "isU1Sim (spsCompFeed G) (spsConvert\<cdot>A\<^sub>I)  (spsCompFeed F) (spsCompPar R\<^sub>O R)"
proof(auto simp add: isU1Sim_def)
  fix x
  assume a1: "x \<in> spsCompFeed G"
  then obtain g where x_def: "x = spfCompFeed\<cdot>g"
        and g_def: "g\<in>G"
    by(auto simp add: spsCompFeed_def)
  then obtain ai a f ro r where g_comp: "g = (spfCompPar\<cdot>ro\<cdot>r) oo f oo (spfCompPar\<cdot>ai\<cdot>a)"
        and a_def: "a\<in>A"
        and ai_def: "ai\<in>A\<^sub>I"
        and f_def: "f\<in>F"
        and r_def: "r\<in>R"
        and ro_def: "ro\<in>R\<^sub>O"
    using assms(2) by(auto simp add: isU1Sim_def spscompseq_insert3 spsCompPar_def)
  have h1: "a oo r = ID"
    using assms(1) by(simp add: isCHRP_def a_def r_def)
  have h2: "x = (spfCompPar\<cdot>ro\<cdot>r) oo (spfCompFeed\<cdot>f) oo (spfConvert\<cdot>ai)"
    apply(simp add: x_def)
    apply(rule cfun_eqI, simp only: g_comp)
    apply(rule u1sim_feedcomp_general_spf [where A="a"])
    by(simp_all add: h1 assms)
  show "x \<in> (spsConvert\<cdot>A\<^sub>I) OOO (spsCompFeed F) OOO (spsCompPar R\<^sub>O R)"
    apply(auto simp add: h2 spsConvert_def spsCompFeed_def spscompseq_insert3 spsCompPar_def)[1]
    using ai_def f_def r_def ro_def imageI by blast
qed


definition sbEQselect::"'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> channel set \<Rightarrow> bool" where
"sbEQselect sb1 sb2 cs \<equiv> \<forall> c\<in>cs. (sb1 \<^enum> ((Abs c)::'cs1) = sb2 \<^enum> ((Abs c)::'cs2))"

definition sbEQmax::"'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> bool" where
"sbEQmax sb1 sb2 \<equiv> sbEQselect sb1 sb2 (chDom TYPE('cs1) \<inter> chDom TYPE('cs2))"

lemma "sbEQmax sb sb"
  by(simp add: sbEQmax_def sbEQselect_def)

lemma assumes "myMagicRefinement (spsCompPar A1 A2) A"
  shows  "(A1 OOO S1 OOO R1) \<Otimes> (A2 OOO S2 OOO R2) \<subseteq> A OOO (S1 \<Otimes> S2) OOO (spsCompPar R1 R2)"
  apply(simp add: spsComp_def)
  oops





lemma "(New1 \<Otimes> New2) \<subseteq> Original \<Longrightarrow> 
    Umgebund \<Otimes> (New1 \<Otimes> New2) \<subseteq> Umgebund \<Otimes> Original"
  by simp


end

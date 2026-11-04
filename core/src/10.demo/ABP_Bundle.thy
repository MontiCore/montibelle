theory ABP_Bundle
  imports tscomponent.TsLocale sps.SPSComp
begin


fun Bob_h :: "bool \<Rightarrow> (nat \<times> bool) tsyn \<Rightarrow> (bool \<times> (nat tsyn \<times> bool tsyn)) set" where
B1:   "Bob_h Ack Eps = {(Ack, (Eps, Eps))}" |
B2_3: "Bob_h Ack (TSynMsg pair) = (if snd pair = Ack 
            then {( \<not>Ack,(TSynMsg (fst pair), TSynMsg Ack))} 
            else {( Ack, (Eps, (TSynMsg (\<not>Ack))))})"

definition Bob_init :: "(bool \<times> nat tsyn \<times> bool tsyn) set" where
"Bob_init = {(True,Eps,Eps)}"


interpretation Bob: tsStrongGen "(\<lambda> (). Bob_h)" "(\<lambda> (). Bob_init)" fin fout
  apply standard
  apply simp_all
  oops


print_theorems


definition Bob_init_weak :: "(bool ) set" where
"Bob_init_weak = {(True)}"



fun fin::"((nat \<times> bool) tsyn \<Rightarrow> unit \<Rightarrow> M)"where
"fin Eps _ = Timed (Tsyn Eps)"|
"fin (TSynMsg (a,b)) _ = Timed (Tsyn (TSynMsg (msg.PROD (NAT a) (BOOL b))))"

instantiation unit::"{tschan}"
begin
definition Rep_unit::"unit \<Rightarrow> channel"where
"Rep_unit _ = (CH ''unit'' TTsyn {msg.PROD (NAT a) (BOOL b) | a b . True})"

definition Abs_unit::"channel \<Rightarrow> unit"where
"Abs_unit _ = ()"

instance
  oops
end

fun fout::"(nat tsyn \<times> bool tsyn) \<Rightarrow> bool \<Rightarrow> M"where
"fout (a,b) True = Timed (Tsyn (map_tsyn NAT a))"|
"fout (a,b) False = Timed (Tsyn (map_tsyn BOOL b))"


instantiation bool::"{tschan}"
begin
fun Rep_bool::"bool \<Rightarrow> channel"where
"Rep_bool True = (CH ''nat'' TTsyn (range NAT))"|
"Rep_bool False = (CH ''bool'' TTsyn (range BOOL))"

definition Abs_bool::"channel \<Rightarrow> bool"where
"Abs_bool = inv Rep"

instance
  oops
end


interpretation Bob_weak: tsWeakGen "(\<lambda> (). Bob_h)" "(\<lambda> (). Bob_init_weak)" fin fout
  apply standard
  apply simp_all
  oops
 





lemma bob_weak_eps_stream_sntimes:assumes"spf\<in> Bob_weak.StateSemw_stream param s"
  shows "snth n (spf\<cdot>\<up>\<sim>\<^sup>\<infinity>) = (\<sim>, \<sim>)"
  using assms
proof(induction n arbitrary: spf s)
  case 0
  then obtain nspf ns out where step_def:"spf\<cdot>(\<up>\<sim> \<Zcat> (\<up>\<sim>\<^sup>\<infinity>)) = \<up>out \<Zcat> nspf\<cdot>\<up>\<sim>\<^sup>\<infinity> \<and> nspf\<in> Bob_weak.StateSemw_stream param ns \<and> (ns,out) \<in> (Bob_weak.transitionC param s Eps)"
    using Bob_weak.statesemw_stream_step
    by blast
  then show ?case
    apply (subst sinftimes_unfold)apply simp
    by(simp add: autTransition.rep_eq Bob_weak.ndaw_stream.rep_eq Bob_weak.transitionC_def)
next
  case (Suc n)
  then obtain nspf ns out where step_def:"spf\<cdot>(\<up>\<sim> \<Zcat> (\<up>\<sim>\<^sup>\<infinity>)) = \<up>out \<Zcat> nspf\<cdot>\<up>\<sim>\<^sup>\<infinity> \<and> nspf\<in> Bob_weak.StateSemw_stream param ns \<and> (ns,out) \<in> (Bob_weak.transitionC param s Eps)"
    using Bob_weak.statesemw_stream_step
    by blast
  then show ?case
    apply (subst sinftimes_unfold)apply simp
    apply(simp add: autTransition.rep_eq Bob_weak.ndaw_stream.rep_eq Bob_weak.transitionC_def)
    apply(rule Suc.IH)
    using step_def by blast
qed

lemma bob_weak_eps_stream:assumes"spf\<in> Bob_weak.Semw_stream param"
  shows "spf\<cdot>(\<up>Eps\<^sup>\<infinity>) = (\<up>(Eps,Eps)\<^sup>\<infinity>)"
  apply(rule snths_eq)
  using assms apply auto
  apply(rule bob_weak_eps_stream_sntimes)
  using assms apply(simp add: sem_def autInitConfig.rep_eq Bob_weak.ndaw_stream.rep_eq)
  apply auto
  by(simp add:  Bob_init_weak_def)

lemma sbegen2sbgen_rule:assumes "spf \<in>  Bob_weak.Sem param"
  and "P i (ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>(i)))))"
and "\<And>x. (getterSB\<cdot>(spf\<cdot>x)) = ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf\<cdot>x))"
and "\<And>x. spf\<cdot>(setterSB\<cdot>x) = spf\<cdot>(sbeGen.setterSB fin\<cdot>x)"
shows "P i (getterSB\<cdot>(spf\<cdot>(setterSB\<cdot>i)))"
  by(simp add: assms)


lemma sbegen_holds:
  assumes "spf \<in>  Bob_weak.Sem param"
  shows "(ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>(\<up>Eps\<^sup>\<infinity>))))) = (\<up>Eps\<^sup>\<infinity>, \<up>Eps\<^sup>\<infinity>)"
  apply(rule Bob_weak.sem2streamsem_rule[where param = param])
  apply(subst bob_weak_eps_stream,simp_all add: ssplit.rep_eq)
  apply (metis slen_sup_sinftimes sprojfst_szipl1 sprojsnd_szipl1 szip2sinftimes)
  using assms by simp

lemma sbgen_holds: assumes "spf \<in>  Bob_weak.Sem param"
and "\<And>x. (getterSB\<cdot>(spf\<cdot>x)) = ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf\<cdot>x))"
and "\<And>x. spf\<cdot>(setterSB\<cdot>x) = spf\<cdot>(sbeGen.setterSB fin\<cdot>x)"
shows "(getterSB\<cdot>(spf\<cdot>(setterSB\<cdot>(\<up>Eps\<^sup>\<infinity>)))) = (\<up>Eps\<^sup>\<infinity>, \<up>Eps\<^sup>\<infinity>)"
  apply(rule sbegen2sbgen_rule)
  using assms sbegen_holds by simp_all

lemma bob_weak_stateSem_singleton: "is_singleton (Bob_weak.StateSemw_stream param bool)"
  apply (rule is_singletonI')
   apply (simp add: statesem_notempty) 
  apply (rule cfun_eqI)
proof -
  fix x y xa
  assume x:"x \<in> Bob_weak.StateSemw_stream param bool"
  assume y:"y \<in> Bob_weak.StateSemw_stream param bool"
  show " x\<cdot>xa = y\<cdot>xa"
    using x y
    apply simp
  proof (induction xa arbitrary : x y bool)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step a xa)
    obtain nspf_x ns_x out_x where
    step_x_def: "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" and
        nspf_x:  "nspf_x \<in> Bob_weak.StateSemw_stream param ns_x"and
       trans_x:  "(ns_x,out_x) \<in> (Bob_weak.transitionC param bool a)"
      using Bob_weak.statesemw_stream_step x
      by (metis (full_types) old.unit.exhaust step.prems(1))

    obtain nspf_y ns_y out_y where 
    step_y_def: "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" and
        nspf_y:  "nspf_y \<in> Bob_weak.StateSemw_stream param ns_y"and
       trans_y:  "(ns_y,out_y) \<in> (Bob_weak.transitionC param bool a)"
      using Bob_weak.statesemw_stream_step y
      by (metis (full_types) old.unit.exhaust step.prems(2))


    have outAndns_eq:"out_x = out_y \<and> ns_x = ns_y"
      proof (cases a)
        case Eps
        with trans_x trans_y show ?thesis using Bob_weak.transitionC_def
          by force
      next
        case (Msg a)
        then show ?thesis
          using trans_x trans_y using Bob_weak.transitionC_def
          by (auto simp: split: if_splits)
      qed

      then have out_eq: "out_x = out_y"
        by simp

      from \<open>out_x = out_y \<and> ns_x = ns_y\<close> have ns_eq: "ns_x = ns_y" by simp

      from step_x_def have "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" by simp
      from step_y_def have "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" by simp
      from this out_eq have"y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_y\<cdot>xa" by simp

      from step.IH ns_eq nspf_x nspf_y out_eq step_x_def step_y_def
      show ?case
        apply auto
        apply (metis step.IH)
        by (metis step.IH)
  qed 
qed



lemma bob_weak_step_simp0[simp]:assumes"spf\<in> Bob_weak.StateSemw_stream param bool"
  shows "spf\<cdot>(\<up>(Eps) \<Zcat> s) = \<up>(Eps, Eps) \<Zcat> spf\<cdot>(s)"
proof -
    obtain nspf ns  out where 
    step_def: "spf\<cdot>(\<up>(Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> Bob_weak.StateSemw_stream param ns"and 
       trans:  "(ns,out) \<in> (Bob_weak.transitionC param bool (Eps))"
      using Bob_weak.statesemw_stream_step assms  by blast

    from this have out:"out = (Eps, Eps)" using Bob_weak.transitionC_def Bob_h.simps
      by (metis case_unit insert_not_empty prod.inject singleton_iff)
    from assms nspf trans have ns: "ns = bool"using Bob.transitionC_def
      by simp  
    from ns nspf assms have eq: "spf = nspf"
      by (metis (mono_tags, lifting) Abs_unit_cases bob_weak_stateSem_singleton
          is_singleton_def singleton_iff)
  from this step_def nspf  ns show "spf\<cdot>(\<up>(Eps) \<Zcat> s) = \<up>(Eps, Eps) \<Zcat> spf\<cdot>(s)"
    using eq out by blast
qed


lemma bob_weak_step_simp1[simp]:assumes"spf\<in> Bob_weak.StateSemw_stream param bool"
  assumes "spf2 \<in> Bob_weak.StateSemw_stream param (\<not>bool)"
  shows "spf\<cdot>(\<up>(TSynMsg (m,bool)) \<Zcat> s) = \<up>(( TSynMsg m, TSynMsg (bool))) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg (m,bool)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Bob_weak.StateSemw_stream param ns"and 
       trans:  "(ns,out) \<in> (Bob_weak.transitionC param bool (TSynMsg (m,bool)))"
      using Bob_weak.statesemw_stream_step assms by blast

    from trans have "out = (( TSynMsg m, TSynMsg (bool)))" using Bob_weak.transitionC_def Bob_h.simps
        by force

    moreover from assms nspf trans have "ns = (\<not>bool)" using Bob.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using bob_weak_stateSem_singleton
        apply auto
        apply (metis is_singleton_def singleton_iff)
        by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg (m, bool)) \<Zcat> s) = \<up>(TSynMsg m, TSynMsg bool) \<Zcat> spf2\<cdot>s"
  by (simp add: step_def) 
qed

lemma bob_weak_step_simp2[simp]:assumes"spf\<in> Bob_weak.StateSemw_stream param bool"
  shows "spf\<cdot>(\<up>(TSynMsg (m,\<not>bool)) \<Zcat> s) = \<up>(Eps, TSynMsg (\<not>bool)) \<Zcat> spf\<cdot>(s)"
proof-
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg (m,\<not>bool)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Bob_weak.StateSemw_stream param ns"and 
       trans:  "(ns,out) \<in> (Bob_weak.transitionC param bool (TSynMsg (m,\<not>bool)))"
      using Bob_weak.statesemw_stream_step assms by blast
    from trans have "out = (Eps, TSynMsg (\<not>bool))" using Bob_weak.transitionC_def Bob_h.simps
        by force

    moreover from assms nspf trans have "ns = (bool)" using Bob.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf" using bob_weak_stateSem_singleton
        apply auto
       apply (metis is_singleton_some_elem singletonD)
       by (metis is_singleton_some_elem singletonD)
        
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg (m,\<not>bool)) \<Zcat> s) = \<up>(Eps, TSynMsg (\<not>bool)) \<Zcat> spf\<cdot>(s)"
  by (simp add:step_def) 
qed


lemma bob_weak_snth_fst:assumes"spf\<in> Bob_weak.StateSemw_stream param bool"
  assumes "Fin n < #s"  
  shows "snth n (fst (ssplit\<cdot>(spf\<cdot>(s)))) = snth n (smap (map_tsyn fst)\<cdot>s) \<or> snth n (fst (ssplit\<cdot>(spf\<cdot>(s)))) = Eps"
  using assms
proof(induction n arbitrary: spf bool s)
  case 0
  obtain spf2 where spf2_def:" spf2 \<in> Bob_weak.StateSemw_stream param (\<not>bool)"
    by (meson neq_emptyD statesem_notempty)
  then show ?case
    using "0.prems"
    apply(simp)
    apply(cases s;simp)
    apply(case_tac a;simp)
    apply(subst bob_weak_step_simp0[where bool=bool and param = param],simp_all)
    apply(metis(full_types) "0.prems"(1) old.unit.exhaust)
    apply(simp add: ssplit.rep_eq)
    apply(case_tac aa;simp)
    apply(case_tac "b=bool";simp)
    using bob_weak_step_simp1[of spf param bool spf2]
    apply(subst bob_weak_step_simp1[of spf param bool spf2],simp_all)
    apply(metis(full_types) "0.prems"(1) old.unit.exhaust)
    apply(simp add: ssplit.rep_eq)
    apply(subst bob_weak_step_simp2[where bool=bool and param = param],simp_all)
    apply(metis(full_types) "0.prems"(1) old.unit.exhaust)
    apply(simp add: ssplit.rep_eq)
    using "0.prems"(1) by force
next
  case (Suc n)
  obtain spf2 where spf2_def:" spf2 \<in> Bob_weak.StateSemw_stream param (\<not>bool)"
    by (meson neq_emptyD statesem_notempty)
  then show ?case 
    using Suc
        apply(simp)
    apply(cases s;simp)
    apply(case_tac a;simp)
    apply(subst bob_weak_step_simp0[where bool=bool and param = param],simp_all)
    apply (metis Suc.prems(1) old.unit.exhaust)
     apply(simp add: ssplit.rep_eq)
    apply (metis Suc.prems(1) bob_weak_step_simp0 snth_scons sprojfst_scons)
    apply(case_tac aa;simp)
    apply(case_tac "b=bool";simp)
    apply(subst bob_weak_step_simp1[where bool=bool and param = param],simp_all)
          apply (metis Suc.prems(1) old.unit.exhaust) defer
      apply(simp add: ssplit.rep_eq)
    using Suc.prems(1)
     apply fastforce
    apply (simp add: ssplit.rep_eq)
      apply(subst bob_weak_step_simp1[where bool=bool and param = param],simp_all)
    using Suc.prems(1) apply force
    by (metis Suc.IH fst_eqD spf2_def
        ssplit.rep_eq)
qed


lemma bob_weak_snd:assumes"spf\<in> Bob_weak.StateSemw_stream param bool"
  shows "snd (ssplit\<cdot>(spf\<cdot>(s))) = smap (map_tsyn snd)\<cdot>s"
apply(simp add: ssplit.rep_eq )
  using assms
proof(induction s arbitrary: spf bool)
  case adm
  then show ?case 
    apply(rule adm_all)+
    apply(rule adm_imp)
    by simp_all
next
  case bottom
  then show ?case 
    using assms by (simp add: ssplit.rep_eq)
next
  case (step a s)
  obtain spf2 where spf2_def:" spf2 \<in> Bob_weak.StateSemw_stream param (\<not>bool)"
    by (meson neq_emptyD statesem_notempty)
  then show ?case 
    using step
    apply(cases a;simp)
    apply(subst bob_weak_step_simp0[where bool=bool and param=param])
    using step.prems apply blast
     apply (simp)
    apply(case_tac aa;simp)
    apply(case_tac "b=bool";simp)
    using step.IH step.prems
    apply force
    using step.prems by force
qed


lemma bob_strong_stateSem_singleton: "is_singleton (Bob.StateSems_stream param bool)"
  apply (rule is_singletonI')
   apply (simp add: statesem_notempty) 
  apply (rule cfun_eqI)
proof -
  fix x y xa
  assume x:"x \<in> Bob.StateSems_stream param bool"
  assume y:"y \<in> Bob.StateSems_stream param bool"
  show " x\<cdot>xa = y\<cdot>xa"
    using x y
    apply simp
  proof (induction xa arbitrary : x y bool)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step a xa)
    obtain nspf_x ns_x out_x where
    step_x_def: "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" and
        nspf_x:  "nspf_x \<in> Bob.StateSems_stream param ns_x"and
       trans_x:  "(ns_x,out_x) \<in> (Bob.transitionC param bool a)"
      using Bob.statesems_stream_step x
      by (metis (full_types) old.unit.exhaust step.prems(1))

    obtain nspf_y ns_y out_y where 
    step_y_def: "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" and
        nspf_y:  "nspf_y \<in> Bob.StateSems_stream param ns_y"and
       trans_y:  "(ns_y,out_y) \<in> (Bob.transitionC param bool a)"
      using Bob.statesems_stream_step y
      by (metis (full_types) old.unit.exhaust step.prems(2))


    have outAndns_eq:"out_x = out_y \<and> ns_x = ns_y"
      proof (cases a)
        case Eps
        with trans_x trans_y show ?thesis using Bob.transitionC_def
          by force
      next
        case (Msg a)
        then show ?thesis
          using trans_x trans_y using Bob.transitionC_def
          by (auto simp: split: if_splits)
      qed

      then have out_eq: "out_x = out_y"
        by simp

      from \<open>out_x = out_y \<and> ns_x = ns_y\<close> have ns_eq: "ns_x = ns_y" by simp

      from step_x_def have "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" by simp
      from step_y_def have "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" by simp
      from this out_eq have"y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_y\<cdot>xa" by simp

      from step.IH ns_eq nspf_x nspf_y out_eq step_x_def step_y_def
      show ?case
        apply auto
        apply (metis step.IH)
        by (metis step.IH)
  qed 
qed



lemma bob_strong_step_simp0[simp]:assumes"spf\<in> Bob.StateSems_stream param bool"
  shows "spf\<cdot>(\<up>(Eps) \<Zcat> s) = \<up>(Eps, Eps) \<Zcat> spf\<cdot>(s)"
proof -
    obtain nspf ns  out where 
    step_def: "spf\<cdot>(\<up>(Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> Bob.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Bob.transitionC param bool (Eps))"
      using Bob.statesems_stream_step assms by blast

    from this have out:"out = (Eps, Eps)" using Bob.transitionC_def Bob_h.simps
      by (metis case_unit insert_not_empty prod.inject singleton_iff)

    from assms nspf trans have ns: "ns = bool"using Bob.transitionC_def
      by simp  

    from ns nspf assms have eq: "spf = nspf"
      by (metis (mono_tags, lifting) Abs_unit_cases bob_strong_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(Eps) \<Zcat> s) = \<up>(Eps, Eps) \<Zcat> spf\<cdot>(s)"
    using eq out by blast

qed


lemma bob_strong_step_simp1[simp]:assumes"spf\<in> Bob.StateSems_stream param bool"
  assumes "spf2 \<in> Bob.StateSems_stream param (\<not>bool)"
  shows "spf\<cdot>(\<up>(TSynMsg (m,bool)) \<Zcat> s) = \<up>(( TSynMsg m, TSynMsg (bool))) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg (m,bool)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Bob.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Bob.transitionC param bool (TSynMsg (m,bool)))"
      using Bob.statesems_stream_step assms by blast

    from trans have "out = (( TSynMsg m, TSynMsg (bool)))" using Bob.transitionC_def Bob_h.simps
        by force

    moreover from assms nspf trans have "ns = (\<not>bool)" using Bob.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using bob_strong_stateSem_singleton
        apply auto
        apply (metis is_singleton_def singleton_iff)
        by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg (m, bool)) \<Zcat> s) = \<up>(TSynMsg m, TSynMsg bool) \<Zcat> spf2\<cdot>s"
  by (simp add: step_def) 
qed

lemma bob_strong_step_simp2[simp]:assumes"spf\<in> Bob.StateSems_stream param bool"
  shows "spf\<cdot>(\<up>(TSynMsg (m,\<not>bool)) \<Zcat> s) = \<up>(Eps, TSynMsg (\<not>bool)) \<Zcat> spf\<cdot>(s)"
proof-
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg (m,\<not>bool)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Bob.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Bob.transitionC param bool (TSynMsg (m,\<not>bool)))"
      using Bob.statesems_stream_step assms by blast

    from trans have "out = (Eps, TSynMsg (\<not>bool))" using Bob.transitionC_def Bob_h.simps
        by force

    moreover from assms nspf trans have "ns = (bool)" using Bob.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf" using bob_strong_stateSem_singleton
        apply auto
       apply (metis is_singleton_some_elem singletonD)
       by (metis is_singleton_some_elem singletonD)
        
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg (m,\<not>bool)) \<Zcat> s) = \<up>(Eps, TSynMsg (\<not>bool)) \<Zcat> spf\<cdot>(s)"
  by (simp add:step_def) 
qed


lemma bob_strong_snth_fst:
  assumes "spf \<in> Bob.StateSems_stream param bool"
  and     "Fin n < #s"  
  shows "snth n (fst (ssplit\<cdot>(spf\<cdot>(s)))) = snth n (smap (map_tsyn fst)\<cdot>s) \<or> snth n (fst (ssplit\<cdot>(spf\<cdot>(s)))) = Eps"
  using assms
proof(induction n arbitrary: spf bool s)
  case 0
  obtain spf2 where spf2_def:" spf2 \<in> Bob.StateSems_stream param (\<not>bool)"
    by (meson neq_emptyD statesem_notempty)
  then show ?case
    using "0.prems"
    apply(simp)
    apply(cases s;simp)
    apply(case_tac a;simp)
    apply(subst bob_strong_step_simp0[where bool=bool and param = param],simp_all)
      apply (metis(full_types) "0.prems"(1) old.unit.exhaust)
     apply(simp add: ssplit.rep_eq)
    apply(case_tac aa;simp)
    apply(case_tac "b=bool";simp)
    using bob_strong_step_simp1[of spf param bool spf2]
    apply(subst bob_strong_step_simp1[of spf param bool spf2],simp_all)
          apply (metis(full_types) "0.prems"(1) old.unit.exhaust)
     apply(simp add: ssplit.rep_eq)
    apply(subst bob_strong_step_simp2[where bool=bool and param = param],simp_all)
          apply (metis(full_types) "0.prems"(1) old.unit.exhaust)
     apply(simp add: ssplit.rep_eq)
    using "0.prems"(1) by force
next
  case (Suc n)
  obtain spf2 where spf2_def:" spf2 \<in> Bob.StateSems_stream param (\<not>bool)"
    by (meson neq_emptyD statesem_notempty)
  then show ?case 
    using Suc
        apply(simp)
    apply(cases s;simp)
    apply(case_tac a;simp)
    apply(subst bob_strong_step_simp0[where bool=bool and param = param],simp_all)
    apply (metis Suc.prems(1) old.unit.exhaust)
     apply(simp add: ssplit.rep_eq)
    apply (metis Suc.prems(1) bob_strong_step_simp0 snth_scons sprojfst_scons)
    apply(case_tac aa;simp)
    apply(case_tac "b=bool";simp)
    apply(subst bob_strong_step_simp1[where bool=bool and param = param],simp_all)
          apply (metis Suc.prems(1) old.unit.exhaust) defer
      apply(simp add: ssplit.rep_eq)
    using Suc.prems(1)
     apply fastforce
    apply (simp add: ssplit.rep_eq)
      apply(subst bob_strong_step_simp1[where bool=bool and param = param],simp_all)
    using Suc.prems(1) apply force
    by (metis Suc.IH fst_eqD spf2_def
        ssplit.rep_eq)
qed

lemma bool_univ: "(UNIV::bool set) = {True, False}"
  by blast

lemma bobs_chDoms_not_empty: shows "chDom TYPE(unit) \<noteq> {}" and "chDom TYPE(bool) \<noteq> {}"
  apply auto
  unfolding chDom_def Rep_unit_def
  defer
  unfolding bool_univ UNIV_def apply auto
  unfolding cEmpty_def apply auto
  unfolding ctype_empty_iff
  by auto

lemma bob_strong_snth_fst_no_stream:
  assumes "spf2 \<in> Bob.StateSem fout fin param bool"
      and "Fin n < #i"  
  shows "snth n (fst (Stream.ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i))))) =
  snth n (smap (map_tsyn fst)\<cdot>i) \<or>
  snth n (fst (Stream.ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i))))) = \<sim>"
  apply (rule Bob.wsem2streamsem_step_rule[of param bool "(\<lambda>s res. snth n (fst (ssplit\<cdot>(res))) = snth n (smap (map_tsyn fst)\<cdot>s) \<or> snth n (fst (ssplit\<cdot>(res))) = Eps)" i spf2 fout fin])
  apply (simp add: bobs_chDoms_not_empty)
  apply (simp add: bobs_chDoms_not_empty)
  defer using assms apply simp
  proof -
    fix spf y
    assume asm1: "spf \<in> Bob.StateSems_stream param bool"
    show "snth n (fst (Stream.ssplit\<cdot>(spf\<cdot>i))) = snth n (smap (map_tsyn fst)\<cdot>i) \<or>
       snth n (fst (Stream.ssplit\<cdot>(spf\<cdot>i))) = \<sim>"      
      apply (rule bob_strong_snth_fst[of spf param bool n i]) 
      using assms asm1
      by auto
  qed

lemma bob_strong_shd_fst_Sem:assumes"spf \<in> Bob.Sems_stream param"
  shows "shd (fst (ssplit\<cdot>(spf\<cdot>(s)))) = Eps"
proof-
  obtain spf2 initState initOut where 
    trans: "(initState, initOut) \<in> (Bob.initConfigC param)" and  
    spf2_def :" spf2 \<in> (Bob.StateSems_stream param initState)" and 
    step: "spf\<cdot>s = \<up>initOut \<Zcat> spf2\<cdot>s" using Bob.sems_stream_apply_init_step
    using assms(1) by blast
  moreover have "initOut = (Eps,Eps)"
    using trans by (simp add: Bob_init_def)
  ultimately show ?thesis
    by simp
qed

lemma bob_strong_snth_fst_Sem: assumes"spf \<in> Bob.Sems_stream param"
  assumes "Fin n < #s"  
  shows "snth (Suc n) (fst (ssplit\<cdot>(spf\<cdot>(s)))) = snth n (smap (map_tsyn fst)\<cdot>s) \<or> snth (Suc n) (fst (ssplit\<cdot>(spf\<cdot>(s)))) = Eps"
proof-
  obtain spf2 initState initOut where 
    trans: "(initState, initOut) \<in> (Bob.initConfigC param)" and  
    spf2_def :" spf2 \<in> (Bob.StateSems_stream param initState)" and 
    step: "spf\<cdot>s = \<up>initOut \<Zcat> spf2\<cdot>s" using Bob.sems_stream_apply_init_step
    using assms(1) by blast
  moreover have "initOut = (Eps,Eps)"
    using trans by (simp add: Bob_init_def)
  ultimately show ?thesis
    apply (simp)
    apply(rule bob_strong_snth_fst,simp)
    using assms(2) by blast
qed

lemma bob_strong_snth_fst_sem_no_stream:
  assumes "(spf2::unit\<^sup>\<Omega> \<rightarrow> bool\<^sup>\<Omega>) \<in> \<lbrakk>(Bob.nda fout fin param)\<rbrakk>\<^sup>c"
      and "Fin n < #i"  
  shows "snth  (Suc n) (fst (Stream.ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i))))) =
  snth n (smap (map_tsyn fst)\<cdot>i) \<or>
  snth (Suc n) (fst (Stream.ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i))))) = \<sim>"
  apply (rule Bob.sem2streamsem_rule[of param "(\<lambda>s res. snth (Suc n) (fst (ssplit\<cdot>(res))) = snth n (smap (map_tsyn fst)\<cdot>s) \<or> snth  (Suc n) (fst (ssplit\<cdot>(res))) = Eps)" i spf2 fout fin])
  using assms bobs_chDoms_not_empty apply simp_all
  proof -
    fix spf
    show "spf \<in> Bob.Sems_stream () \<Longrightarrow>
       Fin n < #i \<Longrightarrow>
       snth(Suc n) (fst (Stream.ssplit\<cdot>(spf\<cdot>i))) = snth n (smap (map_tsyn fst)\<cdot>i) \<or>
       snth (Suc n) (fst (Stream.ssplit\<cdot>(spf\<cdot>i))) = \<sim>"
      using bob_strong_snth_fst_Sem[where n=n and s=i and param="()" and spf=spf] by simp
  qed


lemma bob_strong_snd:assumes"spf\<in> Bob.StateSems_stream param bool"
  shows "snd (ssplit\<cdot>(spf\<cdot>(s))) = smap (map_tsyn snd)\<cdot>s"
apply(simp add: ssplit.rep_eq )
  using assms
proof(induction s arbitrary: spf bool)
  case adm
  then show ?case 
    apply(rule adm_all)+
    apply(rule adm_imp)
    by simp_all
next
  case bottom
  then show ?case 
    using assms by (simp add: ssplit.rep_eq)
next
  case (step a s)
  obtain spf2 where spf2_def:" spf2 \<in> Bob.StateSems_stream param (\<not>bool)"
    by (meson neq_emptyD statesem_notempty)
  then show ?case 
    using step
    apply(cases a;simp)
    apply(subst bob_strong_step_simp0[where bool=bool and param=param])
    using step.prems apply blast
     apply (simp)
    apply(case_tac aa;simp)
    apply(case_tac "b=bool";simp)
    using step.IH step.prems
    apply force
    using step.prems by force
qed

lemma bob_snd_sem:
  assumes"spf\<in> Bob.Sems_stream param "
  shows "snd (ssplit\<cdot>(spf\<cdot>(s))) = \<up>Eps  \<Zcat> smap (map_tsyn snd)\<cdot>s"
proof-
  obtain spf2 initState initOut where 
    trans: "(initState, initOut) \<in> (Bob.initConfigC param)" and  
    spf2_def :" spf2 \<in> (Bob.StateSems_stream param initState)" and 
    step: "spf\<cdot>s = \<up>initOut \<Zcat> spf2\<cdot>s" using Bob.sems_stream_apply_init_step
    using assms(1) by blast
  moreover have "initOut = (Eps,Eps)"
    using trans by (simp add: Bob_init_def)
  ultimately show ?thesis
    by (simp add: bob_strong_snd)
qed

lemma bob_snd_sem_no_stream:
  assumes "spf\<in> Bob.Sem fout fin param"
  shows "snd (Stream.ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>i)))) = \<up>\<sim> \<Zcat> smap (map_tsyn snd)\<cdot>i"
  apply (rule Bob.sem2streamsem_rule[of param "(\<lambda> s res. snd (ssplit\<cdot>(res)) = \<up>Eps  \<Zcat> smap (map_tsyn snd)\<cdot>s)" i spf fout fin])
  using bobs_chDoms_not_empty assms apply simp_all
proof -
  fix spfa x xa
  assume asm: "spfa \<in> Bob.Sems_stream ()"
  show "snd (ssplit\<cdot>(spfa\<cdot>(i))) = \<up>Eps  \<Zcat> smap (map_tsyn snd)\<cdot>i" 
    using asm 
    by (rule bob_snd_sem[of spfa "()"])
qed



fun Alice_h :: "(nat list \<times> bool) \<Rightarrow> (nat tsyn \<times> bool tsyn) \<Rightarrow> ((nat list \<times> bool) \<times> ((nat \<times> bool) tsyn)) set" where
A1:"Alice_h ([], Ack) (Eps, Eps) = {( ([], Ack), Eps)}" |
A2:"Alice_h ([], Ack) (TSynMsg Data, Eps) = {(([Data], Ack),TSynMsg (Data, Ack))}" |
A3:"Alice_h (Buf # Bufs, Ack) (Eps, Eps) = {((Buf # Bufs, Ack), TSynMsg (Buf, Ack))}" |
A4:"Alice_h ([Buf], Ack) (Eps, TSynMsg a) = (if a = Ack then {(([], \<not>Ack), Eps)} else {undefined})" |
A5:"Alice_h (Buf1 # Buf2 # Bufs, Ack) (Eps, TSynMsg a) = 
 (if a = Ack then {((Buf2 # Bufs, \<not>Ack), TSynMsg (Buf2, \<not>Ack))} else {undefined})" |
A6:"Alice_h (Buf # Bufs, Ack) (TSynMsg Data, Eps) = {((Buf # Bufs @ [Data], Ack),TSynMsg (Buf, Ack))}" |
A7:"Alice_h ([Buf], Ack) (TSynMsg Data, TSynMsg a) = 
 (if a = Ack then {( ([Data], \<not>Ack), TSynMsg (Data, \<not>Ack))} else {undefined})" |
A8:"Alice_h (Buf1 # Buf2 # Bufs, Ack) (TSynMsg Data, TSynMsg a) = 
 (if a = Ack then {((Buf2 # Bufs @ [Data], \<not>Ack), TSynMsg (Buf2, \<not>Ack))} else {undefined})" |
"Alice_h _ _ = {undefined}"


definition Alice_init :: "((nat list \<times> bool) \<times> (nat \<times> bool) tsyn) set" where
"Alice_init = {(([],True),Eps)}"

interpretation Alice: tsStrongGen "(\<lambda> (). Alice_h)" "(\<lambda> (). Alice_init)" fina fouta
  apply standard
  apply simp_all
  oops



lemma Alice_h_not_empty: "Alice_h state msg \<noteq> {}"
  apply (case_tac state; case_tac msg)
  apply (case_tac a; case_tac b; case_tac aa; case_tac ba; auto)
     apply (case_tac ac; case_tac ab; case_tac list; auto)
  apply (case_tac ad; case_tac ab; case_tac list; auto)
   apply (case_tac ac; case_tac ab; case_tac list; auto)
  by (case_tac ad; case_tac ab; case_tac list; auto)

lemma Alice_h_singleton:
  "is_singleton (Alice_h state msg)"
  apply (case_tac state; case_tac msg)
  apply (case_tac a; case_tac b; case_tac aa; case_tac ba; auto)
     apply (case_tac list; case_tac ab; case_tac ac; auto)
    apply (case_tac list; case_tac ab; case_tac ac; auto)
   apply (case_tac list; case_tac ab; case_tac ac; auto)
  by (case_tac list; case_tac ab; case_tac ac; auto)

lemma Alice_stateSem_singleton: "is_singleton (Alice.StateSems_stream param listxbool)"
  apply (rule is_singletonI')
   apply (simp add: statesem_notempty) 
  apply (rule cfun_eqI)
proof -
  fix x y xa
  assume x:"x \<in> Alice.StateSems_stream param listxbool"
  assume y:"y \<in> Alice.StateSems_stream param listxbool"
  show " x\<cdot>xa = y\<cdot>xa"
    using x y
    apply simp
  proof (induction xa arbitrary : x y listxbool)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step a xa)
    obtain nspf_x ns_x out_x where
    step_x_def: "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" and
        nspf_x:  "nspf_x \<in> Alice.StateSems_stream param ns_x"and
       trans_x:  "(ns_x,out_x) \<in> (Alice.transitionC param listxbool a)"
      using Alice.statesems_stream_step
      by (metis old.unit.exhaust step.prems(1))

    obtain nspf_y ns_y out_y where 
    step_y_def: "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" and
        nspf_y:  "nspf_y \<in> Alice.StateSems_stream param ns_y"and
       trans_y:  "(ns_y,out_y) \<in> (Alice.transitionC param listxbool a)"
      using Alice.statesems_stream_step
      by (metis old.unit.exhaust step.prems(2))


  have transition_unique: "out_x = out_y \<and> ns_x = ns_y"
    using trans_x trans_y Alice_h_singleton
    unfolding Alice.transitionC_def is_singleton_def
    by (metis case_unit insert_not_empty
        old.prod.inject
        singleton_iff)

      from step.IH transition_unique  nspf_x nspf_y  step_x_def step_y_def
      show ?case
        apply auto
        by (metis step.IH)
  qed 
qed



lemma alice_step_simp0:assumes"spf\<in> Alice.StateSems_stream param ([], bool)"
  shows "spf\<cdot>(\<up>(Eps,Eps) \<Zcat> s) = \<up>(Eps) \<Zcat> spf\<cdot>(s)"
proof - 

    obtain nspf ns out where 
    step_def: "spf\<cdot>(\<up>(Eps,Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([], bool) (Eps, Eps))"
      using Alice.statesems_stream_step   assms  by blast

    from this have out:"out = ( Eps)" using Alice.transitionC_def Alice_h.simps
      by (metis case_unit insert_not_empty prod.inject singleton_iff)

    from assms nspf trans have ns: "ns = ([], bool)"using Alice.transitionC_def
      by simp  

    from ns nspf assms have eq: "spf = nspf"      
      by (metis (mono_tags, lifting) Abs_unit_cases Alice_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(Eps,Eps) \<Zcat> s) = \<up>(Eps) \<Zcat> spf\<cdot>(s)"
    using eq out by blast
qed

lemma alice_step_simp1:assumes"spf\<in> Alice.StateSems_stream param ([], bool)"
  assumes "spf2 \<in> Alice.StateSems_stream param ([Data], bool)"
  shows "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> s) = \<up>(TSynMsg (Data, bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([], bool) (TSynMsg Data, Eps))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Data, bool))" using Alice.transitionC_def trans
      by (auto simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = ([Data], bool)" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
        apply auto
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> s) = \<up>(TSynMsg (Data, bool)) \<Zcat> spf2\<cdot>(s)"
  by (simp add: step_def) 
qed

lemma alice_step_simp2:assumes"spf\<in> Alice.StateSems_stream param (Buf # Bufs, bool)"
  shows "spf\<cdot>(\<up>(Eps, Eps) \<Zcat> s) = \<up>(TSynMsg (Buf, bool)) \<Zcat> spf\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(Eps, Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ((Buf # Bufs), bool) (Eps, Eps) )"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Buf, bool))" using Alice.transitionC_def trans
      by (auto simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = (Buf # Bufs, bool)" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf" using Alice_stateSem_singleton
        apply auto
       by (metis is_singleton_def singleton_iff)
  
     ultimately show "spf\<cdot>(\<up>(Eps, Eps) \<Zcat> s) = \<up>(TSynMsg (Buf, bool)) \<Zcat> spf\<cdot>(s)"
       by (simp add: step_def)

qed

lemma alice_step_simp3:assumes"spf\<in> Alice.StateSems_stream param ([Buf], bool)"
  assumes "spf2\<in> Alice.StateSems_stream param ([], \<not>bool)"
  assumes "a = bool"
  shows "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([Buf], bool) (Eps, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = Eps" using Alice.transitionC_def assms
      by (auto simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = ([], \<not>bool)"
      by (auto simp add: Alice.transitionC_def)

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)

     ultimately show "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def) 
qed

lemma alice_step_simp4:assumes"spf\<in> Alice.StateSems_stream param (Buf1 # Buf2 # Bufs, bool)"
  assumes "spf\<in> Alice.StateSems_stream param (Buf2 # Bufs, \<not>bool)"
  assumes "a = bool"
  shows "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Buf2, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param (Buf1 # Buf2 # Bufs, bool) (Eps, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Buf2, \<not>bool))" using Alice.transitionC_def assms
      by (auto simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = (Buf2 # Bufs, \<not>bool)"
      by (auto simp add: Alice.transitionC_def)

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis alice_step_simp2 prod.inject shd1
           tsyn.inject)

     ultimately show "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Buf2, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def) 
qed

lemma alice_step_simp5:assumes"spf\<in> Alice.StateSems_stream param (Buf # Bufs, bool)"
  assumes "spf2\<in> Alice.StateSems_stream param (Buf # Bufs @ [Data], bool)"
  shows "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> s) = \<up>(TSynMsg (Buf, bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param (Buf # Bufs, bool) (TSynMsg Data, Eps))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Buf, bool))" using Alice.transitionC_def
      by (simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = (Buf # Bufs @ [Data], bool)" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
        apply auto
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> s) = \<up>(TSynMsg (Buf, bool)) \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def) 
qed

lemma alice_step_simp6:assumes"spf\<in> Alice.StateSems_stream param ([Buf], bool)"
  assumes "spf2\<in> Alice.StateSems_stream param ([Data], \<not>bool)"
  assumes "a = bool"
  shows "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Data, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([Buf], bool) (TSynMsg Data, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Data, \<not>bool))" using Alice.transitionC_def assms
      by (simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = ([Data], \<not>bool)" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Data, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def) 

qed

lemma alice_step_simp7:assumes"spf\<in> Alice.StateSems_stream param (Buf1 # Buf2 # Bufs, bool)"
  assumes "spf2\<in> Alice.StateSems_stream param ((Buf2 # Bufs @ [Data], \<not>bool))"
  assumes "a = bool"
  shows "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Buf2, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param (Buf1 # Buf2 # Bufs, bool) (TSynMsg Data, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Buf2, \<not>bool))" using Alice.transitionC_def assms (3)
      by (simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = ((Buf2 # Bufs @ [Data], \<not>bool))" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Buf2, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def ) 

qed



lift_definition sBoolFilter :: "'a::countable tsyn stream \<rightarrow> bool stream \<rightarrow> 'a tsyn stream" is
"\<lambda> s1.  smap (\<lambda> pair. if snd pair then fst pair else Eps) oo (szip\<cdot>s1)"
  by(intro cont2cont)


definition sbgenInGetter ::"'In sb \<rightarrow> (nat \<times> bool) tsyn stream"where
"sbgenInGetter = undefined"

definition sbgenOutGetter ::"'Out sb \<rightarrow> (nat \<times> bool) tsyn stream"where
"sbgenOutGetter = undefined"

definition sbgenInGetter2 ::"'In sb \<rightarrow> bool tsyn stream"where
"sbgenInGetter2 = undefined"

definition sbgenOutGetter2 ::"'Out sb \<rightarrow> bool tsyn stream"where
"sbgenOutGetter2 = undefined"




definition wholePredicate::"unit \<Rightarrow> 'a::countable tsyn stream \<Rightarrow> 'a tsyn stream \<Rightarrow> bool" where
"wholePredicate u = (\<lambda> s1 s2. (\<exists>bs. sBoolFilter\<cdot>s1\<cdot>bs = s2  \<and> #bs=\<infinity>))"


definition Eve::"unit \<Rightarrow>('In sb \<rightarrow> 'Out sb) set"where
"Eve u = {f | f. \<forall>i. wholePredicate u (sbgenInGetter\<cdot>i) (sbgenOutGetter\<cdot>(f\<cdot>i))}"


definition Eve2::"unit \<Rightarrow>('In sb \<rightarrow> 'Out sb) set"where
"Eve2 u = {f | f. \<forall>i. wholePredicate u (sbgenInGetter2\<cdot>i) (sbgenOutGetter2\<cdot>(f\<cdot>i))}"




definition Eve_stream::"unit \<Rightarrow>((nat \<times> bool) tsyn stream \<rightarrow> (nat \<times> bool) tsyn stream) set"where
"Eve_stream u = {f | f. \<forall>i. wholePredicate u i (f\<cdot>i)}"


lemma "Eve_stream u = {f | f. \<forall>i. \<exists>bs. f\<cdot>i = sBoolFilter\<cdot>i\<cdot>bs \<and> #bs=\<infinity>}"
  apply(simp add: Eve_stream_def wholePredicate_def)
  by metis






definition ABP_comp::"unit \<Rightarrow> ('In sb \<rightarrow> 'Out sb) set"where
"ABP_comp u \<equiv> spsConvert\<cdot>((Alice.Sem undefined undefined u) \<Otimes> (Eve u)\<Otimes> (Bob.Sem undefined undefined u) \<Otimes> (Eve2 u))"




end
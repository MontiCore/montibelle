theory lightcontrol_strongnot_ref
  imports sps_StrongNot_HLR.def_StrongNot_HLR sps_StrongNot_LLR.def_StrongNot_LLR

begin


lemma StrongNotAut_stateSem_singleton: "is_singleton (def_StrongNot_LLR.behavior.StateSems_stream param state)"
  apply (rule is_singletonI')
   apply (simp add: statesem_notempty)
  apply (rule cfun_eqI)
proof -
  fix x y xa
  assume x:"x \<in> behavior.StateSems_stream param state"
  assume y:"y \<in> behavior.StateSems_stream param state"
  show " x\<cdot>xa = y\<cdot>xa"
    using x y
    apply simp
  proof (induction xa arbitrary : x y)

    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step a xa)
    obtain nspf_x ns_x out_x where
    step_x_def: "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" and
        nspf_x:  "nspf_x \<in> behavior.StateSems_stream param ns_x"and
       trans_x:  "(ns_x,out_x) \<in> (behavior.transitionC param state a)"
      using behavior.statesems_stream_step x
      by (metis (full_types) old.unit.exhaust step.prems(1))

    obtain nspf_y ns_y out_y where
    step_y_def: "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" and
        nspf_y:  "nspf_y \<in> behavior.StateSems_stream param ns_y"and
       trans_y:  "(ns_y,out_y) \<in> (behavior.transitionC param state a)"
      using behavior.statesems_stream_step y
      by (metis (full_types) old.unit.exhaust step.prems(2))


    have "is_singleton (behavior.transitionC () state a)"
      unfolding behavior.transitionC_def def_StrongNot_LLR.notTransition_def by auto

    then obtain ns out where
      unique: "behavior.transitionC () state a = {(ns, out)}"
      by (metis is_singletonE old.prod.exhaust)

    with trans_x trans_y have
      "ns_x = ns" "out_x = out" "ns_y = ns" "out_y = out"
      by auto


    from this have outAndns_eq:"out_x = out_y \<and> ns_x = ns_y"
        by simp

      from step_x_def have "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" by simp
      from step_y_def have "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" by simp
      from this outAndns_eq have"y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_y\<cdot>xa" by simp

      from step.IH outAndns_eq nspf_x  nspf_y step_x_def step_y_def
      show ?case
        using surj_pair
      proof -
        have "nspf_y\<cdot>xa = nspf_x\<cdot>xa"
          by (metis (full_types) S.exhaust nspf_x nspf_y old.unit.exhaust step.IH)
        then show ?thesis
          using outAndns_eq step_x_def step_y_def by presburger
      qed
    qed
  qed

lemma StrongNotAut_stateSem_bundle_singleton: "is_singleton (behavior.StateSem () state)"
  apply (rule is_singletonI')
   apply (simp add: statesem_notempty)
  apply (rule cfun_eqI)
proof -
  fix x y xa
  assume x: "x \<in> behavior.StateSem () state"
  assume y: "y \<in> behavior.StateSem () state"
  show "x\<cdot>xa = y\<cdot>xa"
    using x y
  proof (induction xa arbitrary: x y)
    case adm
    then show ?case by simp
  next
    case (least xa)
    then show ?case
      by (simp)
  next
    case (sbeCons sbe xa)
    obtain nspf_x ns_x out_x where
      step_x_def: "x\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                   def_StrongNot_HLR_Output.sbesetter out_x \<Zcat>\<^sup>\<surd> nspf_x\<cdot>xa" and
      nspf_x: "nspf_x \<in> behavior.StateSem () ns_x" and
      trans_x: "(ns_x, out_x) \<in> behavior.transitionC () state
                   (sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter sbe))"
      using behavior.statesem_step_get x
      by (metis def_StrongNot_HLR_Output.sbesetter_def sbeCons.prems(1))

    obtain nspf_y ns_y out_y where
      step_y_def: "y\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                   def_StrongNot_HLR_Output.sbesetter out_y \<Zcat>\<^sup>\<surd> nspf_y\<cdot>xa" and
      nspf_y: "nspf_y \<in> behavior.StateSem () ns_y" and
      trans_y: "(ns_y, out_y) \<in> behavior.transitionC () state
                   (sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter sbe))"
      using behavior.statesem_step_get y
      by (metis def_StrongNot_HLR_Output.sbesetter_def sbeCons.prems(2))

    have "is_singleton (behavior.transitionC () state
          (sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter sbe)))"
      unfolding behavior.transitionC_def notTransition_def by auto

    then obtain ns out where
      unique: "behavior.transitionC () state
                (sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter sbe)) = {(ns, out)}"
      by (metis is_singletonE old.prod.exhaust)

    with trans_x trans_y have
      "ns_x = ns" "out_x = out" "ns_y = ns" "out_y = out"
      by auto

    from this have outAndns_eq: "out_x = out_y \<and> ns_x = ns_y"
      by simp

    from step_x_def have "x\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                          def_StrongNot_HLR_Output.sbesetter out_x \<Zcat>\<^sup>\<surd> nspf_x\<cdot>xa" by simp
    from step_y_def have "y\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                          def_StrongNot_HLR_Output.sbesetter out_y \<Zcat>\<^sup>\<surd> nspf_y\<cdot>xa" by simp
    from this outAndns_eq have "y\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                                def_StrongNot_HLR_Output.sbesetter out_x \<Zcat>\<^sup>\<surd> nspf_y\<cdot>xa" by simp

    from sbeCons.IH outAndns_eq nspf_x nspf_y step_x_def step_y_def
    show ?case
    proof -
      have "nspf_y\<cdot>xa = nspf_x\<cdot>xa"
        using sbeCons.IH nspf_x nspf_y outAndns_eq
        by (metis S.exhaust)
      then show ?thesis
        using outAndns_eq step_x_def step_y_def by simp
    qed
  qed
qed

lemma StrongNotAut_step_simp0[simp]:assumes"spf\<in> behavior.StateSems_stream param state"
  shows "spf\<cdot>(\<up>(TOneMsg False)\<Zcat> s)  = \<up>(TOneMsg True) \<Zcat> spf\<cdot> (s)"
proof -
    obtain nspf ns  out where
    step_def: "spf\<cdot>(\<up>((TOneMsg False)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> behavior.StateSems_stream param ns"and
       trans:  "(ns,out) \<in> (behavior.transitionC param state (TOneMsg False))"
      using behavior.statesems_stream_step assms by blast

    from this have out:"out = (TOneMsg True)" using behavior.transitionC_def notTransition_def by simp

      from assms nspf trans have ns: "ns = state"
      by (metis S.exhaust[of "ns::S"]
          S.exhaust[of "state::S"])

    from ns nspf assms have eq: "spf = nspf"
      by (metis (mono_tags, lifting) Abs_unit_cases StrongNotAut_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(TOneMsg False) \<Zcat> s) = \<up>(TOneMsg True) \<Zcat> spf\<cdot>(s)"
    using eq out by blast

qed

lemma StrongNotAut_step_simp1[simp]:assumes"spf\<in> behavior.StateSems_stream param state"
  assumes "a=True"
  shows "spf\<cdot>(\<up>(TOneMsg a)\<Zcat> s)  = \<up>(TOneMsg False) \<Zcat> spf\<cdot> (s)"
proof -
    obtain nspf ns  out where
    step_def: "spf\<cdot>(\<up>((TOneMsg a)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> behavior.StateSems_stream param ns"and
       trans:  "(ns,out) \<in> (behavior.transitionC param state (TOneMsg a))"
      using behavior.statesems_stream_step assms by blast

    from this assms have out:"out = (TOneMsg False)"  using behavior.transitionC_def notTransition_def by simp

    from assms nspf trans have ns: "ns = state"using behavior.transitionC_def
      by (metis S.exhaust[of "ns::S"]
          S.exhaust[of "state::S"])

    from ns nspf assms have eq: "spf = nspf"
      by (metis (mono_tags, lifting) Abs_unit_cases StrongNotAut_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(TOneMsg a) \<Zcat> s) = \<up>(TOneMsg False) \<Zcat> spf\<cdot>(s)"
    using eq out by blast
qed

lemma HLR_snot_state:
  assumes "spf \<in> behavior.StateSems_stream param state"
  shows " (spf\<cdot>x) = smap (\<lambda>msg. TOneMsg (Not (inverseTOne msg)))\<cdot>x"
  using assms
  apply (induction x arbitrary: spf)
    apply simp_all
  apply (case_tac a; simp)
  by (case_tac xa;simp_all)

lemma HLR_not_init:
  assumes "spf \<in> behavior.Spss_stream param"
  shows " (spf\<cdot>\<epsilon>) =  \<up>(TOneMsg True)"
proof -

  from behavior.sems_stream_apply_init_step[OF assms, of \<epsilon>]
  obtain initState initOut spf2 where
    init: "(initState, initOut) \<in> behavior.initConfigC param" and
    spf2_in: "spf2 \<in> behavior.StateSems_stream param initState" and
    unfold: "spf\<cdot>\<epsilon> = \<up>initOut \<Zcat> spf2\<cdot>\<epsilon>"
    by blast

  have initConfigC_eq: "behavior.initConfigC param = {(S, TOneMsg True)}"
    unfolding behavior.initConfig_def initConfigS_def by simp

  with init have "initState = S" and "initOut = TOneMsg True"
    by auto

  have "spf2\<cdot>\<epsilon> = \<epsilon>"
  proof -
   have strict: "spf2\<cdot>\<bottom> = \<bottom>"
   proof (rule ccontr)
    assume con: "spf2\<cdot>\<bottom> \<noteq> \<bottom>"

    show False
        using con spf2_in by auto
  qed

    thus ?thesis by simp
  qed

  then show ?thesis
    using unfold \<open>initOut = TOneMsg True\<close> by simp
qed

lemma HLR_snot:
  assumes "spf \<in> behavior.Spss_stream param"
  shows " (spf\<cdot>x) =  \<up>(TOneMsg True) \<Zcat> smap (\<lambda>msg. TOneMsg (Not (inverseTOne msg)))\<cdot>x"
proof -
  from behavior.sems_stream_apply_init_step[OF assms, of "x"]
  obtain initState initOut spf0 where
    init: "(initState, initOut) \<in> behavior.initConfigC param" and
    spf0_state: "spf0 \<in> behavior.StateSems_stream param initState" and
    unfold_x: "spf\<cdot>x = \<up>initOut \<Zcat> spf0\<cdot>x"
    by blast
  have initConfigC_eq: "behavior.initConfigC param = {(S, TOneMsg True)}"
    unfolding behavior.initConfig_def initConfigS_def by simp

  with init have "initState = S" and io:"initOut = TOneMsg True"
    by auto

  with spf0_state have spf0_state_S: "spf0 \<in> behavior.StateSems_stream param S"
    by simp

 have eps:"spf0\<cdot>\<epsilon> = \<epsilon>"
  proof -
   have strict: "spf0\<cdot>\<bottom> = \<bottom>"
   proof (rule ccontr)
    assume con: "spf0\<cdot>\<bottom> \<noteq> \<bottom>"

    show False
        using con spf0_state by auto
    qed
    thus ?thesis by simp
  qed

  have does:"spf0\<cdot>x = smap (\<lambda>msg. TOneMsg (Not (inverseTOne msg)))\<cdot>x"
    using HLR_snot_state[OF spf0_state_S] .

  then show "spf\<cdot>x = \<up>(TOneMsg True) \<Zcat> smap (\<lambda>msg::bool tone. TOneMsg (\<not> inverseTOne msg))\<cdot>x"
    by (simp add: unfold_x io does)
qed

lemma HLR_snot_sb:
  assumes "spf \<in> behavior.Sps param"
  shows "(sbeGen.getterSB def_StrongNot_HLR_Output.buildSBE\<cdot>(spf\<cdot>(sbeGen.setterSB def_StrongNot_HLR_Input.buildSBE\<cdot>x))) =
         \<up>(TOneMsg True) \<Zcat> smap (\<lambda>msg. TOneMsg (Not (inverseTOne msg)))\<cdot>x"
  apply (rule behavior.ssem2streamsem_rule[of param "\<lambda>x res. res =
         \<up>(TOneMsg True) \<Zcat> smap (\<lambda>msg. TOneMsg (Not (inverseTOne msg)))\<cdot>x" x spf ])
     apply (simp_all add: HLR_snot)
  using assms by simp

(*refinement*)


lemma sbegen2sbgen_rule_snot:assumes "spf \<in>  behavior.Sps param"
  and "P i ((sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>(i)))))"
and "\<And>x. (getterSB\<cdot>(spf\<cdot>x)) =(sbeGen.getterSB fout\<cdot>(spf\<cdot>x))"
and "\<And>x. spf\<cdot>(setterSB\<cdot>x) = spf\<cdot>(sbeGen.setterSB fin\<cdot>(x))"
shows "P i (getterSB\<cdot>(spf\<cdot>(setterSB\<cdot>i)))"
  by(simp add: assms)

lemma getterAssms_snot_p:
  assumes "spf \<in>  behavior.StateSem param state"
  shows "(def_StrongNot_HLR_Output.sbgetter\<cdot>(spf\<cdot>x) = def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>x))"
  using assms
proof (induction x arbitrary: spf state)
  case adm
  then show ?case by simp
next
  case (least x)
  then show ?case by auto
next
  case (sbeCons sbe x)
note IH = this(1)

  have spf_ss: "spf \<in> behavior.StateSem () state"
  using sbeCons.prems by auto

  obtain spf2 out nextState where
    step: "spf\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> x) =
           def_StrongNot_HLR_Output.sbesetter out \<Zcat>\<^sup>\<surd> spf2\<cdot>x" and
    spf2_in: "spf2 \<in> behavior.StateSem () nextState" and
    trans: "(nextState, out) \<in> behavior.transitionC () state
               (sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter sbe))"
    using spf_ss behavior.statesem_step_get
    by (metis def_StrongNot_HLR_Output.sbesetter_def)

have getter_setter: "sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter sbe) = sbe"
  using def_StrongNot_HLR_Input.sbegetter_def by auto

have "behavior.transitionC () state (sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter sbe)) =
        {(state, map_tone Not sbe)}"
  unfolding behavior.transitionC_def notTransition_def
  using getter_setter
  by simp

  with trans have output_eq: "out = map_tone Not sbe" and nextState_eq: "nextState = state"
    by auto

  have lhs: "def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> x)) =
             def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(def_StrongNot_HLR_Output.sbesetter out \<Zcat>\<^sup>\<surd> spf2\<cdot>x)"
    using step by simp

  also have "... = \<up>(def_StrongNot_HLR_Output.SBE.getter (def_StrongNot_HLR_Output.sbesetter out)) \<Zcat>
                   def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>x)"
    by simp

  also have "... = \<up>out \<Zcat> def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>x)"
    by simp

  finally have lhs_eq: "def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> x)) =
                        \<up>out \<Zcat> def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>x)" .

  have rhs: "def_StrongNot_HLR_Output.sbgetter\<cdot>(spf\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> x)) =
             def_StrongNot_HLR_Output.sbgetter\<cdot>(def_StrongNot_HLR_Output.sbesetter out \<Zcat>\<^sup>\<surd> spf2\<cdot>x)"
    using step by simp

  also have "... = \<up>out \<Zcat> def_StrongNot_HLR_Output.sbgetter\<cdot>(spf2\<cdot>x)"
    by (metis conc_stream_def def_StrongNot_HLR_Output.SB.get_set
              def_StrongNot_HLR_Output.getter_conc2sbconc
              def_StrongNot_HLR_Output.setter_sbe2sb)

  finally have rhs_eq: "def_StrongNot_HLR_Output.sbgetter\<cdot>(spf\<cdot>(def_StrongNot_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> x)) =
                        \<up>out \<Zcat> def_StrongNot_HLR_Output.sbgetter\<cdot>(spf2\<cdot>x)" .

  have "spf2 \<in> behavior.StateSem () state" using spf2_in nextState_eq by simp

  have getter_eq: "def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>x) = def_StrongNot_HLR_Output.sbgetter\<cdot>(spf2\<cdot>x)"
    using IH
    by (metis old.unit.exhaust spf2_in)

  from lhs_eq rhs_eq getter_eq output_eq
  show ?case by simp
qed


lemma getterAssms_snot:
  assumes "spf \<in> behavior.Sps param"
  shows "def_StrongNot_HLR_Output.sbgetter\<cdot>(spf\<cdot>x) = def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>x)"
proof -
  from behavior.ssem_apply_init_step[OF assms, of x]
  obtain initState initOut spf0 where
    init: "(initState, initOut) \<in> behavior.initConfig param" and
    spf0_state: "spf0 \<in> behavior.StateSem param initState" and
    spf_eq: "spf\<cdot>x = initOut \<Zcat>\<^sup>\<Omega> spf0\<cdot>x"
    by blast

  have initConfig_eq: "behavior.initConfig param = {(S, sbe2sb (def_StrongNot_HLR_Output.sbesetter (TOneMsg True)))}"
    unfolding behavior.initConfig_def initConfigS_def
    by (simp add: def_StrongNot_HLR_Output.sbesetter_def)

  with init have "initState = S" and initOut_eq: "initOut = sbe2sb (def_StrongNot_HLR_Output.sbesetter (TOneMsg True))"
    by auto

  with spf0_state have spf0_in: "spf0 \<in> behavior.StateSem () S" by simp

  have lhs: "def_StrongNot_HLR_Output.sbgetter\<cdot>(spf\<cdot>x) =
             def_StrongNot_HLR_Output.sbgetter\<cdot>(initOut \<Zcat>\<^sup>\<Omega> spf0\<cdot>x)"
    using spf_eq by simp

  also have i1: "... = def_StrongNot_HLR_Output.sbgetter\<cdot>(initOut) \<Zcat>
                   def_StrongNot_HLR_Output.sbgetter\<cdot>(spf0\<cdot>x)"
    using def_StrongNot_HLR_Output.getter_conc2sbconc by simp

  also have "... = def_StrongNot_HLR_Output.sbgetter\<cdot>(sbe2sb (def_StrongNot_HLR_Output.sbesetter (TOneMsg True))) \<Zcat>
                   def_StrongNot_HLR_Output.sbgetter\<cdot>(spf0\<cdot>x)"
    using initOut_eq by simp

   have i2: "... = \<up>(sbeGen.getter def_StrongNot_HLR_Output.buildSBE (def_StrongNot_HLR_Output.sbesetter (TOneMsg True))) \<Zcat>
                   def_StrongNot_HLR_Output.sbgetter\<cdot>(spf0\<cdot>x)"
     using def_StrongNot_HLR_Output.sbegetter_def def_StrongNot_HLR_Output.setter_sbe2sb by fastforce


  have rhs: "def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>x) =
             def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(initOut \<Zcat>\<^sup>\<Omega> spf0\<cdot>x)"
    using spf_eq by simp

  have getter_eq: "def_StrongNot_HLR_Output.sbgetter\<cdot>(spf0\<cdot>x) = def_StrongNot_HLR_Output.SBE.getterSB\<cdot>(spf0\<cdot>x)"
    using getterAssms_snot_p[OF spf0_in] by simp

  from lhs rhs getter_eq show ?thesis
    apply (auto simp add: getterAssms_snot_p)
    by (metis i1 i2 def_StrongNot_HLR_Output.SBE.gettersb_unfold def_StrongNot_HLR_Output.sbegetter_def initOut_eq)
qed


lemma setterAssms_snot_p:
  assumes "spf \<in> behavior.StateSem param state"
  shows "spf\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x) = spf\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
  using assms
proof (induction x arbitrary: spf state)
  case adm
  then show ?case by simp
next
  case bottom
  then show ?case by simp
next
  case (step a x)
  note IH = this(1)

  have spf_ss: "spf \<in> behavior.StateSem () state"
    using step.prems by auto

  have lhs: "spf\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>(\<up>a \<Zcat> x)) =
             spf\<cdot>(def_StrongNot_HLR_Input.sbesetter a \<Zcat>\<^sup>\<surd> def_StrongNot_HLR_Input.sbsetter\<cdot>x)"
    by (metis conc_stream_def def_StrongNot_HLR_Input.setter_conc2sbconc
              def_StrongNot_HLR_Input.setter_sbe2sb)

  have rhs: "spf\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>(\<up>a \<Zcat> x)) =
             spf\<cdot>(def_StrongNot_HLR_Input.sbesetter a \<Zcat>\<^sup>\<surd> def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
    using def_StrongNot_HLR_Input.SBE.settersb_unfold by presburger

  obtain spf1 out1 nextState1 where
    step1: "spf\<cdot>(def_StrongNot_HLR_Input.sbesetter a \<Zcat>\<^sup>\<surd> def_StrongNot_HLR_Input.sbsetter\<cdot>x) =
            def_StrongNot_HLR_Output.sbesetter out1 \<Zcat>\<^sup>\<surd> spf1\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x)" and
    spf1_in: "spf1 \<in> behavior.StateSem () nextState1" and
    trans1: "(nextState1, out1) \<in> behavior.transitionC () state
                (sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter a))"
    using spf_ss behavior.statesem_step_get
    by (metis def_StrongNot_HLR_Output.sbesetter_def)

  obtain spf2 out2 nextState2 where
    step2: "spf\<cdot>(def_StrongNot_HLR_Input.sbesetter a \<Zcat>\<^sup>\<surd> def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x) =
            def_StrongNot_HLR_Output.sbesetter out2 \<Zcat>\<^sup>\<surd> spf2\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)" and
    spf2_in: "spf2 \<in> behavior.StateSem () nextState2" and
    trans2: "(nextState2, out2) \<in> behavior.transitionC () state
                (sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter a))"
    using spf_ss behavior.statesem_step_get
    by (metis def_StrongNot_HLR_Output.sbesetter_def)

  have getter_setter: "sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter a) = a"
    using def_StrongNot_HLR_Input.sbegetter_def by auto

  have "behavior.transitionC () state (sbeGen.getter def_StrongNot_HLR_Input.buildSBE (def_StrongNot_HLR_Input.sbesetter a)) =
        {(state, map_tone Not a)}"
    unfolding behavior.transitionC_def notTransition_def
    using getter_setter by simp

  with trans1 trans2 have
    out_eq: "out1 = map_tone Not a" "out2 = map_tone Not a" and
    nextState_eq: "nextState1 = state" "nextState2 = state"
    by auto

  have spf1_in_state: "spf1 \<in> behavior.StateSem () state"
    using spf1_in nextState_eq by simp
  have spf2_in_state: "spf2 \<in> behavior.StateSem () state"
    using spf2_in nextState_eq by simp

  have IH1: "spf1\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x) = spf1\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
    using IH
    by (metis old.unit.exhaust spf1_in)

  have IH2: "spf2\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x) = spf2\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
    using IH
    by (metis old.unit.exhaust spf2_in)

  have spf1_eq_spf2: "spf1 = spf2"
    using StrongNotAut_stateSem_bundle_singleton spf1_in_state spf2_in_state
    by (metis is_singleton_def singletonD)

  have lhs_final: "spf\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>(\<up>a \<Zcat> x)) =
                   def_StrongNot_HLR_Output.sbesetter out1 \<Zcat>\<^sup>\<surd> spf1\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x)"
    using lhs step1 by simp

  also have "... = def_StrongNot_HLR_Output.sbesetter out1 \<Zcat>\<^sup>\<surd> spf1\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
    using IH1 by presburger

  also have "... = def_StrongNot_HLR_Output.sbesetter out2 \<Zcat>\<^sup>\<surd> spf2\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
    using out_eq spf1_eq_spf2 by simp

  finally have lhs_eq: "spf\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>(\<up>a \<Zcat> x)) =
                        def_StrongNot_HLR_Output.sbesetter out2 \<Zcat>\<^sup>\<surd> spf2\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)" .

  have rhs_eq: "spf\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>(\<up>a \<Zcat> x)) =
                def_StrongNot_HLR_Output.sbesetter out2 \<Zcat>\<^sup>\<surd> spf2\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
    using rhs step2 by simp

  from lhs_eq rhs_eq show ?case by simp
qed

lemma setterAssms_snot:
  assumes "spf \<in> behavior.Sps param"
  shows "spf\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x) = spf\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
proof -
  from behavior.ssem_apply_init_step[OF assms, of "def_StrongNot_HLR_Input.sbsetter\<cdot>x"]
  obtain initState initOut spf0 where
    init: "(initState, initOut) \<in> behavior.initConfig param" and
    spf0_state: "spf0 \<in> behavior.StateSem param initState" and
    spf_eq: "spf\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x) = initOut \<Zcat>\<^sup>\<Omega> spf0\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x)"
    by blast

  have initConfig_eq: "behavior.initConfig param = {(S, sbe2sb (def_StrongNot_HLR_Output.sbesetter (TOneMsg True)))}"
    unfolding behavior.initConfig_def initConfigS_def
    by (simp add: def_StrongNot_HLR_Output.sbesetter_def)

  with init have "initState = S" and initOut_eq: "initOut = sbe2sb (def_StrongNot_HLR_Output.sbesetter (TOneMsg True))"
    by auto

  with spf0_state have spf0_in: "spf0 \<in> behavior.StateSem () S" by simp

  have lhs: "spf\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x) =
             initOut \<Zcat>\<^sup>\<Omega> spf0\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x)"
    using spf_eq by simp

  have rhs: "spf\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x) =
             initOut \<Zcat>\<^sup>\<Omega> spf0\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
  proof -
    from behavior.ssem_apply_init_step[OF assms, of "def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x"]
    obtain initState' initOut' spf0' where
      init': "(initState', initOut') \<in> behavior.initConfig param" and
      spf0'_state: "spf0' \<in> behavior.StateSem param initState'" and
      spf_eq': "spf\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x) = initOut' \<Zcat>\<^sup>\<Omega> spf0'\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
      by blast

    with initConfig_eq have "initState' = S" and ieq: "initOut' = initOut"
       apply blast
  using init' initConfig_eq initOut_eq by blast

    with spf0'_state have spf0'_in: "spf0' \<in> behavior.StateSem () S" by simp

    have spf0_eq_spf0': "spf0 = spf0'"
      using StrongNotAut_stateSem_bundle_singleton spf0_in spf0'_in
      by (metis is_singleton_def singletonD)

    have setter_eq: "spf0\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x) = spf0\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
      using setterAssms_snot_p[OF spf0_in] by simp

    then show ?thesis
      using spf_eq' initOut_eq spf0_eq_spf0' ieq
      by fastforce
  qed

  have setter_eq: "spf0\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>x) = spf0\<cdot>(def_StrongNot_HLR_Input.SBE.setterSB\<cdot>x)"
    using setterAssms_snot_p[OF spf0_in] by simp

  from lhs rhs setter_eq show ?thesis by simp
qed

lemma works:
assumes "x \<in> behavior.Sps ()"
shows    "def_StrongNot_HLR.predicate_0 () (i)
        (def_StrongNot_HLR_Output.sbgetter\<cdot>(x\<cdot>(def_StrongNot_HLR_Input.sbsetter\<cdot>(i))))"
  apply (rule sbegen2sbgen_rule_snot [where spf=x and setterSB= "def_StrongNot_HLR_Input.sbsetter" and getterSB="def_StrongNot_HLR_Output.sbgetter" and fin=" def_StrongNot_HLR_Input.buildSBE" and fout= "def_StrongNot_HLR_Output.buildSBE"])
     apply (simp_all add: assms)
    apply (rule behavior.ssem2streamsem_rule)
       apply (simp_all add: assms)
    apply (simp add: def_StrongNot_HLR.predicate_0_def HLR_snot)
  using getterAssms_snot
   apply (simp add: assms def_StrongNot_HLR_Output.sbegettersb_def)
  using  setterAssms_snot
  apply (simp add: assms def_StrongNot_HLR_Input.sbesettersb_def)
done



lemma strongnot_ref: "def_StrongNot_LLR.Sps () \<subseteq> def_StrongNot_HLR.Sps ()"
  unfolding def_StrongNot_HLR.Sps_def def_StrongNot_LLR.Sps_def  def_StrongNot_HLR.wholePredicate_def def_StrongNot_HLR.causality_def def_StrongNot_HLR.assumption_0_def strongpred_def
  apply auto
  defer
   apply (metis behavior.strongpred strongpred_def tlen_len_eq)
  using works
  by (metis def_StrongNot_HLR_Input.SB.set_get)

end
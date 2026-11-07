theory lightcontrol_not_ref
  imports sps_Not_HLR.def_Not_HLR  sps_Not_LLR.def_Not_LLR

begin


lemma notAut_stateSem_singleton: "is_singleton (behavior.StateSemw_stream param state)"
  apply (rule is_singletonI')
   apply (simp add: statesem_notempty)
  apply (rule cfun_eqI)
proof -
  fix x y xa
  assume x:"x \<in> behavior.StateSemw_stream param state"
  assume y:"y \<in> behavior.StateSemw_stream param state"
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
        nspf_x:  "nspf_x \<in> behavior.StateSemw_stream param ns_x"and
       trans_x:  "(ns_x,out_x) \<in> (behavior.transitionC param state a)"
      using behavior.statesemw_stream_step x
      by (metis (full_types) old.unit.exhaust step.prems(1))

    obtain nspf_y ns_y out_y where
    step_y_def: "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" and
        nspf_y:  "nspf_y \<in> behavior.StateSemw_stream param ns_y"and
       trans_y:  "(ns_y,out_y) \<in> (behavior.transitionC param state a)"
      using behavior.statesemw_stream_step y
      by (metis (full_types) old.unit.exhaust step.prems(2))

    have "is_singleton (behavior.transitionC () state a)"
      unfolding behavior.transitionC_def notTransition_def by auto

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

lemma notAut_stateSem_bundle_singleton: "is_singleton (behavior.StateSem () state)"
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
      step_x_def: "x\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                   def_Not_HLR_Output.sbesetter out_x \<Zcat>\<^sup>\<surd> nspf_x\<cdot>xa" and
      nspf_x: "nspf_x \<in> behavior.StateSem () ns_x" and
      trans_x: "(ns_x, out_x) \<in> behavior.transitionC () state
                   (sbeGen.getter def_Not_HLR_Input.buildSBE (def_Not_HLR_Input.sbesetter sbe))"
      using behavior.statesem_step_get x
      by (metis def_Not_HLR_Output.sbesetter_def sbeCons.prems(1))

    obtain nspf_y ns_y out_y where
      step_y_def: "y\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                   def_Not_HLR_Output.sbesetter out_y \<Zcat>\<^sup>\<surd> nspf_y\<cdot>xa" and
      nspf_y: "nspf_y \<in> behavior.StateSem () ns_y" and
      trans_y: "(ns_y, out_y) \<in> behavior.transitionC () state
                   (sbeGen.getter def_Not_HLR_Input.buildSBE (def_Not_HLR_Input.sbesetter sbe))"
      using behavior.statesem_step_get y
      by (metis def_Not_HLR_Output.sbesetter_def sbeCons.prems(2))

    have "is_singleton (behavior.transitionC () state
          (sbeGen.getter def_Not_HLR_Input.buildSBE (def_Not_HLR_Input.sbesetter sbe)))"
      unfolding behavior.transitionC_def notTransition_def by auto

    then obtain ns out where
      unique: "behavior.transitionC () state
                (sbeGen.getter def_Not_HLR_Input.buildSBE (def_Not_HLR_Input.sbesetter sbe)) = {(ns, out)}"
      by (metis is_singletonE old.prod.exhaust)

    with trans_x trans_y have
      "ns_x = ns" "out_x = out" "ns_y = ns" "out_y = out"
      by auto

    from this have outAndns_eq: "out_x = out_y \<and> ns_x = ns_y"
      by simp

    from step_x_def have "x\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                          def_Not_HLR_Output.sbesetter out_x \<Zcat>\<^sup>\<surd> nspf_x\<cdot>xa" by simp
    from step_y_def have "y\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                          def_Not_HLR_Output.sbesetter out_y \<Zcat>\<^sup>\<surd> nspf_y\<cdot>xa" by simp
    from this outAndns_eq have "y\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> xa) =
                                def_Not_HLR_Output.sbesetter out_x \<Zcat>\<^sup>\<surd> nspf_y\<cdot>xa" by simp

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

lemma notAut_step_simp0[simp]:assumes"spf\<in> behavior.StateSemw_stream param state"
  shows "spf\<cdot>(\<up>(TOneMsg False)\<Zcat> s)  = \<up>(TOneMsg True) \<Zcat> spf\<cdot> (s)"
proof -
    obtain nspf ns  out where
    step_def: "spf\<cdot>(\<up>((TOneMsg False)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> behavior.StateSemw_stream param ns"and
       trans:  "(ns,out) \<in> (behavior.transitionC param state (TOneMsg False))"
      using behavior.statesemw_stream_step assms by blast

    from this have out:"out = (TOneMsg True)" using behavior.transitionC_def notTransition_def by simp

      from assms nspf trans have ns: "ns = state"
      by (metis S.exhaust[of "ns::S"]
          S.exhaust[of "state::S"])

    from ns nspf assms have eq: "spf = nspf"
      by (metis (mono_tags, lifting) Abs_unit_cases notAut_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(TOneMsg False) \<Zcat> s) = \<up>(TOneMsg True) \<Zcat> spf\<cdot>(s)"
    using eq out by blast

qed

lemma notAut_step_simp1[simp]:assumes"spf\<in> behavior.StateSemw_stream param state"
  assumes "a=True"
  shows "spf\<cdot>(\<up>(TOneMsg a)\<Zcat> s)  = \<up>(TOneMsg False) \<Zcat> spf\<cdot> (s)"
proof -
    obtain nspf ns  out where
    step_def: "spf\<cdot>(\<up>((TOneMsg a)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> behavior.StateSemw_stream param ns"and
       trans:  "(ns,out) \<in> (behavior.transitionC param state (TOneMsg a))"
      using behavior.statesemw_stream_step assms by blast

    from this assms have out:"out = (TOneMsg False)"  using behavior.transitionC_def notTransition_def by simp

    from assms nspf trans have ns: "ns = state"using behavior.transitionC_def
      by (metis S.exhaust[of "ns::S"]
          S.exhaust[of "state::S"])

    from ns nspf assms have eq: "spf = nspf"
      by (metis (mono_tags, lifting) Abs_unit_cases notAut_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(TOneMsg a) \<Zcat> s) = \<up>(TOneMsg False) \<Zcat> spf\<cdot>(s)"
    using eq out by blast
qed

lemma HLR_not_state:
  assumes "spf \<in> behavior.StateSemw_stream param state"
  shows " (spf\<cdot>x) = smap (\<lambda>msg. TOneMsg (Not (inverseTOne msg)))\<cdot>x"
  using assms
  apply (induction x arbitrary: spf)
    apply simp_all
  apply (case_tac a; simp)
  by (case_tac xa;simp_all)



lemma HLR_not:
  assumes "spf \<in> behavior.Spsw_stream param"
  shows " (spf\<cdot>x) = smap (\<lambda>msg. TOneMsg (Not (inverseTOne msg)))\<cdot>x"
  using assms
  apply (induction x arbitrary: spf)
    apply simp
   apply simp
  apply (metis
    HLR_not_state[of _ "param::unit"_"\<up>_\<Zcat>_"]
    behavior.semw_stream_apply_init_step[of _"param::unit""\<up>_\<Zcat>_"])
  done


lemma HLR_not_sb:
  assumes "spf \<in> behavior.Sps param"
  shows "(sbeGen.getterSB def_Not_HLR_Output.buildSBE\<cdot>(spf\<cdot>(sbeGen.setterSB def_Not_HLR_Input.buildSBE\<cdot>x))) =
         smap (\<lambda>msg. TOneMsg (Not (inverseTOne msg)))\<cdot>x"
  apply (rule behavior.wsem2streamsem_rule[of param "\<lambda>x res. res =
         smap (\<lambda>msg. TOneMsg (Not (inverseTOne msg)))\<cdot>x" x spf ])
     apply (simp_all add: HLR_not)
  using assms by fastforce

lemma sbegen2sbgen_rule_not:assumes "spf \<in>  behavior.Sps param"
  and "P i ((sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>(i)))))"
and "\<And>x. (getterSB\<cdot>(spf\<cdot>x)) =(sbeGen.getterSB fout\<cdot>(spf\<cdot>x))"
and "\<And>x. spf\<cdot>(setterSB\<cdot>x) = spf\<cdot>(sbeGen.setterSB fin\<cdot>(x))"
shows "P i (getterSB\<cdot>(spf\<cdot>(setterSB\<cdot>i)))"
  by(simp add: assms)

lemma getterAssms_not:
  assumes "spf \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"
  shows "(def_Not_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>x)) =(def_Not_HLR_Output.sbgetter\<cdot>(spf\<cdot>x))"
  using assms
proof (induction x arbitrary: spf)
  case adm
  then show ?case by simp
next
case (least sb)
    then show ?case
  proof -
    have "sbIsLeast sb" by fact
    have spf_in: "spf \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c" by fact

    have isb:"spf\<cdot>sb = \<bottom>"
    proof -
      from behavior.ssem_apply_init_step[OF spf_in, of sb]
      obtain initState initOut spf0 where
        init: "(initState, initOut) \<in> behavior.initConfig ()" and
        spf0_state: "spf0 \<in> behavior.StateSem () initState" and
        spf_eq: "spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf0\<cdot>sb"
        by blast

      have "initOut = \<bottom>"
        using init behavior.initConfig_def by auto

      then have "spf\<cdot>sb = \<bottom> \<Zcat>\<^sup>\<Omega> spf0\<cdot>sb"
        using spf_eq by simp

      also have "... = spf0\<cdot>sb"
        by simp

      have "spf0\<cdot>sb = \<bottom>"
        using \<open>sbIsLeast sb\<close> spf0_state by auto

      finally show ?thesis
        by (metis sbconc_bot_l)
    qed

    then show ?thesis
      by simp
  qed
next
case (sbeCons sbe sb)
  note IH = this(1)

  fix spf
  assume spf_in: "spf \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"

  have spf_ss: "spf \<in> behavior.StateSem () S"
  proof -
    have "\<exists>s. spf \<in> (\<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>p) s"
      using behavior.sem_def2 spf_in by fastforce
    then show ?thesis
      by (metis (full_types) S.exhaust)
  qed

  obtain spf2 out nextState where
    step: "spf\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> sb) =
           def_Not_HLR_Output.sbesetter out \<Zcat>\<^sup>\<surd> spf2\<cdot>sb" and
    spf2_in: "spf2 \<in> behavior.StateSem () nextState" and
    trans: "(nextState, out) \<in> behavior.transitionC () S
               (sbeGen.getter def_Not_HLR_Input.buildSBE (def_Not_HLR_Input.sbesetter sbe))"
    using spf_ss behavior.statesem_step_get
    by (metis def_Not_HLR_Output.sbesetter_def)

  have "behavior.transitionC () S (sbeGen.getter def_Not_HLR_Input.buildSBE (def_Not_HLR_Input.sbesetter sbe)) =
        {(S, map_tone Not sbe)}"
    unfolding behavior.transitionC_def notTransition_def
    using def_Not_HLR_Input.sbegetter_def by auto

  with trans have output_eq: "out = map_tone Not sbe" and nextState_eq: "nextState = S"
    by auto

  have lhs: "def_Not_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> sb)) =
             def_Not_HLR_Output.SBE.getterSB\<cdot>(def_Not_HLR_Output.sbesetter out \<Zcat>\<^sup>\<surd> spf2\<cdot>sb)"
    using step by simp

  also have "... = \<up>(def_Not_HLR_Output.SBE.getter (def_Not_HLR_Output.sbesetter out)) \<Zcat>
                   def_Not_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>sb)"
    by simp

  also have "... = \<up>out \<Zcat> def_Not_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>sb)"
    by simp

  finally have lhs_eq: "def_Not_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> sb)) =
                        \<up>out \<Zcat> def_Not_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>sb)" .

  have rhs: "def_Not_HLR_Output.sbgetter\<cdot>(spf\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> sb)) =
             def_Not_HLR_Output.sbgetter\<cdot>(def_Not_HLR_Output.sbesetter out \<Zcat>\<^sup>\<surd> spf2\<cdot>sb)"
    using step by simp

  also have "... = \<up>out \<Zcat> def_Not_HLR_Output.sbgetter\<cdot>(spf2\<cdot>sb)"
    by (metis conc_stream_def def_Not_HLR_Output.SB.get_set def_Not_HLR_Output.getter_conc2sbconc
        def_Not_HLR_Output.setter_sbe2sb)

  finally have rhs_eq: "def_Not_HLR_Output.sbgetter\<cdot>(spf\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> sb)) =
                        \<up>out \<Zcat> def_Not_HLR_Output.sbgetter\<cdot>(spf2\<cdot>sb)" .

  have spf2_in_sem: "spf2 \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"
  proof -
    have f1: "spf \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"
      using spf_in by moura
    have "\<forall>s. spf2 \<in> (\<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>p) s"
      by (metis (full_types) S.exhaust spf2_in)
    then show ?thesis
      using f1 behavior.sem_def2 by fastforce
  qed

  have getter_eq: "def_Not_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>sb) = def_Not_HLR_Output.sbgetter\<cdot>(spf2\<cdot>sb)"
    using IH[OF spf2_in_sem] by blast

  from lhs_eq rhs_eq getter_eq
  show "def_Not_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> sb)) =
        def_Not_HLR_Output.sbgetter\<cdot>(spf\<cdot>(def_Not_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> sb))"
    by simp
qed


lemma setterAssms_not:
  assumes "spf \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"
  shows " spf\<cdot>(def_Not_HLR_Input.sbsetter\<cdot>x) = spf\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>x)"
  using assms
proof (induction x arbitrary: spf)
  case adm
  then show ?case by simp
next
  case bottom
  then show ?case by simp
next
  case (step a x)
  note IH = this(1)
  assume spf_in: "spf \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"

  have spf_ss: "spf \<in> behavior.StateSem () S"
  proof -
    have "\<exists>s. spf \<in> (\<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>p) s"
      using behavior.sem_def2 spf_in by fastforce
    then show ?thesis
      by (metis (full_types) S.exhaust)
  qed

  have lhs: "spf\<cdot>(def_Not_HLR_Input.sbsetter\<cdot>(\<up>a \<Zcat> x)) =
             spf\<cdot>(def_Not_HLR_Input.sbesetter a \<Zcat>\<^sup>\<surd> def_Not_HLR_Input.sbsetter\<cdot>x)"
    by (metis conc_stream_def def_Not_HLR_Input.setter_conc2sbconc def_Not_HLR_Input.setter_sbe2sb)

  have rhs: "spf\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>(\<up>a \<Zcat> x)) =
             spf\<cdot>(def_Not_HLR_Input.sbesetter a \<Zcat>\<^sup>\<surd> def_Not_HLR_Input.SBE.setterSB\<cdot>x)"
    using def_Not_HLR_Input.SBE.settersb_unfold by presburger

  obtain spf1 out1 nextState1 where
    step1: "spf\<cdot>(def_Not_HLR_Input.sbesetter a \<Zcat>\<^sup>\<surd> def_Not_HLR_Input.sbsetter\<cdot>x) =
            def_Not_HLR_Output.sbesetter out1 \<Zcat>\<^sup>\<surd> spf1\<cdot>(def_Not_HLR_Input.sbsetter\<cdot>x)" and
    spf1_in: "spf1 \<in> behavior.StateSem () nextState1" and
    trans1: "(nextState1, out1) \<in> behavior.transitionC () S
                (sbeGen.getter def_Not_HLR_Input.buildSBE (def_Not_HLR_Input.sbesetter a))"
    using spf_ss behavior.statesem_step_get
    by (metis def_Not_HLR_Output.sbesetter_def)

  obtain spf2 out2 nextState2 where
    step2: "spf\<cdot>(def_Not_HLR_Input.sbesetter a \<Zcat>\<^sup>\<surd> def_Not_HLR_Input.SBE.setterSB\<cdot>x) =
            def_Not_HLR_Output.sbesetter out2 \<Zcat>\<^sup>\<surd> spf2\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>x)" and
    spf2_in: "spf2 \<in> behavior.StateSem () nextState2" and
    trans2: "(nextState2, out2) \<in> behavior.transitionC () S
                (sbeGen.getter def_Not_HLR_Input.buildSBE (def_Not_HLR_Input.sbesetter a))"
    using spf_ss behavior.statesem_step_get
    by (metis def_Not_HLR_Output.sbesetter_def)

  have "behavior.transitionC () S (sbeGen.getter def_Not_HLR_Input.buildSBE (def_Not_HLR_Input.sbesetter a)) =
        {(S, map_tone Not a)}"
    unfolding behavior.transitionC_def notTransition_def
    using def_Not_HLR_Input.sbegetter_def by auto

  with trans1 trans2 have
    out_eq: "out1 = map_tone Not a" "out2 = map_tone Not a" and
    nextState_eq: "nextState1 = S" "nextState2 = S"
    by auto

  have spf1_in_sem: "spf1 \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"
  proof -
    have f1: "spf \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"
      using spf_in by moura
    have "\<forall>s. spf1 \<in> (\<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>p) s"
      by (metis (full_types) S.exhaust spf1_in)
    then show ?thesis
      using f1 behavior.sem_def2 by fastforce
  qed

  have spf2_in_sem: "spf2 \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"
  proof -
    have f1: "spf \<in> \<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>c"
      using spf_in by moura
    have "\<forall>s. spf2 \<in> (\<lbrakk>(behavior.nda ())\<rbrakk>\<^sup>p) s"
      by (metis (full_types) S.exhaust spf2_in)
    then show ?thesis
      using f1 behavior.sem_def2 by fastforce
  qed

  have IH1: "spf1\<cdot>(def_Not_HLR_Input.sbsetter\<cdot>x) = spf1\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>x)"
    using IH[OF spf1_in_sem] by blast

  have IH2: "spf2\<cdot>(def_Not_HLR_Input.sbsetter\<cdot>x) = spf2\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>x)"
    using IH[OF spf2_in_sem] by blast

  have spf1_in_S: "spf1 \<in> behavior.StateSem () S" using spf1_in nextState_eq by simp
  have spf2_in_S: "spf2 \<in> behavior.StateSem () S" using spf2_in nextState_eq by simp

  have spf1_eq_spf2: "spf1 = spf2"
    using notAut_stateSem_bundle_singleton spf1_in_S spf2_in_S
    by (metis is_singleton_def singletonD)

  have lhs_final: "spf\<cdot>(def_Not_HLR_Input.sbsetter\<cdot>(\<up>a \<Zcat> x)) =
                   def_Not_HLR_Output.sbesetter out1 \<Zcat>\<^sup>\<surd> spf1\<cdot>(def_Not_HLR_Input.sbsetter\<cdot>x)"
    using lhs step1 by simp

  also have "... = def_Not_HLR_Output.sbesetter out1 \<Zcat>\<^sup>\<surd> spf1\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>x)"
    using IH1 by presburger

  also have "... = def_Not_HLR_Output.sbesetter out2 \<Zcat>\<^sup>\<surd> spf2\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>x)"
    using out_eq spf1_eq_spf2 by simp

  finally have lhs_eq: "spf\<cdot>(def_Not_HLR_Input.sbsetter\<cdot>(\<up>a \<Zcat> x)) =
                        def_Not_HLR_Output.sbesetter out2 \<Zcat>\<^sup>\<surd> spf2\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>x)" .

  have rhs_eq: "spf\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>(\<up>a \<Zcat> x)) =
                def_Not_HLR_Output.sbesetter out2 \<Zcat>\<^sup>\<surd> spf2\<cdot>(def_Not_HLR_Input.SBE.setterSB\<cdot>x)"
    using rhs step2 by simp

  from lhs_eq rhs_eq show ?case by simp
qed

lemma work:
assumes "x \<in> behavior.Sps ()"
shows    "def_Not_HLR.predicate_0 () (i)
        (def_Not_HLR_Output.sbgetter\<cdot>(x\<cdot>(def_Not_HLR_Input.sbsetter\<cdot>(i))))"
  apply (rule sbegen2sbgen_rule_not [where spf=x and setterSB= "def_Not_HLR_Input.sbsetter" and getterSB="def_Not_HLR_Output.sbgetter" and fin=" def_Not_HLR_Input.buildSBE" and fout= "def_Not_HLR_Output.buildSBE"])
     apply (simp_all add: assms)
    apply (rule behavior.wsem2streamsem_rule)
       apply (simp_all add: assms)
    apply (simp add: def_Not_HLR.predicate_0_def HLR_not)
  using getterAssms_not
   apply (simp add: assms def_Not_HLR_Output.sbegettersb_def)
  using  setterAssms_not
  apply (simp add: assms def_Not_HLR_Input.sbesettersb_def)
done



lemma not_ref: "def_Not_LLR.Sps () \<subseteq> def_Not_HLR.Sps ()"
  unfolding def_Not_HLR.Sps_def def_Not_LLR.Sps_def  def_Not_HLR.wholePredicate_def def_Not_HLR.predAndCausality_defs def_Not_HLR.assumption_0_def weakpred_def
  apply auto
   defer
  apply (metis behavior.weakwell tlen_len_eq weak2pred weakpred_def)
  using work
  by (metis HLR_not_sb def_Not_HLR_Input.SB.set_get def_Not_HLR_Input.sbesettersb_def def_Not_HLR_Output.sbegettersb_def
      getterAssms_not setterAssms_not)

end
theory lightcontrol_or_Ref
  imports
    sps_Or_HLR.def_Or_HLR sps_Or_LLR.def_Or_LLR

begin




lemma orAut_stateSem_singleton: "is_singleton (orAut.StateSemw_stream param state)"
  apply (rule is_singletonI')
   apply (simp add: statesem_notempty) 
  apply (rule cfun_eqI)
proof -
  fix x y xa
  assume x:"x \<in> orAut.StateSemw_stream param state"
  assume y:"y \<in> orAut.StateSemw_stream param state"
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
        nspf_x:  "nspf_x \<in> orAut.StateSemw_stream param ns_x"and
       trans_x:  "(ns_x,out_x) \<in> (orAut.transitionC param state a)"
      using orAut.statesemw_stream_step x
      
      by (metis (full_types) old.unit.exhaust step.prems(1)) 

    obtain nspf_y ns_y out_y where 
    step_y_def: "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" and
        nspf_y:  "nspf_y \<in> orAut.StateSemw_stream param ns_y"and
       trans_y:  "(ns_y,out_y) \<in> (orAut.transitionC param state a)"
      using orAut.statesemw_stream_step y      
      by (metis (full_types) old.unit.exhaust step.prems(2))


    from this nspf_x trans_x step_x_def  have outAndns_eq:"out_x = out_y \<and> ns_x = ns_y"
      using orAut.transitionC_def 
      apply  (case_tac a; case_tac b;case_tac aa;simp)
      using orAut.transitionC_def orTransition.simps
      by (smt S.exhaust insert_not_empty
          old.prod.inject
          singleton_iff)


      from step_x_def have "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" by simp
      from step_y_def have "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" by simp
      from this outAndns_eq have"y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_y\<cdot>xa" by simp

      from step.IH outAndns_eq nspf_x  nspf_y step_x_def step_y_def
      show ?case
        using surj_pair orTransition.cases orTransition.simps
      proof -
        have "nspf_y\<cdot>xa = nspf_x\<cdot>xa"
          by (metis (full_types) S.exhaust nspf_x nspf_y old.unit.exhaust step.IH)
        then show ?thesis
          using outAndns_eq step_x_def step_y_def by presburger
      qed
    qed 
  qed

lemma orAut_step_simp0[simp]:assumes"spf\<in> orAut.StateSemw_stream param state"
  shows "spf\<cdot>(\<up>(TOneMsg False, TOneMsg False)\<Zcat> s)  = \<up>(TOneMsg False) \<Zcat> spf\<cdot> (s)"
proof -
    obtain nspf ns  out where 
    step_def: "spf\<cdot>(\<up>((TOneMsg False, TOneMsg False)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> orAut.StateSemw_stream param ns"and 
       trans:  "(ns,out) \<in> (orAut.transitionC param state (TOneMsg False, TOneMsg False))"
      using orAut.statesemw_stream_step assms  by blast

    from this have out:"out = (TOneMsg False)"
      using orAut.transitionC_def orTransition.simps
      by (smt S.exhaust insert_not_empty
          old.prod.inject
          singleton_iff)


    from assms nspf trans have ns: "ns = state"using orAut.transitionC_def 
      by (metis S.exhaust[of "ns::S"]
          S.exhaust[of "state::S"])

    from ns nspf assms have eq: "spf = nspf"
      by (metis (mono_tags, lifting) Abs_unit_cases orAut_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(TOneMsg False, TOneMsg False) \<Zcat> s) = \<up>(TOneMsg False) \<Zcat> spf\<cdot>(s)"
    using eq out by blast

qed

lemma orAut_step_simp1[simp]:assumes"spf\<in> orAut.StateSemw_stream param state"
  assumes "a=True \<or> b= True"
  shows "spf\<cdot>(\<up>(TOneMsg a , TOneMsg b)\<Zcat> s)  = \<up>(TOneMsg True) \<Zcat> spf\<cdot> (s)"
proof -
    obtain nspf ns  out where 
    step_def: "spf\<cdot>(\<up>((TOneMsg a , TOneMsg b)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> orAut.StateSemw_stream param ns"and 
       trans:  "(ns,out) \<in> (orAut.transitionC param state (TOneMsg a , TOneMsg b))"
      using orAut.statesemw_stream_step assms  by blast

    from this assms have out:"out = (TOneMsg True)" 
      using orAut.transitionC_def orTransition.simps
      by (smt S.exhaust insert_not_empty
          old.prod.inject
          singleton_iff)


    from assms nspf trans have ns: "ns = state"using orAut.transitionC_def 
      by (metis S.exhaust[of "ns::S"]
          S.exhaust[of "state::S"])

    from ns nspf assms have eq: "spf = nspf"
      by (metis (mono_tags, lifting) Abs_unit_cases orAut_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(TOneMsg a, TOneMsg b) \<Zcat> s) = \<up>(TOneMsg True) \<Zcat> spf\<cdot>(s)"
    using eq out by blast
qed

lemma HLR_or_state: 
  assumes "spf \<in> orAut.StateSemw_stream param state"
  shows " (spf\<cdot>x) = smap (\<lambda>(a,b). TOneMsg (inverseTOne a \<or> inverseTOne b))\<cdot>x"
  using assms
  apply (induction x arbitrary: spf)
    apply simp_all
  apply (case_tac a; case_tac b;case_tac aa; simp)
  by (case_tac xb; case_tac xa;simp_all)



lemma HLR_or: 
  assumes "spf \<in> orAut.Spsw_stream param"
  shows " (spf\<cdot>x) = smap (\<lambda>(a,b). TOneMsg (inverseTOne a \<or> inverseTOne b))\<cdot>x"
  using assms 
  apply (induction x arbitrary: spf)
    apply simp
   apply simp 
  apply (metis
    HLR_or_state[of _ "param::unit"_"\<up>_\<Zcat>_"]
    orAut.semw_stream_apply_init_step[of _"param::unit""\<up>_\<Zcat>_"])
  done

lemma h: "szip\<cdot>(fst (ssplit\<cdot>s))\<cdot>(snd (ssplit\<cdot>s)) = s"
  by (metis fst_eqD snd_eqD ssplit.rep_eq
      szip_sproj)

lemma HLR_or_sb: 
  assumes "spf \<in> orAut.Sps param"
  shows "(sbeGen.getterSB def_Or_HLR_Output.buildSBE\<cdot>(spf\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>x))) =
         (smap (((\<lambda>((a::bool tone),(b::bool tone)). TOneMsg(inverseTOne a \<or>  inverseTOne b))))\<cdot>(szip\<cdot>(fst(ssplit\<cdot>x))\<cdot>(snd (ssplit\<cdot>x))))"
  apply (rule orAut.wsem2streamsem_rule[of param "\<lambda>x res. res =
         (smap (((\<lambda>((a::bool tone),(b::bool tone)). TOneMsg(inverseTOne a \<or> inverseTOne b))))\<cdot>(szip\<cdot>(fst(ssplit\<cdot>x))\<cdot>(snd (ssplit\<cdot>x))))" x spf ])
     apply (simp_all add: HLR_or h)
  using assms  by fastforce


lemma sbegen2sbgen_rule_or:assumes "spf \<in>  orAut.Sps param"
  and "P i ((sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>(i)))))"
and "\<And>x. (getterSB\<cdot>(spf\<cdot>x)) =(sbeGen.getterSB fout\<cdot>(spf\<cdot>x))"
and "\<And>x. spf\<cdot>(setterSB\<cdot>x) = spf\<cdot>(sbeGen.setterSB fin\<cdot>(x))"
shows "P i (getterSB\<cdot>(spf\<cdot>(setterSB\<cdot>i)))"
  by(simp add: assms)

lemma getterAssms_or_stateSem:
  assumes "spf \<in> (\<lbrakk>(orAut.nda param)\<rbrakk>\<^sup>p) State"
  shows "(def_Or_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>x)) =(def_Or_HLR_Output.sbgetter\<cdot>(spf\<cdot>x))"
  using assms
proof(induction x arbitrary: spf State)
  case adm
  then show ?case by simp
next
  case (least x)
  have "spf\<cdot>x = \<bottom>" using orAut.ndastatesem_bottom_new somechannotempty
    using least by blast
  then show ?case by simp
next
  case (sbeCons sbe x)
  obtain nextState spf2 Out where
    trans: "(nextState, Out) \<in> orAut.transitionC param State sbe" and
    spf2_sem: "spf2 \<in> (\<lbrakk>(orAut.nda param)\<rbrakk>\<^sup>p) nextState" and
    step_eq: "\<And>sb. spf\<cdot>(sbeGen.setter def_Or_HLR_Input.buildSBE sbe \<Zcat>\<^sup>\<surd> sb) = 
                      sbeGen.setter def_Or_HLR_Output.buildSBE Out \<Zcat>\<^sup>\<surd> spf2\<cdot>sb"
    using orAut.statesem_step_complete sbeCons by blast 

  have  "def_Or_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(def_Or_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> x)) =
              def_Or_HLR_Output.SBE.getterSB\<cdot>(sbeGen.setter def_Or_HLR_Output.buildSBE Out \<Zcat>\<^sup>\<surd> spf2\<cdot>x)"
    by (simp add: step_eq def_Or_HLR_Input.sbesetter_def)
  
  also have  "... = \<up>(Out) \<Zcat> 
                   def_Or_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>x)"
    using
      def_Or_HLR_Output.SBE.get_set
      def_Or_HLR_Output.SBE.gettersb_unfold
      def_Or_HLR_Output.sbesetter_def
    by moura
  
  also have  "... = \<up>( Out) \<Zcat> 
                   def_Or_HLR_Output.sbgetter\<cdot>(spf2\<cdot>x)"
    using sbeCons.IH[OF spf2_sem] by simp
  
  also have  h: "def_Or_HLR_Output.sbgetter\<cdot>(spf\<cdot>(def_Or_HLR_Input.sbesetter sbe \<Zcat>\<^sup>\<surd> x)) =
               def_Or_HLR_Output.sbgetter\<cdot>(sbeGen.setter def_Or_HLR_Output.buildSBE Out \<Zcat>\<^sup>\<surd> spf2\<cdot>x)"
    by (simp add: step_eq def_Or_HLR_Input.sbesetter_def)
  
   then have  "... = \<up>( Out) \<Zcat> 
                   def_Or_HLR_Output.sbgetter\<cdot>(spf2\<cdot>x)"
     by (metis conc_stream_def
         def_Or_HLR_Output.SB.get_set
         def_Or_HLR_Output.getter_conc2sbconc
         def_Or_HLR_Output.sbesetter_def
         def_Or_HLR_Output.setter_sbe2sb)
  
   finally show ?case using h
     by argo
qed

lemma getterAssms_or:
  assumes "spf \<in> \<lbrakk>(orAut.nda param)\<rbrakk>\<^sup>c"
  shows "(def_Or_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>x)) =(def_Or_HLR_Output.sbgetter\<cdot>(spf\<cdot>x))"
  using getterAssms_or_stateSem assms
  by (metis (no_types, lifting)
      UN_iff orAut.sem_def2)

lemma setterAssms_or_stateSem:
  assumes "spf \<in> (\<lbrakk>(orAut.nda param)\<rbrakk>\<^sup>p) State"
  shows"spf\<cdot>(def_Or_HLR_Input.sbsetter\<cdot>(a, b)) = 
         spf\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>a\<cdot>b))"
  using assms
proof (induction a arbitrary: spf State b )
  case adm
  then show ?case by simp
next
  case (bottom)
  have "#(def_Or_HLR_Input.sbsetter\<cdot>(\<epsilon>, b)) = 0" by simp

  from this have sbIsLeast_l: "sbIsLeast (def_Or_HLR_Input.sbsetter\<cdot>(\<epsilon>, b))"
    using sbnleast_len
    by blast

    have  left:" spf\<cdot>(def_Or_HLR_Input.sbsetter\<cdot>(\<epsilon>, b)) = \<bottom>" 
    using sbIsLeast_l orAut.ndastatesem_bottom_new
      somechannotempty bottom 
    by blast

    have "#(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>\<epsilon>\<cdot>b)) = 0"
      apply (cases b; auto)
      using def_Or_HLR_Input.sbesettersb_def
      by auto

    from this have sbIsLeast_r: "sbIsLeast (sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>\<epsilon>\<cdot>b))"
    using sbnleast_len
    by blast

    have  right:" spf\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>\<epsilon>\<cdot>b)) = \<bottom>" 
    using sbIsLeast_r orAut.ndastatesem_bottom_new
      somechannotempty bottom
    by blast

  from left right show ?case by simp
  next
  case (step a1 a2 spf State b)
  
  show ?case
  proof (cases b)
    case bottom
  have "#(def_Or_HLR_Input.sbsetter\<cdot>(\<up>a1 \<Zcat> a2, \<epsilon>)) = 0" by simp

  from this have sbIsLeast_l: "sbIsLeast (def_Or_HLR_Input.sbsetter\<cdot>(\<up>a1 \<Zcat> a2, \<epsilon>))"
    using sbnleast_len
    by blast

    have  left:" spf\<cdot>(def_Or_HLR_Input.sbsetter\<cdot>(\<up>a1 \<Zcat> a2, \<epsilon>)) = \<bottom>" 
    using sbIsLeast_l orAut.ndastatesem_bottom_new
      somechannotempty bottom step
    by blast

    have "#(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>(\<up>a1 \<Zcat> a2)\<cdot>\<epsilon>)) = 0"
      apply (cases b; auto)
      using def_Or_HLR_Input.sbesettersb_def
      by auto

    from this have sbIsLeast_r: "sbIsLeast (sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>(\<up>a1 \<Zcat> a2)\<cdot>\<epsilon>))"
    using sbnleast_len
    by blast

    have  right:" spf\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>(\<up>a1 \<Zcat> a2)\<cdot>\<epsilon>)) = \<bottom>" 
    using sbIsLeast_r orAut.ndastatesem_bottom_new
      somechannotempty bottom step
    by blast

  from left right bottom show ?thesis by simp
  next
    case (step b1 b2)
    obtain nextState spf2 Out where
      trans: "(nextState, Out) \<in> orAut.transitionC param State (a1, b1)" and
      spf2_sem: "spf2 \<in> (\<lbrakk>(orAut.nda param)\<rbrakk>\<^sup>p) nextState" and
      step_eq: "\<And>sb. spf\<cdot>(sbeGen.setter def_Or_HLR_Input.buildSBE (a1, b1) \<Zcat>\<^sup>\<surd> sb) = 
                      sbeGen.setter def_Or_HLR_Output.buildSBE Out \<Zcat>\<^sup>\<surd> spf2\<cdot>sb"
      using orAut.statesem_step_complete[OF step.prems, of "(a1, b1)"] by blast
    
    have left: "def_Or_HLR_Input.sbsetter\<cdot>(\<up>a1 \<Zcat> a2, \<up>b1 \<Zcat> b2) =
                sbeGen.setter def_Or_HLR_Input.buildSBE (a1, b1) \<Zcat>\<^sup>\<surd> 
                def_Or_HLR_Input.sbsetter\<cdot>(a2, b2)"
      by (metis
          conc_prod_stream_apply
          def_Or_HLR_Input.sbesetter_def
          def_Or_HLR_Input.setter_conc2sbconc
          def_Or_HLR_Input.setter_sbe2sb)
    
    have szip_split: "szip\<cdot>(\<up>a1 \<Zcat> a2)\<cdot>(\<up>b1 \<Zcat> b2) = \<up>(a1, b1) \<Zcat> szip\<cdot>a2\<cdot>b2"
      by (simp add: szip_scons)
    
    have right: "sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>(\<up>a1 \<Zcat> a2)\<cdot>(\<up>b1 \<Zcat> b2)) =
                 sbeGen.setter def_Or_HLR_Input.buildSBE (a1, b1) \<Zcat>\<^sup>\<surd>
                 sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>a2\<cdot>b2)"
      by (simp add:
          orAut.sbegenfin
          sbeGen.settersb_unfold)
    
    have "spf\<cdot>(def_Or_HLR_Input.sbsetter\<cdot>(\<up>a1 \<Zcat> a2, \<up>b1 \<Zcat> b2)) =
          spf\<cdot>(sbeGen.setter def_Or_HLR_Input.buildSBE (a1, b1) \<Zcat>\<^sup>\<surd> def_Or_HLR_Input.sbsetter\<cdot>(a2, b2))"
      by (simp add: left)
    
    also have "... = sbeGen.setter def_Or_HLR_Output.buildSBE Out \<Zcat>\<^sup>\<surd> 
                     spf2\<cdot>(def_Or_HLR_Input.sbsetter\<cdot>(a2, b2))"
      using step_eq by simp
    
    also have "... = sbeGen.setter def_Or_HLR_Output.buildSBE Out \<Zcat>\<^sup>\<surd> 
                     spf2\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>a2\<cdot>b2))"
      using step.IH[OF spf2_sem, of b2] by simp
    
    also have "... = spf\<cdot>(sbeGen.setter def_Or_HLR_Input.buildSBE (a1, b1) \<Zcat>\<^sup>\<surd>
                         sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>a2\<cdot>b2))"
      using step_eq by simp
    
    also have "... = spf\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>(\<up>a1 \<Zcat> a2)\<cdot>(\<up>b1 \<Zcat> b2)))"
      using right
      by presburger
    
    finally show ?thesis
      using local.step
      by blast 
  qed
qed



lemma setterAssms_or:
  assumes "x \<in> \<lbrakk>(orAut.nda param)\<rbrakk>\<^sup>c"
  shows "x\<cdot>(def_Or_HLR_Input.sbsetter\<cdot>(a, b)) = x\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>a\<cdot>b))"
  using assms setterAssms_or_stateSem
  by (metis (no_types, lifting)
      UN_iff
      orAut.sem_def2)

lemma pred_or: 
  "\<And>x sb. x \<in> \<lbrakk>(orAut.nda ())\<rbrakk>\<^sup>c \<Longrightarrow>
   def_Or_HLR.assumption_0 () (def_Or_HLR_Input.sbgetter\<cdot>sb) (def_Or_HLR_Output.sbgetter\<cdot>(x\<cdot>sb)) \<Longrightarrow>
   def_Or_HLR.predicate_0 () (def_Or_HLR_Input.sbgetter\<cdot>sb) (def_Or_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
proof -
  fix x sb
  assume x_sem: "x \<in> \<lbrakk>(orAut.nda ())\<rbrakk>\<^sup>c"
  assume assm: "def_Or_HLR.assumption_0 () (def_Or_HLR_Input.sbgetter\<cdot>sb) (def_Or_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
  
  define a where "a = fst(def_Or_HLR_Input.sbgetter\<cdot>sb)"
  define b where "b = snd(def_Or_HLR_Input.sbgetter\<cdot>sb)"
  
  have hl1: "def_Or_HLR_Output.SBE.getterSB\<cdot>(x\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>a\<cdot>b))) =
             smap (\<lambda>(p,q). TOneMsg (inverseTOne p \<or> inverseTOne q))\<cdot>(szip\<cdot>(fst(ssplit\<cdot>(szip\<cdot>a\<cdot>b)))\<cdot>(snd(ssplit\<cdot>(szip\<cdot>a\<cdot>b))))"
    using HLR_or_sb[OF x_sem] by simp
  
  then have hl2: "def_Or_HLR_Output.SBE.getterSB\<cdot>(x\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>a\<cdot>b))) =
                  smap (\<lambda>(p,q). TOneMsg (inverseTOne p \<or> inverseTOne q))\<cdot>(szip\<cdot>a\<cdot>b)"
    by (simp add: hl1 h)
  
  have "def_Or_HLR_Output.sbgetter\<cdot>(x\<cdot>sb) = def_Or_HLR_Output.SBE.getterSB\<cdot>(x\<cdot>sb)"
    using getterAssms_or[OF x_sem] by simp


  from this have setter_rel: "x\<cdot>(def_Or_HLR_Input.sbsetter\<cdot>(a, b)) = 
                    x\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>a\<cdot>b))"
    using setterAssms_or [OF x_sem]  a_def b_def
    by blast 
  
  have sb_eq: "sb = def_Or_HLR_Input.sbsetter\<cdot>(def_Or_HLR_Input.sbgetter\<cdot>sb)"
    by (metis def_Or_HLR_Input.SB.set_get)
  
  then have "sb = def_Or_HLR_Input.sbsetter\<cdot>(a, b)"
    by (simp add: a_def b_def)
  
  have "def_Or_HLR_Output.sbgetter\<cdot>(x\<cdot>sb) = 
        def_Or_HLR_Output.SBE.getterSB\<cdot>(x\<cdot>(def_Or_HLR_Input.sbsetter\<cdot>(a, b)))"
    by (simp add: \<open>sb = def_Or_HLR_Input.sbsetter\<cdot>(a, b)\<close> getterAssms_or[OF x_sem])
  
  also have "... = def_Or_HLR_Output.SBE.getterSB\<cdot>(x\<cdot>(sbeGen.setterSB def_Or_HLR_Input.buildSBE\<cdot>(szip\<cdot>a\<cdot>b)))"
    by (simp add: setter_rel)
  
  also have "... = smap (\<lambda>(p,q). TOneMsg (inverseTOne p \<or> inverseTOne q))\<cdot>(szip\<cdot>a\<cdot>b)"
    by (simp add: hl2)
  
  finally have "def_Or_HLR_Output.sbgetter\<cdot>(x\<cdot>sb) = 
                smap (\<lambda>(p,q). TOneMsg (inverseTOne p \<or> inverseTOne q))\<cdot>(szip\<cdot>a\<cdot>b)"
    by simp
  
  then show "def_Or_HLR.predicate_0 () (def_Or_HLR_Input.sbgetter\<cdot>sb) (def_Or_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
    unfolding def_Or_HLR.predicate_0_def
    by (simp add: a_def b_def
        case_prod_beta)
qed

lemma causality_or: 
"\<And>(x::def_Or_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Or_HLR_Output.channels\<^sup>\<Omega>) sb::def_Or_HLR_Input.channels\<^sup>\<Omega>.
       x \<in> \<lbrakk>(orAut.nda ())\<rbrakk>\<^sup>c \<Longrightarrow> def_Or_HLR.causality (def_Or_HLR_Input.sbgetter\<cdot>sb) (def_Or_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
proof- 
  fix  x sb
  assume sem: "x \<in> \<lbrakk>(orAut.nda ())\<rbrakk>\<^sup>c"

  have weakpred_rel: "weakpred sb (x\<cdot>sb)"
    by (rule orAut.weakpred[OF sem])


  from this show " def_Or_HLR.causality (def_Or_HLR_Input.sbgetter\<cdot>sb) (def_Or_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
    unfolding def_Or_HLR.causality_def weakpred_def
    using def_Or_HLR_Input.SB.getter_tlen def_Or_HLR_Output.SB.getter_tlen somechannotempty weakpred_rel
    by fastforce  
qed

lemma ref_or:"def_Or_LLR.Sps () \<subseteq> def_Or_HLR.Sps ()"
  unfolding def_Or_LLR.Sps_def def_Or_HLR.Sps_def  def_Or_HLR.wholePredicate_def
  apply auto
  by (simp_all add: causality_or pred_or)



end 




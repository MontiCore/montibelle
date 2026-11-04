theory hwl_ref_Bob_LLR_rough_Bob_HLR
  imports
    (* Gen *) sps_Bob_HLR.def_Bob_HLR sps_Bob_LLR.def_Bob_LLR
    (* Hwl  *)

begin


lemma bob_stream_sntimes:assumes"spf\<in> def_Bob_LLR.behavior.StateSems_stream param s"
  shows "snth n (spf\<cdot>\<up>\<sim>\<^sup>\<infinity>) = (\<sim>, \<sim>)"
  using assms
proof(induction n arbitrary: spf s)
  case 0
  then obtain nspf ns out where step_def:"spf\<cdot>(\<up>\<sim> \<Zcat> (\<up>\<sim>\<^sup>\<infinity>)) = \<up>out \<Zcat> nspf\<cdot>\<up>\<sim>\<^sup>\<infinity> \<and> nspf\<in> def_Bob_LLR.behavior.StateSems_stream param ns \<and> (ns,out) \<in> (def_Bob_LLR.behavior.transitionC param s Eps)"
    using def_Bob_LLR.behavior.statesems_stream_step
    by blast
  then show ?case
    apply (subst sinftimes_unfold)apply simp
    by(simp add: autTransition.rep_eq def_Bob_LLR.behavior.ndas_stream.rep_eq def_Bob_LLR.behavior.transitionC_def)
next
  case (Suc n)
  then obtain nspf ns out where step_def:"spf\<cdot>(\<up>\<sim> \<Zcat> (\<up>\<sim>\<^sup>\<infinity>)) = \<up>out \<Zcat> nspf\<cdot>\<up>\<sim>\<^sup>\<infinity> \<and> nspf\<in> def_Bob_LLR.behavior.StateSems_stream param ns \<and> (ns,out) \<in> (def_Bob_LLR.behavior.transitionC param s Eps)"
    using def_Bob_LLR.behavior.statesems_stream_step
    by blast
  then show ?case
    apply (subst sinftimes_unfold)apply simp
    apply(simp add: autTransition.rep_eq def_Bob_LLR.behavior.ndas_stream.rep_eq def_Bob_LLR.behavior.transitionC_def)
    apply(rule Suc.IH)
    using step_def by blast
qed



lemma bob_strong_stateSem_singleton: "is_singleton (def_Bob_LLR.behavior.StateSems_stream param (d_state,b_state))"
  apply (rule is_singletonI')
   apply (simp add: statesem_notempty) 
  apply (rule cfun_eqI)
proof -
  fix x y xa
  assume x:"x \<in> def_Bob_LLR.behavior.StateSems_stream param (d_state,b_state)"
  assume y:"y \<in> def_Bob_LLR.behavior.StateSems_stream param (d_state,b_state)"
  show " x\<cdot>xa = y\<cdot>xa"
    using x y
    apply simp
  proof (induction xa arbitrary : x y d_state b_state)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step a xa)
    obtain nspf_x ns_x out_x where
    step_x_def: "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" and
        nspf_x:  "nspf_x \<in> def_Bob_LLR.behavior.StateSems_stream param ns_x"and
       trans_x:  "(ns_x,out_x) \<in> (def_Bob_LLR.behavior.transitionC param (d_state,b_state) a)"
      using def_Bob_LLR.behavior.statesems_stream_step x
      by (metis (full_types) old.unit.exhaust step.prems(1))

    obtain nspf_y ns_y out_y where 
    step_y_def: "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" and
        nspf_y:  "nspf_y \<in> def_Bob_LLR.behavior.StateSems_stream param ns_y"and
       trans_y:  "(ns_y,out_y) \<in> (def_Bob_LLR.behavior.transitionC param (d_state,b_state) a)"
      using def_Bob_LLR.behavior.statesems_stream_step y
      by (metis (full_types) old.unit.exhaust step.prems(2))


    from this nspf_x trans_x step_x_def  have outAndns_eq:"out_x = out_y \<and> ns_x = ns_y"
      using def_Bob_LLR.behavior.transitionC_def
      apply (cases a)
      apply (metis R1 case_unit
          insert_not_empty prod.inject singleton_iff)
      apply (case_tac aa)
      using Data_Bool_Tuple_get_fst.simps  Data_Bool_Tuple_get_snd.simps
      by (metis
          R2[of "d_state::nat tsyn" "b_state::bool" "Data_Bool_TupleConstr _ _"]
          Pair_inject[of "ns_x::nat tsyn \<times> bool" "out_x::bool tsyn \<times> nat tsyn"
                      "ns_y::nat tsyn \<times> bool" "out_y::bool tsyn \<times> nat tsyn"]
          insert_not_empty[of "((TSynMsg (Data_Bool_Tuple_get_fst (Data_Bool_TupleConstr _ _)),
                            Data_Bool_Tuple_get_snd (Data_Bool_TupleConstr _ _)),
                             TSynMsg (Data_Bool_Tuple_get_snd (Data_Bool_TupleConstr _ _)), \<sim>)" "{}"]
          insert_not_empty[of "((TSynMsg (Data_Bool_Tuple_get_fst (Data_Bool_TupleConstr _ _)),
                          Data_Bool_Tuple_get_snd (Data_Bool_TupleConstr _ _)), TSynMsg(Data_Bool_Tuple_get_snd
                (Data_Bool_TupleConstr _ _)), TSynMsg (Data_Bool_Tuple_get_fst (Data_Bool_TupleConstr _ _)))" "{}"]
          old.unit.case[of Receiver_LLR_h_v2] old.unit.exhaust[of "param::unit"]
          singleton_iff[of "(ns_x::nat tsyn \<times> bool, out_x::bool tsyn \<times> nat tsyn)" "((TSynMsg _, Data_Bool_Tuple_get_snd _),
                        TSynMsg (Data_Bool_Tuple_get_snd _), \<sim>)"]
          singleton_iff[of "(ns_y::nat tsyn \<times> bool, out_y::bool tsyn \<times> nat tsyn)""((TSynMsg _, Data_Bool_Tuple_get_snd _),
                            TSynMsg (Data_Bool_Tuple_get_snd _), \<sim>)"]
          singleton_iff[of "(ns_x::nat tsyn \<times> bool, out_x::bool tsyn \<times> nat tsyn)""((TSynMsg _, Data_Bool_Tuple_get_snd _),
                            TSynMsg (Data_Bool_Tuple_get_snd _), TSynMsg _)"]
          singleton_iff[of "(ns_y::nat tsyn \<times> bool, out_y::bool tsyn \<times> nat tsyn)" "((TSynMsg _, Data_Bool_Tuple_get_snd _),
                        TSynMsg (Data_Bool_Tuple_get_snd _), TSynMsg _)"])



      from step_x_def have "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" by simp
      from step_y_def have "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" by simp
      from this outAndns_eq have"y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_y\<cdot>xa" by simp

      from step.IH outAndns_eq nspf_x  nspf_y step_x_def step_y_def
      show ?case
        apply simp
        by (metis step.IH surj_pair)
  qed 
qed



lemma bob_strong_step_simp0[simp]:assumes"spf\<in> def_Bob_LLR.behavior.StateSems_stream param (d_state ,b_state)"
  shows "spf\<cdot>(\<up>(Eps) \<Zcat> s) = \<up>(Eps, Eps) \<Zcat> spf\<cdot>(s)"
proof -
    obtain nspf ns  out where 
    step_def: "spf\<cdot>(\<up>(Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> def_Bob_LLR.behavior.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (def_Bob_LLR.behavior.transitionC param (d_state ,b_state) (Eps))"
      using def_Bob_LLR.behavior.statesems_stream_step assms by blast

    from this have out:"out = (Eps, Eps)" using def_Bob_LLR.behavior.transitionC_def R1
      by auto

    from assms nspf trans have ns: "ns = (d_state ,b_state)"using def_Bob_LLR.behavior.transitionC_def
      by simp  

    from ns nspf assms have eq: "spf = nspf"
      by (metis (mono_tags, lifting) Abs_unit_cases bob_strong_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(Eps) \<Zcat> s) = \<up>(Eps, Eps) \<Zcat> spf\<cdot>(s)"
    using eq out by blast

qed


lemma bob_strong_step_simp1[simp]:assumes"spf\<in> def_Bob_LLR.behavior.StateSems_stream param (d_state ,b_state)"
  assumes "(d_state ,b_state) = (TSynMsg (Data_Bool_Tuple_get_fst input), Data_Bool_Tuple_get_snd input)"
  assumes "spf2 \<in> def_Bob_LLR.behavior.StateSems_stream param (TSynMsg (Data_Bool_Tuple_get_fst input), Data_Bool_Tuple_get_snd input)"
  shows "spf\<cdot>(\<up>(TSynMsg ( input)) \<Zcat> s) = \<up>((TSynMsg (Data_Bool_Tuple_get_snd input), Eps)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg ( input)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> def_Bob_LLR.behavior.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (def_Bob_LLR.behavior.transitionC param (d_state ,b_state) (TSynMsg(input)))"
      using def_Bob_LLR.behavior.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Data_Bool_Tuple_get_snd input), Eps)" using def_Bob_LLR.behavior.transitionC_def R2 
      by (cases input; auto simp add: assms (2))



    moreover from assms nspf trans have "ns = (TSynMsg (Data_Bool_Tuple_get_fst input), Data_Bool_Tuple_get_snd input)" using def_Bob_LLR.behavior.transitionC_def
      by auto

     moreover from this  assms nspf have "nspf = spf2" using bob_strong_stateSem_singleton
        apply auto
        by (metis is_singleton_def singleton_iff)+
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg ( input)) \<Zcat> s) = \<up>((TSynMsg (Data_Bool_Tuple_get_snd input), Eps)) \<Zcat> spf2\<cdot>(s)"
  by (simp add: step_def) 
qed


lemma bob_strong_step_simp2[simp]:assumes"spf\<in> def_Bob_LLR.behavior.StateSems_stream param (d_state ,b_state)"
  assumes "(d_state ,b_state) \<noteq> (TSynMsg (Data_Bool_Tuple_get_fst input), Data_Bool_Tuple_get_snd input)"
  assumes "spf2 \<in> def_Bob_LLR.behavior.StateSems_stream param (TSynMsg (Data_Bool_Tuple_get_fst input), Data_Bool_Tuple_get_snd input)"
  shows "spf\<cdot>(\<up>(TSynMsg(input)) \<Zcat> s) = \<up>((TSynMsg (Data_Bool_Tuple_get_snd input), TSynMsg (Data_Bool_Tuple_get_fst input))) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg ( input)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> def_Bob_LLR.behavior.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (def_Bob_LLR.behavior.transitionC param (d_state ,b_state) (TSynMsg(input)))"
      using def_Bob_LLR.behavior.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Data_Bool_Tuple_get_snd input), TSynMsg (Data_Bool_Tuple_get_fst input))" using def_Bob_LLR.behavior.transitionC_def R2
      using assms(2) by auto 



    moreover from assms nspf trans have "ns = (TSynMsg (Data_Bool_Tuple_get_fst input), Data_Bool_Tuple_get_snd input)" using def_Bob_LLR.behavior.transitionC_def
      by auto

     moreover from this  assms nspf have "nspf = spf2" using bob_strong_stateSem_singleton
        apply auto
        by (metis is_singleton_def singleton_iff)+
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg ( input)) \<Zcat> s) = \<up>((TSynMsg (Data_Bool_Tuple_get_snd input), TSynMsg (Data_Bool_Tuple_get_fst input))) \<Zcat> spf2\<cdot>(s)"
  by (simp add: step_def) 
qed

lemma Bob_forwards_ack_stateSem: assumes "spf \<in> def_Bob_LLR.behavior.StateSems_stream param state"
  shows"fst (ssplit\<cdot>(spf\<cdot>s) ) = (smap(map_tsyn Data_Bool_Tuple_get_snd)\<cdot>s)"
  using assms
proof (induction s arbitrary: spf state)
  case adm
  then show ?case
    by auto
next
  case bottom
  have "spf\<cdot>\<epsilon> = \<epsilon>" using assms
    using bottom
    by auto 
  then show ?case
    by (metis
        below_bottom_iff
        fst_strict
        ssplit_szip_below
        strictI
        strict_smap)
next
  case (step a s)
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>((a)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> def_Bob_LLR.behavior.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (def_Bob_LLR.behavior.transitionC param state ((a)))"
      using def_Bob_LLR.behavior.statesems_stream_step step.prems
      by blast 
    from step show ?case 
    apply (case_tac a) 
    apply (simp_all add: tsynprojsnd_sconc_Eps)
    apply (cases state)
    apply (case_tac aa)
    apply (case_tac "aaa = TSynMsg ab")
    using step.prems
       apply force +
    apply (cases state)
    apply (case_tac "(aaa, b) = ((TSynMsg (Data_Bool_Tuple_get_fst aa)), Data_Bool_Tuple_get_snd aa)")
    apply (metis (no_types, lifting) ext
        bob_strong_step_simp1 conc_prod_fst
        conc_stream_def ssplit_step step.prems)
    by (smt
       R2 def_Bob_LLR.behavior.transitionC_def
        step_def nspf trans fst_conv
        insert_not_empty old.unit.case
        old.unit.exhaust singleton_iff
        snd_conv sprojfst_scons
        ssplit.rep_eq step.IH)
qed


lemma Bob_forwards_ack: 
  assumes "spf\<in> def_Bob_LLR.behavior.Sems_stream param "
  shows "(sprojfst\<cdot>(spf\<cdot>s))= \<up>Eps \<Zcat> (smap(map_tsyn Data_Bool_Tuple_get_snd)\<cdot>s)"
proof -

      obtain nspf initState initOut where
    step_def: "spf\<cdot>(s) = \<up>initOut \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> def_Bob_LLR.behavior.StateSems_stream param initState"and 
       trans:  "(initState,initOut) \<in> def_Bob_LLR.behavior.initConfigC param"
      using def_Bob_LLR.behavior.sems_stream_apply_init_step assms
      by blast

    have "initOut = (Eps, Eps)"
      by (metis Pair_inject
          Receiver_LLR_h_init_def
          case_unit insert_not_empty
          singletonD trans)

  from this show ?thesis using Bob_forwards_ack_stateSem assms
    by (metis (no_types, lifting) Stream.ssplit.rep_eq
        conc_prod_fst conc_stream_def fst_conv nspf
        ssplit_step step_def)
qed

lemma bob_snd_sem:
  assumes"spf\<in> def_Bob_LLR.behavior.Sems_stream param "
  shows "fst (ssplit\<cdot>(spf\<cdot>(s))) = \<up>Eps \<Zcat> smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>s"
  using Bob_forwards_ack 
  by (metis assms fst_conv
      ssplit.rep_eq)

lemma bob_snd_sem_no_stream:
  assumes "spf\<in> def_Bob_LLR.behavior.Sem param "
  shows "fst (Stream.ssplit\<cdot>(sbeGen.getterSB def_Bob_HLR_Output.buildSBE\<cdot>(spf\<cdot>(sbeGen.setterSB def_Bob_HLR_Input.buildSBE\<cdot>i)))) = \<up>Eps \<Zcat> smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>i"
  apply (rule def_Bob_LLR.behavior.ssem2streamsem_rule[of param "(\<lambda> s res. fst (ssplit\<cdot>(res)) = \<up>Eps \<Zcat> smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>s)" i spf])
  using assms apply simp_all
  using bob_snd_sem by blast

lemma tsynProjSnd_equals_smap_snd:
  "tsynProjSnd\<cdot>(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>s) 
   = smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>s"
proof -
  have "tsynSnd (map_tsyn Data_Bool_Tuple2tuple x) = map_tsyn Data_Bool_Tuple_get_snd x" for x
  proof (cases x)
    case Eps
    then show ?thesis
      by simp 
  next
    case (Msg a)
    then show ?thesis
      by (cases a; simp)
    qed

  from this show ?thesis
    unfolding tsynProjSnd_def
    by (metis (no_types, lifting) 
        rek2smap smap_split smap_sup smapsmap2smap
        strict_smap) 
qed

lemma tsynProjFst_smap_fst:
  "tsynProjFst\<cdot>(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>s) 
   = smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>s"
proof -
  have composition: "tsynFst (map_tsyn Data_Bool_Tuple2tuple x) = map_tsyn Data_Bool_Tuple_get_fst x" for x
  proof (cases x)
    case Eps
    then show ?thesis
      by simp 
  next
    case (Msg a)
    then show ?thesis
      by (cases a; simp)
  qed

  show ?thesis
    unfolding tsynProjFst_def
    by (metis (no_types, lifting) composition
        rek2smap smap_split smap_sup smapsmap2smap
        strict_smap) 
qed

lemma sbegen2sbgen_rule:assumes "spf \<in>  def_Bob_LLR.behavior.Sem param"
  and "P i (ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>(i)))))"
and "\<And>x. (getterSB\<cdot>(spf\<cdot>x)) = ssplit\<cdot>(sbeGen.getterSB fout\<cdot>(spf\<cdot>x))"
and "\<And>x. spf\<cdot>(setterSB\<cdot>x) = spf\<cdot>(sbeGen.setterSB fin\<cdot>x)"
shows "P i (getterSB\<cdot>(spf\<cdot>(setterSB\<cdot>i)))"
  by(simp add: assms)
(*
lemma bob_weak_eps_stream:assumes"spf\<in> def_Bob_LLR.behavior.Sems_stream param"
  shows "spf\<cdot>(\<up>Eps\<^sup>\<infinity>) = (\<up>(Eps,Eps)\<^sup>\<infinity>)"
  apply(rule snths_eq)
  using assms apply auto
  by (metis def_Bob_LLR.behavior.sems_stream_apply_init_step
      bob_stream_sntimes) 

lemma sbegen_holds:
  assumes "spf \<in>  def_Bob_LLR.behavior.Sem param"
  shows "(ssplit\<cdot>(sbeGen.getterSB def_Bob_HLR_Output.buildSBE\<cdot>(spf\<cdot>(sbeGen.setterSB def_Bob_HLR_Input.buildSBE\<cdot>(\<up>Eps\<^sup>\<infinity>))))) = (\<up>Eps\<^sup>\<infinity>, \<up>Eps\<^sup>\<infinity>)"
  apply(rule def_Bob_LLR.behavior.ssem2streamsem_rule[where param = param];simp_all)
  apply(subst bob_weak_eps_stream,simp_all add: ssplit.rep_eq)
  apply (metis slen_sup_sinftimes sprojfst_szipl1 sprojsnd_szipl1 szip2sinftimes)
  using assms by simp


lemma sbgen_holds: assumes "spf \<in>  def_Bob_LLR.behavior.Sem param"
and "\<And>x. (def_Bob_HLR_Output.SB.getter\<cdot>(spf\<cdot>x)) = ssplit\<cdot>(sbeGen.getterSB def_Bob_HLR_Output.buildSBE\<cdot>(spf\<cdot>x))"
and "\<And>x. spf\<cdot>(def_Bob_HLR_Input.SB.setter\<cdot>x) = spf\<cdot>(sbeGen.setterSB def_Bob_HLR_Input.buildSBE\<cdot>x)"
shows "(def_Bob_HLR_Output.SB.getter\<cdot>(spf\<cdot>(def_Bob_HLR_Input.SB.setter\<cdot>(\<up>Eps\<^sup>\<infinity>)))) = (\<up>Eps\<^sup>\<infinity>, \<up>Eps\<^sup>\<infinity>)"
  apply(rule sbegen2sbgen_rule)
  using assms sbegen_holds by simp_all                

*)
lemma sbestter_sbsetter_eq:"\<forall>s. def_Bob_HLR_Input.sbesettersb\<cdot>s = def_Bob_HLR_Input.sbsetter\<cdot>s"
  apply (rule )
  apply (induct_tac s) apply simp_all
  by (metis (no_types) conc_stream_def
        def_Bob_HLR_Input.setter_conc2sbconc
        def_Bob_HLR_Input.setter_sbe2sb)



lemma sbgetter_conc:
  "def_Bob_HLR_Output.sbgetter\<cdot>(a \<Zcat>\<^sup>\<Omega> b) = 
   (fst (def_Bob_HLR_Output.sbgetter\<cdot>a) \<Zcat> fst (def_Bob_HLR_Output.sbgetter\<cdot>b),
    snd (def_Bob_HLR_Output.sbgetter\<cdot>a) \<Zcat> snd (def_Bob_HLR_Output.sbgetter\<cdot>b))"
    by (metis (no_types) conc_prod_stream_apply
        def_Bob_HLR_Output.getter_conc2sbconc prod.collapse)

(*core*)
lemma ssplit_conc:
  "Stream.ssplit\<cdot>(a \<Zcat> b) = 
   (fst (Stream.ssplit\<cdot>a) \<Zcat> fst (Stream.ssplit\<cdot>b),
    snd (Stream.ssplit\<cdot>a) \<Zcat> snd (Stream.ssplit\<cdot>b))"
  unfolding  ssplit_def sprojfst_def sprojsnd_def
  apply simp
  by (meson smap_split)

lemma sbgetter_ssplit_single:
  "def_Bob_HLR_Output.sbgetter\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>a)) = 
   Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>a)))"
        by (metis (no_types, opaque_lifting)
            def_Bob_LLR.behavior.helping
            def_Bob_HLR_Output.SB.get_set
            def_Bob_HLR_Output.SBE.getset_eq
            def_Bob_HLR_Output.sbesetter_def
            def_Bob_HLR_Output.sbesettersb_def
            def_Bob_HLR_Output.setter_sbe2sb
            old.prod.exhaust
            somechannotempty sprojfst_sup
            sprojsnd_sup
            ssplit.rep_eq)

lemma bob_sb2sbeget_stateSem:
  assumes "spf \<in> (\<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>p) State"
  shows "def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb) = Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>sb))"
  using assms
proof(induction sb arbitrary: spf State rule: sb_ind2)
  case adm
  then show ?case by simp
next
  case (least sb)
  have input_dom_nonempty: "chDom TYPE(def_Bob_HLR_Input.channels) \<noteq> {}" by simp

  from least have "sbIsLeast sb"
    using sbnleast_len by blast 

  from assms this have spf_sb_bot: "spf\<cdot>sb = \<bottom>"
    apply (subst def_Bob_LLR.behavior.ndastatesem_bottom_new [of sb spf "()" State])
    by (simp_all add: local.least)

  then show ?case unfolding ssplit_def by simp
next
  case (sbeCons sbe sb)

  obtain spf2 out nextState where
    spf2_sem: "spf2 \<in> (\<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>p) nextState" and
    transition: "(nextState, out) \<in> def_Bob_LLR.behavior.transitionC () State (def_Bob_HLR_Input.SBE.getter sbe)" and
    step_eq: "spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = def_Bob_HLR_Output.SBE.setter out \<Zcat>\<^sup>\<surd> spf2\<cdot>sb"
    using def_Bob_LLR.behavior.statesem_step_complete assms
    by (metis def_Bob_LLR.behavior.statesem_step_get
        def_Bob_HLR_Input.sbegetter_def
        def_Bob_HLR_Output.sbesetter_def
        sbeCons.prems)

  have left_side_fst: "fst (def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))) = 
                      fst (def_Bob_HLR_Output.sbgetter\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out) \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb))"
    by (metis (no_types)
        def_Bob_HLR_Output.SBE.settersb_strict
        def_Bob_HLR_Output.SBE.settersb_unfold
        sbconc_bot_r sconc_snd_empty
        step_eq)

  have left_side_snd: "snd (def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))) = 
                      snd (def_Bob_HLR_Output.sbgetter\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out) \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb))"
    by (metis
        def_Bob_HLR_Output.SBE.settersb_strict
        def_Bob_HLR_Output.SBE.settersb_unfold
        sbconc_bot_r sconc_snd_empty
        step_eq)

  have fst_calc: "fst (def_Bob_HLR_Output.sbgetter\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out) \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)) =
                  fst (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))))"
  proof -
    have "fst (def_Bob_HLR_Output.sbgetter\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out) \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)) =
          fst (def_Bob_HLR_Output.sbgetter\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out))) \<Zcat> 
          fst (def_Bob_HLR_Output.sbgetter\<cdot>(spf2\<cdot>sb))"
      using sbgetter_conc by auto
    
    also have "... = fst (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out)))) \<Zcat>
                    fst (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>sb)))"
      using sbgetter_ssplit_single sbeCons.IH[OF spf2_sem] by simp
    
    also have "... = fst (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out)) \<Zcat> 
                                        def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>sb)))"
      using ssplit_conc
      by (metis split_pairs2)
    
    also have "... = fst (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out) \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)))"
      by (metis (no_types, lifting)
          botconc2
          def_Bob_HLR_Output.SB.get_set
          def_Bob_HLR_Output.SB.getter_strict
          def_Bob_HLR_Output.SB.set_get
          def_Bob_HLR_Output.SBE.get_set
          def_Bob_HLR_Output.SBE.gettersb_unfold
          def_Bob_HLR_Output.SBE.settersb_strict
          def_Bob_HLR_Output.SBE.settersb_unfold
          def_Bob_HLR_Output.getter_conc2sbconc
          def_Bob_HLR_Output.setter_sbe2sb
          prod.collapse
          sbgetter_ssplit_single
          sconc_snd_empty sprojfst_sup
          sprojsnd_sup ssplit.rep_eq
          szip_ssplit)
    
    also have "... = fst (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))))"
      by (metis
          def_Bob_HLR_Output.SB.get_eq
          left_side_fst left_side_snd
          prod_eq_iff)
    
    finally show ?thesis .
  qed

  have snd_calc: "snd (def_Bob_HLR_Output.sbgetter\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out) \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)) =
                  snd (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))))"
  proof -
    have "snd (def_Bob_HLR_Output.sbgetter\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out) \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)) =
          snd (def_Bob_HLR_Output.sbgetter\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out))) \<Zcat> 
          snd (def_Bob_HLR_Output.sbgetter\<cdot>(spf2\<cdot>sb))"
      using sbgetter_conc by auto
    
    also have "... = snd (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out)))) \<Zcat>
                    snd (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>sb)))"
      using sbgetter_ssplit_single sbeCons.IH[OF spf2_sem] by simp
    
    also have "... = snd (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out)) \<Zcat> 
                                        def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>sb)))"
      using ssplit_conc
      by (metis split_pairs2)
    
    also have "... = snd (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(def_Bob_HLR_Output.SBE.setterSB\<cdot>(\<up>out) \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)))"
      by (metis (no_types, lifting)
          botconc2
          def_Bob_HLR_Output.SB.get_set
          def_Bob_HLR_Output.SB.getter_strict
          def_Bob_HLR_Output.SB.set_get
          def_Bob_HLR_Output.SBE.get_set
          def_Bob_HLR_Output.SBE.gettersb_unfold
          def_Bob_HLR_Output.SBE.settersb_strict
          def_Bob_HLR_Output.SBE.settersb_unfold
          def_Bob_HLR_Output.getter_conc2sbconc
          def_Bob_HLR_Output.setter_sbe2sb
          prod.collapse
          sbgetter_ssplit_single
          sconc_snd_empty sprojfst_sup
          sprojsnd_sup ssplit.rep_eq
          szip_ssplit)
    
    also have "... = snd (Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))))"
      by (metis
          def_Bob_HLR_Output.SB.get_eq
          left_side_fst left_side_snd
          prod_eq_iff)
    
    finally show ?thesis .
  qed

  show ?case
    by (metis fst_calc left_side_fst
        left_side_snd prod_eq_iff
        snd_calc)

next
   show "\<And>(sb::def_Bob_HLR_Input.channels\<^sup>\<Omega>) (spf::def_Bob_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Bob_HLR_Output.channels\<^sup>\<Omega>) State::nat tsyn \<times> bool.
       chDomEmpty TYPE(def_Bob_HLR_Input.channels) \<Longrightarrow>
       spf \<in> (\<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>p) State \<Longrightarrow> def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb) = Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>sb))" by simp
 qed


lemma bob_sb2sbeget: 
  "\<And>x sb. x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c \<Longrightarrow> def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb) = ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(x\<cdot>sb))"
  apply (induct_tac sb rule: sb_ind) 
     apply simp
  apply simp
proof -
  fix x sba
  assume x_sem: "x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c"
  assume zero_length: "#(sba::def_Bob_HLR_Input.channels\<^sup>\<Omega>) = 0"

  from def_Bob_LLR.behavior.ssem_apply_init_step[OF x_sem]
  obtain initState initOut spf where
    init: "(initState, initOut) \<in> def_Bob_LLR.behavior.initConfig ()" and
    spf_sem: "spf \<in> (\<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>p) initState" and
    x_def: "x\<cdot>sba = initOut \<Zcat>\<^sup>\<Omega> spf\<cdot>sba"
    by blast

  have input_dom_nonempty: "chDom TYPE(def_Bob_HLR_Input.channels) \<noteq> {}" by simp
  have least_sba: "sbIsLeast sba"
    using sbnleast_len zero_length by blast

  from def_Bob_LLR.behavior.ndastatesem_bottom_new spf_sem least_sba input_dom_nonempty 
  have spf_sba_bot: "spf\<cdot>sba = \<bottom>" by simp

  have l:"(def_Bob_HLR_Output.SBE.getterSB\<cdot>(initOut)) = \<up>(Eps, Eps)"using init def_Bob_LLR.behavior.initConfig_def 
    apply (simp add: Receiver_LLR_h_init_def)
    by (metis (no_types, opaque_lifting)
        botconc2 
        def_Bob_HLR_Output.SB.get_set
        def_Bob_HLR_Output.SB.getter_strict
        def_Bob_HLR_Output.SB.set_get
        def_Bob_HLR_Output.SBE.settersb_strict
        def_Bob_HLR_Output.SBE.settersb_unfold
        def_Bob_HLR_Output.getter_conc2sbconc
        def_Bob_HLR_Output.sbesetter_def
        def_Bob_HLR_Output.setter_sbe2sb
        fst_conv sbgetter_ssplit_single
        sconc_snd_empty snd_conv
        sprojfst_sup sprojsnd_sup
        ssplit.rep_eq
        szip_sproj)

  have r:"def_Bob_HLR_Output.sbgetter\<cdot>(initOut) = (\<up>Eps, \<up>Eps)"
    using init def_Bob_LLR.behavior.initConfig_def
    apply (simp add: Receiver_LLR_h_init_def)
    using
      def_Bob_HLR_Output.SB.get_set
      def_Bob_HLR_Output.sbesetter_def
      def_Bob_HLR_Output.setter_sbe2sb
    by presburger 

  from l r have "def_Bob_HLR_Output.sbgetter\<cdot>(initOut) = Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(initOut))"
    by (metis sprojfst_sup
        sprojsnd_sup
        ssplit.rep_eq)


  from this show "def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sba) = Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(x\<cdot>sba))"
    by (metis sbconc_bot_r spf_sba_bot
        x_def)
next
  fix x sba sbe
  assume x_sem: "x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c"
  assume step: "def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sba) = Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(x\<cdot>sba))"

  from def_Bob_LLR.behavior.ssem_apply_init_step[OF x_sem]
  obtain initState initOut spf where
    init: "(initState, initOut) \<in> def_Bob_LLR.behavior.initConfig ()" and
    spf_sem: "spf \<in> (\<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>p) initState" and
    x_def: "x\<cdot>(sbe \<Zcat>\<^sup>\<surd> sba) = initOut \<Zcat>\<^sup>\<Omega> spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sba)"
    by blast

  obtain spf2 out nextState where
    spf2_sem: "spf2 \<in> (\<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>p) nextState" and
    transition: "(nextState, out) \<in> def_Bob_LLR.behavior.transitionC () initState (def_Bob_HLR_Input.SBE.getter sbe)" and
    step_eq: "spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sba) = def_Bob_HLR_Output.SBE.setter out \<Zcat>\<^sup>\<surd> spf2\<cdot>sba"
    using def_Bob_LLR.behavior.statesem_step_complete spf_sem
    by (metis def_Bob_LLR.behavior.statesem_step_get def_Bob_HLR_Input.sbegetter_def def_Bob_HLR_Output.sbesetter_def)

  have IH_for_spf2: "def_Bob_HLR_Output.sbgetter\<cdot>(spf2\<cdot>sba) = Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf2\<cdot>sba))"
    using bob_sb2sbeget_stateSem spf2_sem by blast

  have l:"(def_Bob_HLR_Output.SBE.getterSB\<cdot>(initOut)) = \<up>(Eps, Eps)"using init def_Bob_LLR.behavior.initConfig_def 
    apply (simp add: Receiver_LLR_h_init_def)
    by (metis (no_types, opaque_lifting)
        botconc2
        def_Bob_HLR_Output.SB.get_set
        def_Bob_HLR_Output.SB.getter_strict
        def_Bob_HLR_Output.SB.set_get
        def_Bob_HLR_Output.SBE.settersb_strict
        def_Bob_HLR_Output.SBE.settersb_unfold
        def_Bob_HLR_Output.getter_conc2sbconc
        def_Bob_HLR_Output.sbesetter_def
        def_Bob_HLR_Output.setter_sbe2sb
        fst_conv sbgetter_ssplit_single
        sconc_snd_empty snd_conv
        sprojfst_sup sprojsnd_sup
        ssplit.rep_eq
        szip_sproj)

  have r:"def_Bob_HLR_Output.sbgetter\<cdot>(initOut) = (\<up>Eps, \<up>Eps)"
    using init def_Bob_LLR.behavior.initConfig_def
    apply (simp add: Receiver_LLR_h_init_def)
    using
      def_Bob_HLR_Output.SB.get_set
      def_Bob_HLR_Output.sbesetter_def
      def_Bob_HLR_Output.setter_sbe2sb
    by presburger 

  from l r have "def_Bob_HLR_Output.sbgetter\<cdot>(initOut) = Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(initOut))"
    by (metis sprojfst_sup
        sprojsnd_sup
        ssplit.rep_eq)

  have setter_getter_id: "sbeGen.setter def_Bob_HLR_Input.buildSBE (sbeGen.getter def_Bob_HLR_Input.buildSBE sbe) = sbe"
    by (simp add: def_Bob_HLR_Input.SBE.sbeGen_axioms sbeGen.set_get)
  
  have specific_step: "spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sba) = def_Bob_HLR_Output.sbesetter out \<Zcat>\<^sup>\<surd> spf2\<cdot>sba"
    using def_Bob_HLR_Output.sbesetter_def setter_getter_id step_eq by auto

  have left_side: "def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>((sbe \<Zcat>\<^sup>\<surd> sba))) = 
                  def_Bob_HLR_Output.sbgetter\<cdot>( initOut \<Zcat>\<^sup>\<Omega> (def_Bob_HLR_Output.sbesetter out) \<Zcat>\<^sup>\<surd> spf2\<cdot>sba)"
    by (simp add:  specific_step x_def)

  show "def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>(sbe \<Zcat>\<^sup>\<surd> sba)) = Stream.ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(x\<cdot>(sbe \<Zcat>\<^sup>\<surd> sba)))"
    using ssplit_step
    by (metis (no_types, lifting)
        IH_for_spf2
        conc_prod_stream_apply
        def_Bob_HLR_Output.SB.set_get
        def_Bob_HLR_Output.SBE.gettersb_unfold
        def_Bob_HLR_Output.SBE.settersb_strict
        def_Bob_HLR_Output.SBE.settersb_unfold
        def_Bob_HLR_Output.getter_conc2sbconc
        def_Bob_HLR_Output.setter_sbe2sb
        l prod.exhaust_sel r
        sbconc_bot_r sbgetter_ssplit_single
        ssplit_conc step_eq
        sup_conc_eps x_def)
qed

lemma bob_sb2sbeget2:assumes" x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c"
  shows  " x\<cdot>(def_Bob_HLR_Input.sbsetter\<cdot>s) = x\<cdot>(def_Bob_HLR_Input.SBE.setterSB\<cdot>s) "
  using sbestter_sbsetter_eq
  by simp

lemma h0: 
  "\<And>x sb. x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c \<Longrightarrow>
   (\<bbbW>) (def_Bob_HLR_Input.sbgetter\<cdot>sb) \<Longrightarrow> 
   assumption_0 () (def_Bob_HLR_Input.sbgetter\<cdot>sb) (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb)) \<Longrightarrow>
   predicate_0 () (def_Bob_HLR_Input.sbgetter\<cdot>sb) (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
proof -
  fix x sb
  assume x_sem: "x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c"
  
  have sbegen_result: 
    "\<And>i. fst (ssplit\<cdot>(sbeGen.getterSB def_Bob_HLR_Output.buildSBE\<cdot>(x\<cdot>(sbeGen.setterSB def_Bob_HLR_Input.buildSBE\<cdot>i)))) 
         = \<up>Eps \<Zcat> tsynProjSnd\<cdot>(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>i)"
    (is "\<And>i. ?P i")
  proof -
    fix i
    from bob_snd_sem_no_stream[OF x_sem, where i=i]
    have "fst (ssplit\<cdot>(sbeGen.getterSB def_Bob_HLR_Output.buildSBE\<cdot>(x\<cdot>(sbeGen.setterSB def_Bob_HLR_Input.buildSBE\<cdot>i)))) 
          = \<up>Eps \<Zcat> smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>i"
      by simp
    also have "... = \<up>Eps \<Zcat> tsynProjSnd\<cdot>(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>i)"
      unfolding tsynProjSnd_def Data_Bool_Tuple2tuple.simps
      by (metis (lifting) ext
          Data_Bool_Tuple2tuple.simps
          tsynProjSnd_def
          tsynProjSnd_equals_smap_snd) 
    finally show "?P i" .
  qed


  have assm1_rule: "\<And>sb. def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb) = ssplit\<cdot>(sbeGen.getterSB def_Bob_HLR_Output.buildSBE\<cdot>(x\<cdot>sb))"
    using bob_sb2sbeget
    using x_sem
    by blast
    
  have assm2_rule: "\<And>sb. x\<cdot>(def_Bob_HLR_Input.sbsetter\<cdot>sb) = x\<cdot>(def_Bob_HLR_Input.SBE.setterSB\<cdot>sb) " 
    using bob_sb2sbeget2
    using x_sem
    by blast
  
  have sbgen_result:
    "\<And>i. fst (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>(def_Bob_HLR_Input.sbsetter\<cdot>i))) 
         = \<up>Eps \<Zcat> tsynProjSnd\<cdot>(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>i)"
    using sbegen2sbgen_rule
    using assm1_rule assm2_rule
      def_Bob_HLR_Input.sbesettersb_def sbegen_result
    by presburger
  
  have specific_case:
    "fst (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb)) 
     = \<up>Eps \<Zcat> tsynProjSnd\<cdot>(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>(def_Bob_HLR_Input.sbgetter\<cdot>sb))"
    by (metis
        def_Bob_HLR_Input.SB.set_get
        sbgen_result)

  show "predicate_0 () (def_Bob_HLR_Input.sbgetter\<cdot>sb) (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
    unfolding predicate_0_def assumption_0_def
    using specific_case
    by force
qed



lemma tsynRemDups_h_map_snd:
  assumes "inj f"
  shows "map_tsyn f (snd (tsynRemDups_h x y)) = snd (tsynRemDups_h (map_tsyn f x) (map_tsyn f y))"
proof (cases y)
  case Eps
  then show ?thesis by simp
next
  case (Msg a)
  then show ?thesis 
  proof (cases x)
    case Eps
    then show ?thesis
      by (metis map_tsyn_is_Eps sndI
          tsynRemDups_h.elims) 
  next
    case (Msg a)
    then show ?thesis 
      apply (cases y;simp)
      by (metis assms injD)
  qed
qed

lemma tsynRemDups_h_map_fst:
  "map_tsyn f (fst (tsynRemDups_h x y)) = fst (tsynRemDups_h (map_tsyn f x) (map_tsyn f y))"
proof (cases y)
  case Eps
  then show ?thesis by simp
next
  case (Msg a)
  then show ?thesis 
  proof (cases x)
    case Eps
    then show ?thesis
      by (simp add: Msg)
  next
    case (Msg a)
    then show ?thesis 
      by (metis (no_types, lifting) Eps_eq_map_tsyn_iff
          tsynRemDups_h.elims fstI
          tsynRemDups_h.simps(1))
  qed
qed

lemma tsynRemDups_smap_h:
  assumes "inj f"
  shows   "smap (map_tsyn f)\<cdot>(sscanlAOne tsynRemDups_h state\<cdot>s) =
            sscanlAOne tsynRemDups_h (map_tsyn f state)\<cdot>
            (smap (map_tsyn f)\<cdot>s)"
proof (induction s arbitrary: state)
  case adm
  then show ?case by simp
next
  case bottom
  then show ?case 
    unfolding tsynRemDups_def sscanlAOne_def
    by simp
next
  case (step a s state)
  show ?case
    by (metis (no_types, lifting)
        tsynRemDups_h_map_fst
        tsynRemDups_h_map_snd
         local.step
        smap_scons StreamAutomaton.sscanlaone_step
        tsynRemDups_h_map_fst tsynRemDups_h_map_snd
        assms)
qed

lemma tsynRemDups_smap:
  assumes "inj f"
  shows    "smap (map_tsyn f)\<cdot>(tsynRemDups\<cdot>s) = 
   tsynRemDups\<cdot>(smap (map_tsyn f)\<cdot>s)"
  unfolding tsynRemDups_def 
  by (simp add: tsynRemDups_smap_h assms)


lemma tsynRemDups_smap_Data_Bool_Tuple2tuple:
  "smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>(tsynRemDups\<cdot>s) = 
   tsynRemDups\<cdot>(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>s)"
  apply (rule tsynRemDups_smap)
  using Data_Bool_Tuple2tuple_inj
  by simp
  

fun Data_Bool_pair :: " (nat tsyn \<times> bool) \<Rightarrow> (Data_Bool_Tuple tsyn)" where
  "Data_Bool_pair (\<sim>,  b) = \<sim>" |
  "Data_Bool_pair (TSynMsg d, b) = TSynMsg (Data_Bool_TupleConstr d b)"


lemma Bob_refs_HLR_out_h:
  assumes "spf \<in> def_Bob_LLR.behavior.StateSems_stream param state"
  shows "sprojsnd\<cdot>(spf\<cdot>s) = 
         \<Pi>\<^sub>1\<^sub>-(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>
               (sscanlAOne tsynRemDups_h (Data_Bool_pair state)\<cdot>s))"
  using assms
proof (induction s arbitrary: spf state rule: tsyn_ind)
  case adm
  then show ?case by simp
next
  case bot
  have "spf\<cdot>\<epsilon> = \<epsilon>"
    using bot
    by auto 
  then show ?case unfolding tsynRemDups_def sscanlAOne_def
    by simp
next
  case (msg m s)
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg (m)) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> def_Bob_LLR.behavior.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (def_Bob_LLR.behavior.transitionC param state (TSynMsg (m)))"
      using def_Bob_LLR.behavior.statesems_stream_step msg.prems
      by blast

    have step_tsyn: "sscanlAOne tsynRemDups_h (Data_Bool_pair state)\<cdot>(\<up>a \<Zcat> s) =
                   \<up>(snd (tsynRemDups_h (Data_Bool_pair state) a)) \<Zcat>
                   sscanlAOne tsynRemDups_h (fst (tsynRemDups_h (Data_Bool_pair state) a))\<cdot>s"
      by (simp add: StreamAutomaton.sscanlaone_step)

    have uneq : "state \<noteq> ((TSynMsg (Data_Bool_Tuple_get_fst m)),Data_Bool_Tuple_get_snd m) \<Longrightarrow> 
        out = (TSynMsg (Data_Bool_Tuple_get_snd m), TSynMsg (Data_Bool_Tuple_get_fst m))"using  trans def_Bob_LLR.behavior.transitionC_def
      by (smt Receiver_LLR_h_v2.elims
          case_unit insert_not_empty
          prod.inject singleton_iff
          tsyn.distinct(1)
          tsyn.inject)

    have eq : "state = ((TSynMsg (Data_Bool_Tuple_get_fst m)),Data_Bool_Tuple_get_snd m) \<Longrightarrow> 
        out = (TSynMsg (Data_Bool_Tuple_get_snd m), Eps)"using  trans def_Bob_LLR.behavior.transitionC_def
      by auto
  
  have rhs: "\<Pi>\<^sub>1\<^sub>-(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>
                (sscanlAOne tsynRemDups_h (Data_Bool_pair state)\<cdot>(\<up>(TSynMsg m) \<Zcat> s))) =
            \<up>(if state = (TSynMsg (Data_Bool_Tuple_get_fst m), Data_Bool_Tuple_get_snd m)
               then Eps
               else TSynMsg (Data_Bool_Tuple_get_fst m)) \<Zcat>
            \<Pi>\<^sub>1\<^sub>-(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>
                  (sscanlAOne tsynRemDups_h (Data_Bool_pair ns)\<cdot>s))"
  proof -
    have step_tsyn: "sscanlAOne tsynRemDups_h (Data_Bool_pair state)\<cdot>(\<up>(TSynMsg m) \<Zcat> s) =
                    \<up>(snd (tsynRemDups_h (Data_Bool_pair state) (TSynMsg m))) \<Zcat>
                    sscanlAOne tsynRemDups_h 
                      (fst (tsynRemDups_h (Data_Bool_pair state) (TSynMsg m)))\<cdot>s"
      by (simp add: StreamAutomaton.sscanlaone_step)
    
    have new_state: "fst (tsynRemDups_h (Data_Bool_pair state) (TSynMsg m)) = Data_Bool_pair ns"
      using trans
      apply  (cases state; cases "Data_Bool_pair state")
      apply simp_all
      by (smt R2
          def_Bob_LLR.behavior.transitionC_def
          Data_Bool_Tuple_get_fst.simps
          Data_Bool_Tuple_get_snd.elims(2,3)
          Data_Bool_pair.simps(2) eq_fst_iff
          insert_not_empty old.unit.case
          singletonD)+

    have head: "tsynFst (map_tsyn Data_Bool_Tuple2tuple 
                 (snd (tsynRemDups_h (Data_Bool_pair state) (TSynMsg m)))) =
               (if state = (TSynMsg (Data_Bool_Tuple_get_fst m), Data_Bool_Tuple_get_snd m)
                then Eps
                else TSynMsg (Data_Bool_Tuple_get_fst m))"
      apply  (cases state; cases m; simp)
      using Data_Bool_pair.elims
      by auto
    
    show ?thesis
      by (smt head new_state smap_scons
          step_tsyn
          tsynProjFst_def)
  qed
 
  have lhs: "sprojsnd\<cdot>(spf\<cdot>(\<up>(TSynMsg m) \<Zcat> s)) = 
            \<up>(snd out) \<Zcat> sprojsnd\<cdot>(nspf\<cdot>s)"
    by (simp add: step_def sprojsnd_def)
  
  have out_snd: "snd out = (if state = (TSynMsg (Data_Bool_Tuple_get_fst m), Data_Bool_Tuple_get_snd m)
                            then Eps
                            else TSynMsg (Data_Bool_Tuple_get_fst m))"
    using trans
    by (simp add: eq uneq)
  
    from msg show ?case
      using lhs nspf out_snd rhs
      by presburger
next
  case (Eps s)
  then show ?case
    apply (cases state) unfolding  sscanlAOne_def tsynProjFst_def 
      apply simp
      using Eps.prems by force
qed


lemma Bob_refs_HLR_out:
  assumes "spf \<in> def_Bob_LLR.behavior.Sems_stream param"
  shows "sprojsnd\<cdot>(spf\<cdot>s) = \<up>Eps \<Zcat> smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(tsynRemDups\<cdot>s)"
proof -
      obtain nspf initState initOut where
    step_def: "spf\<cdot>(s) = \<up>initOut \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> def_Bob_LLR.behavior.StateSems_stream param initState"and 
       trans:  "(initState,initOut) \<in> def_Bob_LLR.behavior.initConfigC param"
      using def_Bob_LLR.behavior.sems_stream_apply_init_step assms
      by blast

    have "initOut = (Eps, Eps)" 
      by (metis Pair_inject
          Receiver_LLR_h_init_def
          case_unit insert_not_empty
          singletonD trans)

  from Bob_refs_HLR_out_h[OF nspf]this 
  have eq1: "sprojsnd\<cdot>(spf\<cdot>s) = \<up>Eps \<Zcat>
             \<Pi>\<^sub>1\<^sub>-(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>
                   (sscanlAOne tsynRemDups_h (Data_Bool_pair (initState))\<cdot>s))"
    by (simp add: step_def)

  from trans have initial_state: "initState = (Eps, True) \<or> initState = (Eps, False)"
    by (simp add:
        Receiver_LLR_h_init_def)
  
  then have "Data_Bool_pair (initState) = Eps"
    by auto

  from this have tsyn_eq: "sscanlAOne tsynRemDups_h (Data_Bool_pair (initState)) = tsynRemDups"
    unfolding tsynRemDups_def  by simp
  
  from eq1 have proj: "sprojsnd\<cdot>(spf\<cdot>s) = \<up>Eps \<Zcat>
                 \<Pi>\<^sub>1\<^sub>-(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>(tsynRemDups\<cdot>s))"
    by (simp add: tsyn_eq)
  
  have projection_eq: "\<Pi>\<^sub>1\<^sub>-(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>x) = 
                       smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>x"
    for x :: "Data_Bool_Tuple tsyn stream"
    unfolding tsynProjFst_def
    by (metis (lifting)
        tsynProjFst_def
        tsynProjFst_smap_fst)
  
  show ?thesis
    by (simp add: proj projection_eq)
qed

lemma bob_fst_sem_stream:
  assumes "spf \<in> def_Bob_LLR.behavior.Sems_stream param"
  shows "snd (ssplit\<cdot>(spf\<cdot>(s))) 
         = \<up>Eps \<Zcat> (smap (map_tsyn Data_Bool_Tuple_get_fst) oo tsynRemDups)\<cdot>s"
  apply simp
  using Bob_refs_HLR_out 
  by (metis assms
      split_pairs
      ssplit.rep_eq)

lemma bob_fst_sem:
  assumes "spf \<in> def_Bob_LLR.behavior.Sem param"
  shows "snd (ssplit\<cdot>(def_Bob_HLR_Output.SBE.getterSB\<cdot>(spf\<cdot>(sbeGen.setterSB def_Bob_HLR_Input.buildSBE\<cdot>i)))) 
         = \<up>Eps \<Zcat> (smap (map_tsyn Data_Bool_Tuple_get_fst) oo tsynRemDups)\<cdot>i"
  apply simp
  apply (rule def_Bob_LLR.behavior.ssem2streamsem_rule[of param "(\<lambda> s res. snd (ssplit\<cdot>(res)) = \<up>Eps \<Zcat> smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(tsynRemDups\<cdot>i))" i spf])
  apply simp_all
   apply (simp add: bob_fst_sem_stream)
  using assms by simp

lemma h1: 
  "\<And>x sb. x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c \<Longrightarrow>
   (\<bbbW>) (def_Bob_HLR_Input.sbgetter\<cdot>sb) \<Longrightarrow> 
   assumption_1 () (def_Bob_HLR_Input.sbgetter\<cdot>sb) (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb)) \<Longrightarrow>
   predicate_1 () (def_Bob_HLR_Input.sbgetter\<cdot>sb) (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
proof -
  fix x sb
  assume x_sem: "x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c"
                                                     
  have sbegen_result: 
    "\<And>i. snd (ssplit\<cdot>(sbeGen.getterSB def_Bob_HLR_Output.buildSBE\<cdot>(x\<cdot>(sbeGen.setterSB def_Bob_HLR_Input.buildSBE\<cdot>i)))) 
         = \<up>Eps \<Zcat>(tsynProjFst oo tsynRemDups oo (smap (map_tsyn Data_Bool_Tuple2tuple)))\<cdot>i"
    (is "\<And>i. ?P i")
  proof -
    fix i
    have "snd (ssplit\<cdot>(sbeGen.getterSB def_Bob_HLR_Output.buildSBE\<cdot>(x\<cdot>(sbeGen.setterSB def_Bob_HLR_Input.buildSBE\<cdot>i)))) 
          = \<up>Eps \<Zcat> (smap (map_tsyn Data_Bool_Tuple_get_fst) oo tsynRemDups)\<cdot>i"
    using  bob_fst_sem[OF x_sem, where i=i] 
    by simp

  also have "... = \<up>Eps \<Zcat> tsynProjFst\<cdot>(tsynRemDups\<cdot>(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>i))" 
      by (metis (no_types, lifting) tsynProjFst_smap_fst 
          cfcomp2  tsynRemDups_smap_Data_Bool_Tuple2tuple)
    finally show "?P i" by simp
  qed
  
  have assm1_rule: "\<And>sb. def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb) = ssplit\<cdot>(sbeGen.getterSB def_Bob_HLR_Output.buildSBE\<cdot>(x\<cdot>sb))"
    using bob_sb2sbeget x_sem by blast
    
  have assm2_rule: "\<And>sb. x\<cdot>(def_Bob_HLR_Input.sbsetter\<cdot>sb) = x\<cdot>(def_Bob_HLR_Input.SBE.setterSB\<cdot>sb)" 
    using bob_sb2sbeget2 x_sem by blast
  
  have sbgen_result:
    "\<And>i. snd (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>(def_Bob_HLR_Input.sbsetter\<cdot>i))) 
         = \<up>Eps \<Zcat> (tsynProjFst oo tsynRemDups oo (smap (map_tsyn Data_Bool_Tuple2tuple)))\<cdot>i"
    by (metis assm1_rule
        def_Bob_HLR_Input.sbesettersb_def
        sbegen_result
        sbestter_sbsetter_eq)
  
  have specific_case:
    "snd (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb)) 
     = \<up>Eps \<Zcat> (tsynProjFst oo tsynRemDups oo (smap (map_tsyn Data_Bool_Tuple2tuple)))\<cdot>(def_Bob_HLR_Input.sbgetter\<cdot>sb)"
    by (metis def_Bob_HLR_Input.SB.set_get sbgen_result)

  have proj: " \<up> Eps \<Zcat> ((smap (map_tsyn Data_Bool_Tuple_get_fst)) oo tsynRemDups)\<cdot>(def_Bob_HLR_Input.sbgetter\<cdot>sb)
      =  \<up>Eps \<Zcat> (tsynProjFst oo tsynRemDups oo (smap (map_tsyn Data_Bool_Tuple2tuple)))\<cdot>(def_Bob_HLR_Input.sbgetter\<cdot>sb)"
    apply simp
    by (metis (no_types)
        tsynProjFst_smap_fst
        tsynRemDups_smap_Data_Bool_Tuple2tuple)

  show "predicate_1 () (def_Bob_HLR_Input.sbgetter\<cdot>sb) (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
    unfolding predicate_1_def assumption_1_def
    using specific_case proj
    by auto
qed

lemma causality:
  "\<And>x sb. x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c \<Longrightarrow> 
   causality (def_Bob_HLR_Input.sbgetter\<cdot>sb) (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
proof -
  fix x sb
  assume x_sem: "x \<in> \<lbrakk>(def_Bob_LLR.behavior.nda ())\<rbrakk>\<^sup>c"
  
  have strongpred_rel: "strongpred sb (x\<cdot>sb)"
    by (rule def_Bob_LLR.behavior.strongpred[OF x_sem])
  
  have input_len: "#\<^sub>\<surd>(def_Bob_HLR_Input.sbgetter\<cdot>sb) = #\<^sub>\<surd>sb"
    using def_Bob_HLR_Input.SB.getter_tlen
      somechannotempty by blast
  
  have output_len: "#\<^sub>\<surd>(def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb)) = #\<^sub>\<surd>(x\<cdot>sb)"
    using def_Bob_HLR_Output.SB.getter_tlen
      somechannotempty by blast

  show "causality (def_Bob_HLR_Input.sbgetter\<cdot>sb) (def_Bob_HLR_Output.sbgetter\<cdot>(x\<cdot>sb))"
    unfolding causality_def strongpred_def
    using strongpred_rel input_len output_len
    by (simp add: strongpred_def)
qed



end


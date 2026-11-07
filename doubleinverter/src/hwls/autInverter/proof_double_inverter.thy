theory proof_double_inverter
  imports inverter_automatonDoubleInverter.inverter_automatonDoubleInverter
begin



definition inverter::"bool stream \<rightarrow> bool stream" where
  "inverter  = (\<Lambda> x.  smap Not\<cdot>x)"

lemma settersb2setter: "(inverter_AutomatonInverter_Input.SB.setter\<cdot>x 
      = inverter_AutomatonInverter_Input.SBE.setterSB\<cdot>x)"
  apply (induction x)
  apply (simp add: inverter_AutomatonInverter_Input.SB.setter_def)
  using inverter_AutomatonInverter_Input.SB.set_get
     inverter_AutomatonInverter_Input.SB.setter.abs_eq strictI
     inverter_AutomatonInverter_Input.setter_conc2sbconc
     inverter_AutomatonInverter_Input.setter_sbe2sb
  by auto

lemma gettersb2getter: "(inverter_AutomatonInverter_Output.SB.getter\<cdot>x 
      = inverter_AutomatonInverter_Output.SBE.getterSB\<cdot>x)"
  apply (induction x)
  apply auto
  defer
  using inverter_AutomatonInverter_Output.getter_conc2sbconc
  apply (metis inverter_AutomatonInverter_Output.SB.get_set 
      inverter_AutomatonInverter_Output.setter_sbe2sb conc_stream_def)
  unfolding sbHdElemWell_def
  using inverter_AutomatonInverter_Output.Rep_channels_def
      inverter_AutomatonInverter_Output.rep_range inverter_AutomatonInverter_Output.channels.exhaust
  apply (simp add: inverter_AutomatonInverter_Output.SB.getter_def)
  using inverter_AutomatonInverter_Output.SB.getter.abs_eq sbbot_getch strictI
  by (metis (full_types) inverter_AutomatonInverter_Output.SB.get_set
      inverter_AutomatonInverter_Output.SB.getter.abs_eq sbbot_getch strictI)

lemma transition_simplified: "(transitionH_0 () state input) = (expression_0 () (state) (input))"
  using State.exhaust Substate.exhaust inverter_AutomatonInverter.guard_0.simps
  by (metis id_apply toBool_def transitionH_0.elims untimedExpression.lift_def)

lemma transition_range: "\<And> (state::State) (input::bool). (transitionH_0 () state input) 
      = {(State Substate.StateInitial, (liftedNot (input)))}"
  apply (simp add: transition_simplified)
  by (metis expression_0.elims liftedNot_def)

lemma assm: "(behavior.transition (), {(State StateInitial, \<bottom>)}) \<in> {(transition, initialConfig) 
      |(transition::State \<Rightarrow> inverter_AutomatonInverter_Input.channels\<^sup>\<surd> 
      \<Rightarrow> (State \<times> inverter_AutomatonInverter_Output.channels\<^sup>\<Omega>) set) 
      initialConfig::(State \<times>inverter_AutomatonInverter_Output.channels\<^sup>\<Omega>) set.(\<forall>(state::State) 
      sbe::inverter_AutomatonInverter_Input.channels\<^sup>\<surd>. transition state sbe \<noteq> {}) 
      \<and> initialConfig \<noteq> {}}"
  apply (simp add: Substate.exhaust getSubstate.cases)
  apply (simp add: behavior.transition_def)
  apply (simp add: behavior.transitionH_def)
  by (metis (mono_tags, hide_lams) empty_not_UNIV)

lemma initconfig_range: "ndaInitConfig\<cdot>(Abs_ndAutomaton (behavior.transition (), {(State StateInitial, \<bottom>)})) 
      = {(State StateInitial, \<bottom>)} "
  apply (simp add: ndaInitConfig.rep_eq)
  using assm
  by (simp add: Abs_ndAutomaton_inverse)

lemma statesem_reduction: "\<And>spf. (spf \<in> inverter_AutomatonInverter.Sps ())
      \<Longrightarrow> (spf \<in> behavior.StateSem () (State Substate.StateInitial))"
  apply (simp add: inverter_AutomatonInverter.Sps_def)
  apply (simp add: behavior.Sem_def)
  apply (simp add: behavior.StateSem_def)
  apply (simp add: behavior.nda_def)
  apply (simp add: behavior.initConfig_def)
  apply (simp add: inverter_AutomatonInverter.initialStates_def)
  apply (simp add: behavior.initConfig_def)
  apply (simp add: inverter_AutomatonInverter.initialStates_def)
  apply (simp add: ndaSem_def)
  apply (simp add: initconfig_range)
  apply auto
  by (simp add: Cfun.cfun.Rep_cfun_inverse)

lemma automaton_inverter_proof_sps_1: "\<And>spf. (spf \<in> inverter_AutomatonInverter.Sps ()) \<Longrightarrow> 
      (inverter_AutomatonInverter_Output.SBE.getterSB oo spf
      oo inverter_AutomatonInverter_Input.SBE.setterSB) = inverter"
  apply (simp add: inverter_def)
  apply (subst behavior.ndastatesem2sscanl)
  apply auto
  apply (simp add: inverter_AutomatonInverter.transition_def)
  apply (simp add: transition_range)
  using statesem_reduction
  apply blast
  apply (simp add: inverter_AutomatonInverter.transition_def)
  apply (simp add: sscanlautone2smap)
  by (simp add: eta_cfun)

lemma automaton_inverter_proof_sps_2: "\<And>spf. (spf \<in> inverter_AutomatonInverter.Sps ()) \<Longrightarrow> 
      (inverter_AutomatonInverter_Output.SB.getter oo spf
      oo inverter_AutomatonInverter_Input.SB.setter) = inverter"
  apply (subst cfcomp1)+
  apply (simp add: settersb2setter)
  apply (simp add: gettersb2getter)
  using automaton_inverter_proof_sps_1
  by (simp add: cfcomp1)



lemma automaton_inverter1_proof_sps: "\<And>spf. (spf \<in> inverter_automatonDoubleInverter_inverter1.Sps ())
      \<Longrightarrow> (inverter_automatonDoubleInverter_inverter1_Output.channelsRename.getter oo spf 
      oo inverter_automatonDoubleInverter_inverter1_Input.channelsRename.setter) = inverter"
  apply (simp add: inverter_automatonDoubleInverter_inverter1.Sps_def)
  apply (simp add: inverter_AutomatonInverter.Sps_def)
  apply (subst cfcomp1)+
  apply auto
  proof-
    have "\<And>spf. (spf \<in> inverter_AutomatonInverter.Sps ()) \<Longrightarrow> 
        (inverter_AutomatonInverter_Output.SB.getter oo spf
        oo inverter_AutomatonInverter_Input.SB.setter) = inverter"
      using automaton_inverter_proof_sps_2 by simp
    then show "\<And>spf.(spf \<in> behavior.Sem ()) \<Longrightarrow>
        (\<Lambda> (x::bool stream). inverter_AutomatonInverter_Output.SB.getter\<cdot>
        (spf\<cdot>(inverter_AutomatonInverter_Input.SB.setter\<cdot>x))) = inverter"
      apply (simp add: inverter_AutomatonInverter.Sps_def)
      by (simp add: cfcomp1)+
  qed



lemma automaton_inverter2_proof_sps: "\<And>spf. (spf \<in> inverter_automatonDoubleInverter_inverter2.Sps ())
      \<Longrightarrow> (inverter_automatonDoubleInverter_inverter2_Output.channelsRename.getter oo spf 
      oo inverter_automatonDoubleInverter_inverter2_Input.channelsRename.setter) = inverter"
  apply (simp add: inverter_automatonDoubleInverter_inverter2.Sps_def)
  apply (simp add: inverter_AutomatonInverter.Sps_def)
  apply (subst cfcomp1)+
  apply auto
  proof-
    have "\<And>spf. (spf \<in> inverter_AutomatonInverter.Sps ()) \<Longrightarrow> 
        (inverter_AutomatonInverter_Output.SB.getter oo spf
        oo inverter_AutomatonInverter_Input.SB.setter) = inverter"
      using automaton_inverter_proof_sps_2 by simp
    then show "\<And>spf.(spf \<in> behavior.Sem ()) \<Longrightarrow>
        (\<Lambda> (x::bool stream). inverter_AutomatonInverter_Output.SB.getter\<cdot>
        (spf\<cdot>(inverter_AutomatonInverter_Input.SB.setter\<cdot>x))) = inverter"
      apply (simp add: inverter_AutomatonInverter.Sps_def)
      by (simp add: cfcomp1)+
  qed



definition doubleInverter::"bool stream \<rightarrow> bool stream" where
  "doubleInverter  = (\<Lambda> x.  x)"

lemma inverter_comp:  "doubleInverter = inverter oo inverter"
  unfolding inverter_def
  apply (subst cfcomp1)
  apply (simp add: smaps2smap)
  unfolding doubleInverter_def
  using smap_id
  by (metis eq_id_iff)

lemma setter_eq_double: "inverter_automatonDoubleInverter_Input.SB.setter\<cdot>s 
      = ((inverter_automatonDoubleInverter_inverter1_Input.channelsRename.setter\<cdot>s)\<star>)"
  apply (subst sb_eqI)
  apply auto
  apply (simp add: inverter_AutomatonInverter_Input.buildSB_def)
  by (simp add: inverter_automatonDoubleInverter_Input.buildSB_def)

lemma getter_eq_double_help: "inverter_automatonDoubleInverter_Output.SB.setter\<cdot>s 
      = ((inverter_automatonDoubleInverter_inverter2_Output.channelsRename.setter\<cdot>s)\<star>)"
  apply (subst sb_eqI)
  apply auto
  apply (simp add: inverter_AutomatonInverter_Output.buildSB_def)
  by (simp add: inverter_automatonDoubleInverter_Output.buildSB_def)

lemma getter_eq_double: "inverter_automatonDoubleInverter_Output.SB.getter\<cdot>(sb) 
      = inverter_automatonDoubleInverter_inverter2_Output.channelsRename.getter\<cdot>(sb\<star>)"
  proof-
    obtain s where subst_sb: "(inverter_automatonDoubleInverter_Output.SB.setter\<cdot>s) = sb"
      using inverter_automatonDoubleInverter_Output.SB.set_get by blast
    then have "inverter_automatonDoubleInverter_Output.SB.getter\<cdot>
        (inverter_automatonDoubleInverter_Output.SB.setter\<cdot>s) =
        inverter_automatonDoubleInverter_inverter2_Output.channelsRename.getter\<cdot>
        (inverter_automatonDoubleInverter_inverter2_Output.channelsRename.setter\<cdot>s)"
      using inverter_automatonDoubleInverter_Output.SB.get_set
        inverter_automatonDoubleInverter_inverter2_Output.channelsRename.get_set
      by auto
    then have "inverter_automatonDoubleInverter_Output.SB.getter\<cdot>
        (inverter_automatonDoubleInverter_Output.SB.setter\<cdot>s) 
        = inverter_automatonDoubleInverter_inverter2_Output.channelsRename.getter\<cdot>
        ((inverter_automatonDoubleInverter_Output.SB.setter\<cdot>s)\<star>)"
      by (simp add: getter_eq_double_help)
    then show ?thesis
      by (simp add: subst_sb)
  qed

lemma setter_getter_inv_help: "(inverter_automatonDoubleInverter_inverter2_Input.channelsRename.setter\<cdot>s)
      = ((inverter_automatonDoubleInverter_inverter1_Output.channelsRename.setter\<cdot>s) \<star>)"
  apply (subst sb_eqI)
  apply auto
  apply (case_tac c;simp)
  apply auto
  using  inverter_AutomatonInverter_Output.buildSB_def inverter_AutomatonInverter_Input.buildSB_def
  apply (simp add: inverter_AutomatonInverter_Output.buildSB_def)
  by (simp add: inverter_AutomatonInverter_Input.buildSB_def)

lemma setter_getter_inv: "inverter_automatonDoubleInverter_inverter2_Input.channelsRename.setter\<cdot>
      (inverter_automatonDoubleInverter_inverter1_Output.channelsRename.getter\<cdot>(sb)) = (sb\<star>) "
  by (simp add: setter_getter_inv_help)

lemma automaton_doubleInverter_proof_spf_comp: "\<And> spf1 spf2.
      spf1 \<in> inverter_automatonDoubleInverter_inverter1.Sps () \<Longrightarrow>
      spf2 \<in> inverter_automatonDoubleInverter_inverter2.Sps () \<Longrightarrow>
      inverter_automatonDoubleInverter_inverter2_Output.channelsRename.getter oo spf2 
      oo inverter_automatonDoubleInverter_inverter2_Input.channelsRename.setter
      oo inverter_automatonDoubleInverter_inverter1_Output.channelsRename.getter oo spf1 
      oo inverter_automatonDoubleInverter_inverter1_Input.channelsRename.setter = doubleInverter"
  apply (simp add: automaton_inverter1_proof_sps)
  apply (rule cfun_eqI, simp)
  apply (simp add: inverter_comp)
  using automaton_inverter2_proof_sps cfcomp2
  by metis

lemma automaton_doubleInverter_proof_sps_unfolded: "\<And>spf1 spf2.
      spf1 \<in> inverter_automatonDoubleInverter_inverter1.Sps () \<Longrightarrow>
      spf2 \<in> inverter_automatonDoubleInverter_inverter2.Sps () \<Longrightarrow>
      inverter_automatonDoubleInverter_Output.SB.getter oo spfConvert\<cdot>(spf1 \<otimes> spf2)
      oo inverter_automatonDoubleInverter_Input.SB.setter = doubleInverter"
  apply (rule cfun_eqI, simp)
  apply (subst spfconvert_apply)+
  apply (subst spfcomp_serial)
  apply auto
  apply (subst sbunion_conv_snd)
  apply auto
  apply (simp add: getter_eq_double)
  apply (simp add: setter_eq_double)
  using automaton_doubleInverter_proof_spf_comp setter_getter_inv
  by (metis (no_types, lifting) cfcomp2)

lemma automaton_doubleInverter_proof_sps: "\<And>spf. (spf \<in> inverter_automatonDoubleInverter.Sps ()) 
      \<Longrightarrow> (inverter_automatonDoubleInverter_Output.SB.getter oo spf 
      oo inverter_automatonDoubleInverter_Input.SB.setter) = doubleInverter"
  apply (simp add: inverter_automatonDoubleInverter.Sps_def)
  apply (simp add: inverter_automatonDoubleInverter.rawSps_def)
  apply (simp add: spsConvert_def) 
  apply (simp add: spsComp_def)
  apply auto
  by (simp add: automaton_doubleInverter_proof_sps_unfolded)


end
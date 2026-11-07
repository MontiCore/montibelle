theory lightcontrol_HLR_Ref
  imports
    (* Gen  *) sps_LightcontrolHLR1.def_LightcontrolHLR1 sps_LightcontrolHLR2.def_LightcontrolHLR2
               sps_LightcontrolHLR2_flasher.def_LightcontrolHLR2_flasher sps_LightcontrolHLR2_and1.def_LightcontrolHLR2_and1 sps_LightcontrolHLR2_not1.def_LightcontrolHLR2_not1 sps_LightcontrolHLR2_or1.def_LightcontrolHLR2_or1 
    (* Hwl  *) reference.lightcontrol

begin



(*
lemma h[simp]: "wellformed (s:: ('a:: countable) tone stream)"
  apply (auto simp: Stream.wellformed_stream_def)
  done

lemma h_unpack_not[simp]:
  assumes "Fin n < #s"
  shows "inverseTOne (snth n (smap (\<lambda>x. TOneMsg (f (inverseTOne x)))\<cdot>s)) = f (inverseTOne (snth n s))"
  using assms by (simp add: smap_snth_lemma inverseTOne.simps)

lemma h_unpack_zip[simp]:
  assumes "Fin n < #s1" and "Fin n < #s2"
  shows "inverseTOne (snth n (smap (\<lambda>(a, b). TOneMsg (f (inverseTOne a) (inverseTOne b)))\<cdot>(szip\<cdot>s1\<cdot>s2))) = 
         f (inverseTOne (snth n s1)) (inverseTOne (snth n s2))"
  using assms by (simp add: smap_snth_lemma szip_nth inverseTOne.simps)
*)

lemma tone_to_bool_transfer:
  assumes "out = smap (\<lambda>(a, b). TOneMsg (inverseTOne a \<and> inverseTOne b))\<cdot>(szip\<cdot>in1\<cdot>in2)"
  shows "And_HLR (smap inverseTOne\<cdot>in1, smap inverseTOne\<cdot>in2) (smap inverseTOne\<cdot>out)"
  using assms
  apply (simp add: And_HLR.simps)
  apply (subst smapsmap2smap smap_szip[symmetric])
  apply (auto simp: smapsmap2smap)
  apply (simp add: o_def split_def)
  done


lemma tone_to_bool_lightcontrol:
  assumes "And_HLR (smap inverseTOne\<cdot>c_switch, smap inverseTOne\<cdot>c_not_out) (smap inverseTOne\<cdot>c_and_out)"
  assumes "Not_HLR (smap inverseTOne\<cdot>c_alarm) (smap inverseTOne\<cdot>c_not_out)"
  assumes "flasher_HLR (smap inverseTOne\<cdot>c_alarm) (smap inverseTOne\<cdot>c_flash_out)"
  assumes "Or_HLR (smap inverseTOne\<cdot>c_and_out, smap inverseTOne\<cdot>c_flash_out) (smap inverseTOne\<cdot>c_out)"
  shows "lightcontrol_HLR (smap inverseTOne\<cdot>c_switch, smap inverseTOne\<cdot>c_alarm) (smap inverseTOne\<cdot>c_out)"
  by (rule lightcontrol_pred[OF assms(1) assms(2) assms(3) assms(4)])


lemma tone_to_bool_and:
  "smap inverseTOne \<cdot>
   (smap (\<lambda>(a,b). TOneMsg (inverseTOne a \<and> inverseTOne b)) \<cdot> (szip\<cdot>x\<cdot>y)) =
   smap (\<lambda>(x,y). x \<and> y) \<cdot> (szip\<cdot>(smap inverseTOne\<cdot>x)\<cdot>(smap inverseTOne\<cdot>y))"
  using split_beta tone_to_bool_transfer by auto


lemma h1[simp]: "smap inverseTOne\<cdot>(smap (TOneMsg o f)\<cdot>s) = smap f \<cdot> s"
  proof (induction s)
    case (step a s)
    then show ?case 
      by simp 
  qed (simp_all)

lemma h2[simp]: "smap inverseTOne\<cdot>(\<up>(TOneMsg m) \<Zcat> s) = \<up>m \<Zcat> (smap inverseTOne\<cdot>s)"
  apply (subst smap_split)
  apply simp 
  done


lemma or_snth2:
  assumes "def_Or_HLR.wholePredicate () (s1,s2) s3"
and "Fin (t::nat)<#(s1,s2)"
shows "inverseTOne (snth t s3) = ((inverseTOne (snth t s1))\<or>(inverseTOne (snth t s2)))"
  using assms unfolding def_Or_HLR.wholePredicate_def def_Or_HLR.predicate_0_def def_Or_HLR.causality_def def_Or_HLR.assumption_0_def
  apply simp
  using len_prod_def2 smap_snth_lemma case_prod_beta' szip_nth
  by (smt inverseTOne.elims
      min_less_iff_conj split_pairs2
      szip_len)

lemma pred_0:
  assumes "def_Flasher_HLR1.wholePredicate ()  (def_LightcontrolHLR2_flasher_InputMap.connector\<cdot>(channel_flasher_input_val_pattern)) (def_LightcontrolHLR2_flasher_OutputMap.connector\<cdot>(channel_flasher_output_val_pattern))"
  assumes "def_And_HLR.wholePredicate ()  (def_LightcontrolHLR2_and1_InputMap.connector\<cdot>(channel_and1_input1_val_pattern, channel_and1_input2_val_pattern)) (def_LightcontrolHLR2_and1_OutputMap.connector\<cdot>(channel_and1_output_val_pattern))"
  assumes "def_Not_HLR.wholePredicate ()  (def_LightcontrolHLR2_not1_InputMap.connector\<cdot>(channel_not1_input_val_pattern)) (def_LightcontrolHLR2_not1_OutputMap.connector\<cdot>(channel_not1_output_val_pattern))"
  assumes "def_Or_HLR.wholePredicate ()  (def_LightcontrolHLR2_or1_InputMap.connector\<cdot>(channel_or1_input1_val_pattern, channel_or1_input2_val_pattern)) (def_LightcontrolHLR2_or1_OutputMap.connector\<cdot>(channel_or1_output_val_pattern))"
      and "wellformed (channel_alarmstatus_val_pattern, channel_switchstatus_val_pattern)"
      and "channel_and1_input1_val_pattern = channel_switchstatus_val_pattern"
      and "channel_not1_input_val_pattern = channel_alarmstatus_val_pattern"
      and "channel_flasher_input_val_pattern = channel_alarmstatus_val_pattern"
      and "channel_and1_input2_val_pattern = channel_not1_output_val_pattern"
      and "channel_or1_input1_val_pattern = channel_and1_output_val_pattern"
      and "channel_or1_input2_val_pattern = channel_flasher_output_val_pattern"
      and "channel_OnOffCmd_val_pattern = channel_or1_output_val_pattern"
    shows "def_LightcontrolHLR1.predicate_0 () (channel_alarmstatus_val_pattern, channel_switchstatus_val_pattern) (channel_OnOffCmd_val_pattern)"
proof -
  have flasher_hlr:
    "flasher_HLR (smap inverseTOne\<cdot>channel_alarmstatus_val_pattern)
                 (smap inverseTOne\<cdot>channel_flasher_output_val_pattern)"
    using assms(1,8)
    apply (simp add:
          def_Flasher_HLR1.wholePredicate_def
          def_Flasher_HLR1.predicate_0_def
          def_LightcontrolHLR2_flasher_InputMap.connector.rep_eq
          def_LightcontrolHLR2_flasher_OutputMap.connector.rep_eq)
    using assms
    unfolding def_Flasher_HLR1.predicate_0_def
    apply (simp add: smap_snth_lemma inverseTOne.simps)
    apply (simp add: convert_inductive_asm less2lnleD smap_snth_lemma)
    using assms
    unfolding def_Flasher_HLR1.predicate_0_def
    apply (simp add: inverseTOne.simps)
    using assms
    unfolding def_Flasher_HLR1.predicate_0_def
    apply simp
    using assms(1) def_Flasher_HLR1.wholePredicate_def def_LightcontrolHLR2_flasher_InputMap.connector.rep_eq
    def_LightcontrolHLR2_flasher_OutputMap.connector.rep_eq
    by (metis (no_types, lifting) empty_is_shortest shd1 smap_hd_rst snths_eq)

  have and_hlr:
    "And_HLR (smap inverseTOne\<cdot>channel_switchstatus_val_pattern,
              smap inverseTOne\<cdot>channel_not1_output_val_pattern)
             (smap inverseTOne\<cdot>channel_and1_output_val_pattern)"
    using assms(2,6,9)
    apply (simp add:
          def_And_HLR.wholePredicate_def
          def_And_HLR.predicate_0_def
          def_And_HLR.assumption_0_def
          def_LightcontrolHLR2_and1_InputMap.connector.rep_eq
          def_LightcontrolHLR2_and1_OutputMap.connector.rep_eq)
    apply (simp add: tone_to_bool_and)
    done

  have not_hlr:
    "Not_HLR (smap inverseTOne\<cdot>channel_alarmstatus_val_pattern)
             (smap inverseTOne\<cdot>channel_not1_output_val_pattern)"
    using assms(3,7)
    apply (simp add:
          def_Not_HLR.wholePredicate_def
          def_Not_HLR.predicate_0_def
          def_Not_HLR.assumption_0_def
          def_LightcontrolHLR2_not1_InputMap.connector.rep_eq
          def_LightcontrolHLR2_not1_OutputMap.connector.rep_eq
          Not_HLR.simps
          )
    apply (simp add: smapsmap2smap o_def)
    done
    

  have or_hlr:
    "Or_HLR (smap inverseTOne\<cdot>channel_and1_output_val_pattern,
             smap inverseTOne\<cdot>channel_flasher_output_val_pattern)
            (smap inverseTOne\<cdot>channel_OnOffCmd_val_pattern)"
    using assms(4,10,11,12)
    apply (simp add:
          def_Or_HLR.wholePredicate_def
          def_Or_HLR.predicate_0_def
          def_Or_HLR.assumption_0_def
          def_LightcontrolHLR2_or1_InputMap.connector.rep_eq
          def_LightcontrolHLR2_or1_OutputMap.connector.rep_eq
          Or_HLR.simps)
    apply (subst smapsmap2smap)
    apply (simp add: smapsmap2smap o_def split_def)
    done

  have lc_bool: "lightcontrol_HLR 
       (smap inverseTOne\<cdot>channel_switchstatus_val_pattern, 
        smap inverseTOne\<cdot>channel_alarmstatus_val_pattern) 
       (smap inverseTOne\<cdot>channel_OnOffCmd_val_pattern)"
  by (rule lightcontrol_pred[OF and_hlr not_hlr flasher_hlr or_hlr])

  show ?thesis
  apply (simp add: def_LightcontrolHLR1.predicate_0_def)
  apply (simp add: assms)
  using lc_bool apply simp
proof -
  have H:
    "\<forall>t::nat.
       Fin (Suc t) < #(smap inverseTOne\<cdot>channel_alarmstatus_val_pattern,
                       smap inverseTOne\<cdot>channel_switchstatus_val_pattern) \<longrightarrow>
       snth (Suc t) (smap inverseTOne\<cdot>channel_alarmstatus_val_pattern) \<and>
       snth t (smap inverseTOne\<cdot>channel_alarmstatus_val_pattern) \<longrightarrow>
       snth (Suc t) (smap inverseTOne\<cdot>channel_OnOffCmd_val_pattern) =
       (\<not> snth t (smap inverseTOne\<cdot>channel_OnOffCmd_val_pattern))"
    using lc_bool
    by simp

  show "\<forall>t::nat.
       Fin (Suc (Suc t)) \<le> #(channel_alarmstatus_val_pattern, channel_switchstatus_val_pattern) \<longrightarrow>
       inverseTOne (snth (Suc t) channel_alarmstatus_val_pattern) \<and>
       inverseTOne (snth t channel_alarmstatus_val_pattern) \<longrightarrow>
       inverseTOne (snth (Suc t) channel_or1_output_val_pattern) =
       (\<not> inverseTOne (snth t channel_or1_output_val_pattern))"
    apply rule
    apply rule 
    apply rule 
  proof -
    fix t
    assume a1:"Fin (Suc (Suc t)) \<le> #(channel_alarmstatus_val_pattern, channel_switchstatus_val_pattern)"
    assume a2:"inverseTOne (snth (Suc t) channel_alarmstatus_val_pattern) \<and> inverseTOne (snth t channel_alarmstatus_val_pattern)"
  have length1:"Fin (Suc t)< #(channel_not1_output_val_pattern, channel_and1_output_val_pattern)"
    using a1 assms
    by (metis (no_types, lifting) ext
        Fin_leq_Suc_leq
        LNat.lnat.inject
        Not_HLR.elims(2) and_hlr
        and_len antisym_conv2
        convert_inductive_asm
        len_prod_def2 min_less_iff_conj
        n_not_Suc_n not_hlr
        slen_smap)

  have length2:"Fin (Suc t)<#channel_or1_input2_val_pattern"
    using a1 assms(3)
  proof -
    have "#channel_alarmstatus_val_pattern = #channel_flasher_output_val_pattern"
      by (metis (no_types) flasher_hlr lightcontrol.flasher_HLR.elims(2) slen_smap)
    then show ?thesis
      by (metis (no_types) a1 assms(11) dual_order.strict_trans1 fst_conv leD len_prod_le_len_fst less2nat lessI linorder_le_less_linear)
  qed



  have "\<not> inverseTOne (snth (Suc t) channel_and1_input2_val_pattern) \<and> \<not> inverseTOne (snth t channel_and1_input2_val_pattern)"
    using a1 a2 not_snth  assms(2)
    by (metis (mono_tags, lifting)
        Not_HLR.simps assms(11,9)
        convert_inductive_asm
        flasher_hlr length2
        lightcontrol.flasher_HLR.simps
        not_hlr slen_smap
        smap_snth_lemma) 

  then have "\<not> inverseTOne (snth (Suc t) channel_or1_input1_val_pattern) \<and> \<not> inverseTOne (snth t channel_or1_input1_val_pattern)"
    using a1 a2 and_snth  assms(1) linorder_not_less and_len convert_inductive_asm len_prod_rsmaller
    by (metis (mono_tags, lifting)
        and_hlr assms(10,9) length1
        slen_smap
        smap_snth_lemma)


  then have onoff_snth:" (inverseTOne (snth (Suc t) channel_or1_output_val_pattern)) = 
                         (inverseTOne (snth (Suc t) channel_or1_input2_val_pattern)) \<and>
                          (inverseTOne (snth t channel_or1_output_val_pattern)) =  ( inverseTOne (snth t channel_or1_input2_val_pattern))"
    apply(subst or_snth2[of channel_or1_input1_val_pattern channel_or1_input2_val_pattern ])
    using assms(4)     unfolding  def_Or_HLR.wholePredicate_def def_Or_HLR.predicate_0_def def_Or_HLR.causality_def
    apply (simp add:
        def_LightcontrolHLR2_or1_InputMap.connector.rep_eq
        def_LightcontrolHLR2_or1_OutputMap.connector.rep_eq)
    using length1 length2 len_prod_def2
    apply (metis assms(10) min_less_iff_conj)
    apply(subst(4) or_snth2[of channel_or1_input1_val_pattern channel_or1_input2_val_pattern ])
    using assms(4)     unfolding  def_Or_HLR.wholePredicate_def def_Or_HLR.predicate_0_def def_Or_HLR.causality_def
    apply (simp add:
        def_LightcontrolHLR2_or1_InputMap.connector.rep_eq
        def_LightcontrolHLR2_or1_OutputMap.connector.rep_eq)
    using length1 length2 len_prod_def2
    apply (metis assms(10)
        convert_inductive_asm
        min_less_iff_conj)
    using convert_inductive_asm by blast

  have flasherout:"inverseTOne (snth (Suc t) channel_or1_input2_val_pattern) \<noteq> inverseTOne (snth t channel_or1_input2_val_pattern)"
    using a2 assms(3) length2
    using assms(11) flasher_hlr
    by (metis (mono_tags, lifting)
        assms(11) convert_inductive_asm
        flasher_hlr
        lightcontrol.flasher_HLR.elims(2)
        slen_smap
        smap_snth_lemma)


    show "inverseTOne (snth (Suc t) channel_or1_output_val_pattern) = (\<not> inverseTOne (snth t channel_or1_output_val_pattern))"
      using flasherout onoff_snth
      by auto
        qed
      qed
    qed

lemma causality:
  assumes "def_Flasher_HLR1.causality  (def_LightcontrolHLR2_flasher_InputMap.connector\<cdot>(channel_flasher_input_val_pattern)) (def_LightcontrolHLR2_flasher_OutputMap.connector\<cdot>(channel_flasher_output_val_pattern))"
  assumes "def_And_HLR.causality  (def_LightcontrolHLR2_and1_InputMap.connector\<cdot>(channel_and1_input1_val_pattern, channel_and1_input2_val_pattern)) (def_LightcontrolHLR2_and1_OutputMap.connector\<cdot>(channel_and1_output_val_pattern))"
  assumes "def_Not_HLR.causality  (def_LightcontrolHLR2_not1_InputMap.connector\<cdot>(channel_not1_input_val_pattern)) (def_LightcontrolHLR2_not1_OutputMap.connector\<cdot>(channel_not1_output_val_pattern))"
  assumes "def_Or_HLR.causality  (def_LightcontrolHLR2_or1_InputMap.connector\<cdot>(channel_or1_input1_val_pattern, channel_or1_input2_val_pattern)) (def_LightcontrolHLR2_or1_OutputMap.connector\<cdot>(channel_or1_output_val_pattern))"
      and "channel_and1_input1_val_pattern = channel_switchstatus_val_pattern"
      and "channel_not1_input_val_pattern = channel_alarmstatus_val_pattern"
      and "channel_flasher_input_val_pattern = channel_alarmstatus_val_pattern"
      and "channel_and1_input2_val_pattern = channel_not1_output_val_pattern"
      and "channel_or1_input1_val_pattern = channel_and1_output_val_pattern"
      and "channel_or1_input2_val_pattern = channel_flasher_output_val_pattern"
      and "channel_OnOffCmd_val_pattern = channel_or1_output_val_pattern"
    shows "def_LightcontrolHLR1.causality (channel_alarmstatus_val_pattern, channel_switchstatus_val_pattern) (channel_OnOffCmd_val_pattern)"
  apply(insert assms)
  apply(simp add: def_Flasher_HLR1.wholePredicate_def def_Flasher_HLR1.causality_def def_And_HLR.wholePredicate_def def_And_HLR.causality_def def_Not_HLR.wholePredicate_def def_Not_HLR.causality_def def_Or_HLR.wholePredicate_def def_Or_HLR.causality_def
                  def_LightcontrolHLR1.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: def_LightcontrolHLR2_flasher_InputMap.connector.rep_eq def_LightcontrolHLR2_flasher_OutputMap.connector.rep_eq def_LightcontrolHLR2_and1_InputMap.connector.rep_eq def_LightcontrolHLR2_and1_OutputMap.connector.rep_eq def_LightcontrolHLR2_not1_InputMap.connector.rep_eq def_LightcontrolHLR2_not1_OutputMap.connector.rep_eq def_LightcontrolHLR2_or1_InputMap.connector.rep_eq def_LightcontrolHLR2_or1_OutputMap.connector.rep_eq)?
  apply(simp add: def_LightcontrolHLR1.causality_def strongpred_def weakpred_def tlen_prod_def)?
  apply(rule conjI)? 
  by (metis (no_types, lifting) len_prod_def2 min.order_iff min_le_iff_disj)


end

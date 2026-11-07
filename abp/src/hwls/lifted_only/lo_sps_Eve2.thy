theory lo_sps_Eve2
imports
    move_to_core.hwl_tsynSBBoolFilter

    to_be_generated.hwl_tsynSBlens
begin



lemma def_Eve2_HLR_Output_getter_getch:
  "toTsynMsgStream\<cdot>(spf\<cdot>sb \<^enum> def_Eve2_HLR_Output.channel_output_val)
  = smap (map_tsyn boolEVENTConstr)\<cdot>(def_Eve2_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  by (metis def_Eve2_HLR_Output.SB.set_get def_Eve2_HLR_Output.SB.setter_getch def_Eve2_HLR_Output.buildSB_def def_Eve2_HLR_Output.channelsChan.simps toTsynMsgStream_smap_Timed_Tsyn_f)

lemma def_Eve2_HLR_Output_getter_getch2:
  "spf\<cdot>sb \<^enum> def_Eve2_HLR_Output.channel_output_val
  = tsynMsgToMStream\<cdot>(smap (map_tsyn boolEVENTConstr)\<cdot>(def_Eve2_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb)))"
  apply(rule totsynmsgstream_tsynmsgtomstream)
   apply(rule def_Eve2_HLR_Output_getter_getch)
  by (metis image_comp tsynchan_svalues)

lemma def_Eve2_HLR_Input_getter_getch:
  "toTsynMsgStream\<cdot>(sb \<^enum> def_Eve2_HLR_Input.channel_input_val)
  = smap (map_tsyn boolEVENTConstr)\<cdot>(def_Eve2_HLR_Input.sbgetter\<cdot>(sb))"
  by (metis def_Eve2_HLR_Input.SB.set_get def_Eve2_HLR_Input.SB.setter_rep def_Eve2_HLR_Input.buildSB_def def_Eve2_HLR_Input.channelsChan.simps sbgetch_insert2 toTsynMsgStream_smap_Timed_Tsyn_f)


lemma
  def_Eve2_HLR_sps_def2_pred:
  assumes "spf \<in> def_Eve2_HLR.Sps ()"
  shows "\<exists>ora.
    (spf\<cdot>sb) \<^enum> c = tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> def_Eve2_HLR_Input.channel_input_val))\<cdot>(ora))
  \<and> #({True} \<ominus> ora) = \<infinity>"
  apply(cases c, auto)
  apply(subst def_Eve2_HLR_Input_getter_getch)
  apply(subst def_Eve2_HLR_Output_getter_getch2)
  apply(insert assms)
  apply(auto simp add:
      def_Eve2_HLR.Sps_def
      def_Eve2_HLR.wholePredicate_def
      def_Eve2_HLR.assumption_0_def
      def_Eve2_HLR.predicate_0_def)
  apply(drule_tac x="sb" in spec)
  apply (simp add: well_all)
  apply(simp add: tsynMap_def2[symmetric] tsynboolfilter_tsynmap)
  by (metis tsynboolfilter_tsynmap inf_ub sfilterl4)
  


lemma
  def_Eve2_HLR_sps_def2:
  assumes "spf \<in> def_Eve2_HLR.Sps ()"
  shows "\<exists>ora. spf\<cdot>sb = sbRenameCh (\<lambda> _. def_Eve2_HLR_Input.channel_input_val)\<cdot>(tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda> _. ora))  \<and> #({True} \<ominus> ora) = \<infinity>"
proof -
  obtain ora
    where ora_def: "\<And>c. ((spf\<cdot>sb) \<^enum> c) = tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> def_Eve2_HLR_Input.channel_input_val))\<cdot>(ora))"
      and ora_inf: "#({True} \<ominus> ora) = \<infinity>"
    by (metis (full_types) def_Eve2_HLR_sps_def2_pred assms def_Eve2_HLR_Output.channels.exhaust)


  show ?thesis
    apply(rule_tac x="ora" in exI)
    apply auto
    apply(rule tsynsbboolfilter_insert)
      apply(rule ora_def)
     apply(case_tac c, auto simp add: ctype_def)
    by(rule ora_inf)
qed

end

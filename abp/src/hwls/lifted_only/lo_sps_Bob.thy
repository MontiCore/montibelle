theory lo_sps_Bob
imports
    move_to_core.hwl_tsynSBBoolFilter

    to_be_generated.hwl_tsynSBlens
begin


lemma def_Bob_HLR_Input_getter_getch:
  "toTsynMsgStream\<cdot>(sb \<^enum> def_Bob_HLR_Input.channel_input_val)
  = smap (map_tsyn DataBoolTupleEVENTConstr)\<cdot>(def_Bob_HLR_Input.sbgetter\<cdot>(sb))"
  by (metis def_Bob_HLR_Input.SB.set_get def_Bob_HLR_Input.SB.setter_rep def_Bob_HLR_Input.buildSB_def def_Bob_HLR_Input.channelsChan.simps sbgetch_insert2 toTsynMsgStream_smap_Timed_Tsyn_f)

lemma def_Bob_HLR_Output_getter_getch_ctrl:
  "toTsynMsgStream\<cdot>(spf\<cdot>sb \<^enum> def_Bob_HLR_Output.channel_control_val)
  = smap (map_tsyn boolEVENTConstr)\<cdot>(fst (def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb)))"
  apply(subgoal_tac "\<exists> ns bs. spf\<cdot>sb = def_Bob_HLR_Output.sbsetter\<cdot>(ns, bs)")
  apply(auto simp add: def_Bob_HLR_Output.buildSB_def toTsynMsgStream_smap_Timed_Tsyn_f)
  by (metis def_Bob_HLR_Output.SB.set_get prod.collapse)

lemma def_Bob_HLR_Output_getter_getch_ctrl2:
  "spf\<cdot>sb \<^enum> def_Bob_HLR_Output.channel_control_val
  = tsynMsgToMStream\<cdot>(smap (map_tsyn boolEVENTConstr)\<cdot>(fst (def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb))))"
  apply(rule totsynmsgstream_tsynmsgtomstream)
   apply(rule def_Bob_HLR_Output_getter_getch_ctrl)
  by (metis image_comp tsynchan_svalues)

lemma def_Bob_HLR_Output_getter_getch_out:
  "toTsynMsgStream\<cdot>(spf\<cdot>sb \<^enum> def_Bob_HLR_Output.channel_output_val)
  = smap (map_tsyn natEVENTConstr)\<cdot>(snd (def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb)))"
  apply(subgoal_tac "\<exists> ns bs. spf\<cdot>sb = def_Bob_HLR_Output.sbsetter\<cdot>(ns, bs)")
  apply(auto simp add: def_Bob_HLR_Output.buildSB_def toTsynMsgStream_smap_Timed_Tsyn_f)
  by (metis def_Bob_HLR_Output.SB.set_get prod.collapse)

lemma def_Bob_HLR_Output_getter_getch_out2:
  "spf\<cdot>sb \<^enum> def_Bob_HLR_Output.channel_output_val
  = tsynMsgToMStream\<cdot>(smap (map_tsyn natEVENTConstr)\<cdot>(snd (def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb))))"
  apply(rule totsynmsgstream_tsynmsgtomstream)
   apply(rule def_Bob_HLR_Output_getter_getch_out)
  by (metis image_comp tsynchan_svalues)



lemma
  def_Bob_HLR_sps_def2_pred_1:
  assumes "spf \<in> def_Bob_HLR.Sps ()"
  shows "spf\<cdot>sb  \<^enum>  def_Bob_HLR_Output.channel_control_val
  = tsynMsgToMStream\<cdot>((smap (map_tsyn boolEVENTConstr) oo tsynProjSnd oo smap (map_tsyn (Data_Bool_Tuple2tuple o inv DataBoolTupleEVENTConstr)))\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  def_Bob_HLR_Input.channel_input_val)))"
  apply(subst def_Bob_HLR_Input_getter_getch)
  apply(subst def_Bob_HLR_Output_getter_getch_ctrl2)
  apply(insert assms)
  apply(auto simp add:
      def_Bob_HLR.Sps_def
      def_Bob_HLR.wholePredicate_def
      def_Bob_HLR.assumption_0_def
      def_Bob_HLR.predicate_0_def
      def_Bob_HLR.assumption_1_def
      def_Bob_HLR.predicate_1_def)
  apply(drule_tac x="sb" in spec)
  by (auto simp add: well_all smaps2smap map_tsyn.compositionality)


lemma
  def_Bob_HLR_sps_def2_pred_2:
  assumes "spf \<in> def_Bob_HLR.Sps ()"
  shows "spf\<cdot>sb  \<^enum>  def_Bob_HLR_Output.channel_output_val
  = tsynMsgToMStream\<cdot>((smap (map_tsyn natEVENTConstr) oo tsynProjFst oo tsynRemDups oo smap (map_tsyn (Data_Bool_Tuple2tuple o inv DataBoolTupleEVENTConstr)))\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  def_Bob_HLR_Input.channel_input_val)))"
  apply(subst def_Bob_HLR_Input_getter_getch)
  apply(subst def_Bob_HLR_Output_getter_getch_out2)
  apply(insert assms)
  apply(auto simp add:
      def_Bob_HLR.Sps_def
      def_Bob_HLR.wholePredicate_def
      def_Bob_HLR.assumption_0_def
      def_Bob_HLR.predicate_0_def
      def_Bob_HLR.assumption_1_def
      def_Bob_HLR.predicate_1_def)
  apply(drule_tac x="sb" in spec)
  by (auto simp add: well_all smaps2smap map_tsyn.compositionality)


end

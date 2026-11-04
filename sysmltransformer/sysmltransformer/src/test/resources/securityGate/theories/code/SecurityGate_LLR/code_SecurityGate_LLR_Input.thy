theory code_SecurityGate_LLR_Input
  imports
    (* Gen  *) bundle_SecurityGate_LLR.def_SecurityGate_LLR_Input
    (* Core *) bundle.SBCodegen
    (* Hwl  *)

begin


lemma [code]:"Enum.enum_ex (P::channels \<Rightarrow> bool) =  (\<exists>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

lemma [code]:"Enum.enum_all (P::channels \<Rightarrow> bool) =  (\<forall>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

lemma [code,simp]:"Rep_channels channel_input_data = (CH ''channel_input_data'' TTLive TActionEnumEVENT)"
using channel_input_data_rep Rep_channels_def by auto

lemma[code]:" Abs_channels (CH ''channel_input_data'' TTLive TActionEnumEVENT) = channel_input_data"
by(simp add: channel_input_data_def)


fun conv_ActionEnum ::"M \<Rightarrow> ActionEnum event" where
"conv_ActionEnum (Timed ( TLive ( EventMsg (ActionEnumEVENTConstr a)))) = EventMsg a"|
"conv_ActionEnum (Timed (TLive Tick)) = Tick"|
"conv_ActionEnum  v = inv (Timed o TLive o map_event ActionEnumEVENTConstr) v"

lemma inv2conv_ActionEnum[code_abbrev]:"(conv_ActionEnum a) = inv (Timed o TLive o map_event ActionEnumEVENTConstr) a"
  apply(cases a,simp_all)
  apply(case_tac x2,simp_all)
  by(rename_tac x1,case_tac x1;
    (rename_tac x2,case_tac x2;
    (simp add: inv_f_eq | rename_tac x3, case_tac x3)+))

lemma [code_abbrev]:"sbesetter = sbeGen.setter buildSBE"
  by(simp add: sbesetter_def)

lemma sbegeth: assumes "a channel_input_data \<in> range (Timed o TLive o map_event ActionEnumEVENTConstr)"
                        shows "inv (channelsChan (Timed o TLive o map_event ActionEnumEVENTConstr)) a = channelsChan_inv (Timed o TLive o map_event ActionEnumEVENTConstr) a"
  unfolding channelsChan_inv_def
(*
  using assms inv_f_f channelsChan_inv_def channelsChan_surj_helper buildSBE_def build_inj by metis
*)
sorry

lemma sbegeth2 :assumes "\<forall>c. a c \<in> ctype (Rep c)"
  shows"sbegetter (Abs_sbElem (Some a)) = inv buildSBE a"
  by (metis assms(1) Abs_sbElem_inverse SBE.getter_def mem_Collect_eq option.simps(5) sbElem_well.simps(2))

lemma [code]:"sbegetter sbe = (case Rep_sbElem sbe of Some (f::channels \<Rightarrow> M)
\<Rightarrow> ((inv (Timed o TLive o map_event ActionEnumEVENTConstr) (the (Rep_sbElem (sbe)) channel_input_data))))"
  apply(cases sbe, case_tac y)
  apply (simp add: option.case_eq_if)+
  apply(subst Abs_sbElem_inverse,simp_all)+
(* Doesn't work for cc
  by (metis buildSBE_def build_surj channelsChan.simps channelsChan_inv_def f_inv_into_f rangeI sbegeth sbegeth2)
*)
  sorry

lemma [code_abbrev]:"sbegetter = sbeGen.getter buildSBE"
by(simp add: sbegetter_def)

lemma [ccode]:" sbesettersb\<cdot>((updis l) && ls) = (sbesetter ( l)) \<Zcat>\<^sup>\<surd> (sbesettersb\<cdot>ls)"
  and [ccode]:" sbesettersb\<cdot> \<epsilon> = botsb"
  using sbesettersb_def apply auto[1]
  by (simp add: botsb_eq)

lemma [code_abbrev]:"(\<lambda>a. sbesettersb\<cdot>a) = (\<lambda>a. sbeGen.setterSB buildSBE\<cdot>a)"
  by(simp add: sbesettersb_def)

lemma [code]:"Rep_cfun sbesettersb = sbesettersb_nc"
  by(simp add: sbesettersb_nc_def)

definition insbsetter_nc::" (ActionEnum event stream) \<Rightarrow> channels\<^sup>\<Omega>" where
"insbsetter_nc =  Abs_lsb o buildSB"

lemma[code]:"Rep_lsb(insbsetter_nc a) = buildSB a"
  using insbsetter_nc_def SB.setter.rep_eq SB.setter_rep by auto

lemma[code]:"Rep_cfun(sbsetter) =  insbsetter_nc"
  using insbsetter_nc_def SB.setter.rep_eq sbsetter_def by auto

lemma[code]:"Rep_cfun(sbgetter) = (inv buildSB) o  Rep_lsb"
  by(simp add: SB.getter.rep_eq)

lemma sbgetterh2:"Rep_lsb sb channel_input_data = smap (Timed o TLive o map_event ActionEnumEVENTConstr)\<cdot>((inv buildSB o Rep_lsb) sb)"
(* Doesn't work for cc
  by (metis SB.getter.rep_eq SB.set_get SB.setter_rep buildSB_def channelsChan.simps)
*)
  sorry

lemma smap_conv_ActionEnum:" smap (inv  (Timed o TLive o map_event ActionEnumEVENTConstr))\<cdot>s = smap conv_ActionEnum\<cdot>s"
  apply(induction s,simp_all)
  apply(subst inject_scons,simp_all)
  by(simp add: inv2conv_ActionEnum comp_def)


lemma sbgetterh:"sbgetter\<cdot> sb = ( 
  smap conv_ActionEnum\<cdot> (Rep_lsb sb channel_input_data)   
 ) "
  apply(simp add: sbgetter_def)
(*
  using SB.getter_def  smapsmap2smap sbgetterh2 
  SB.getter.abs_eq inj_compose inj_tonetimed sbgetter_def ActionEnumEVENTConstr_inj  smap_inv_eq
  by (metis prod.collapse smap_conv_ActionEnum )
*)
  sorry

lemma [code_abbrev]:"(\<lambda>a. (smap conv_ActionEnum\<cdot> (Rep_lsb a channel_input_data))) = (\<lambda>a. ((inv buildSB) o  Rep_lsb) a)"
  apply(simp add: buildSB_def channelsChan_inv_def)
  using SB.getter.rep_eq buildSB_def sbgetterh smap_conv_ActionEnum 
  by auto


end

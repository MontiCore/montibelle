theory code_Alice_LLR_Input
  imports
    (* Gen  *) bundle_Alice_LLR.def_Alice_LLR_Input
    (* Core *) bundle.SBCodegen
    (* Hwl  *)

begin


lemma [code]:"Enum.enum_ex (P::channels \<Rightarrow> bool) =  (\<exists>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

lemma [code]:"Enum.enum_all (P::channels \<Rightarrow> bool) =  (\<forall>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

lemma [code,simp]:"Rep_channels channel_control_val = (CH ''channel_control_val'' TTsyn TboolSYNC)"
using channel_control_val_rep Rep_channels_def by auto

lemma[code]:" Abs_channels (CH ''channel_control_val'' TTsyn TboolSYNC) = channel_control_val"
by(simp add: channel_control_val_def)

lemma [code,simp]:"Rep_channels channel_input_val = (CH ''channel_input_val'' TTsyn TstringSYNC)"
using channel_input_val_rep Rep_channels_def by auto

lemma[code]:" Abs_channels (CH ''channel_input_val'' TTsyn TstringSYNC) = channel_input_val"
by(simp add: channel_input_val_def)


fun conv_bool ::"M \<Rightarrow> bool tsyn" where
"conv_bool (Timed ( Tsyn ( TSynMsg (boolSYNCConstr a)))) = TSynMsg a"|
"conv_bool (Timed (Tsyn Eps)) = Eps"|
"conv_bool  v = inv (Timed o Tsyn o map_tsyn boolSYNCConstr) v"

lemma inv2conv_bool[code_abbrev]:"(conv_bool a) = inv (Timed o Tsyn o map_tsyn boolSYNCConstr) a"
  apply(cases a,simp_all)
  apply(case_tac x2,simp_all)
  by(rename_tac x1,case_tac x1;
    (rename_tac x2,case_tac x2;
    (simp add: inv_f_eq | rename_tac x3, case_tac x3)+))

fun conv_string ::"M \<Rightarrow> string tsyn" where
"conv_string (Timed ( Tsyn ( TSynMsg (stringSYNCConstr a)))) = TSynMsg a"|
"conv_string (Timed (Tsyn Eps)) = Eps"|
"conv_string  v = inv (Timed o Tsyn o map_tsyn stringSYNCConstr) v"

lemma inv2conv_string[code_abbrev]:"(conv_string a) = inv (Timed o Tsyn o map_tsyn stringSYNCConstr) a"
  apply(cases a,simp_all)
  apply(case_tac x2,simp_all)
  by(rename_tac x1,case_tac x1;
    (rename_tac x2,case_tac x2;
    (simp add: inv_f_eq | rename_tac x3, case_tac x3)+))

lemma [code_abbrev]:"sbesetter = sbeGen.setter buildSBE"
  by(simp add: sbesetter_def)

lemma sbegeth: assumes "a channel_control_val \<in> range (Timed o Tsyn o map_tsyn boolSYNCConstr)"
                    and "a channel_input_val \<in> range (Timed o Tsyn o map_tsyn stringSYNCConstr)"
                        shows "inv (channelsChan (Timed o Tsyn o map_tsyn boolSYNCConstr) (Timed o Tsyn o map_tsyn stringSYNCConstr)) a = channelsChan_inv (Timed o Tsyn o map_tsyn boolSYNCConstr) (Timed o Tsyn o map_tsyn stringSYNCConstr) a"
  unfolding channelsChan_inv_def
(*
  using assms inv_f_f channelsChan_inv_def channelsChan_surj_helper buildSBE_def build_inj by metis
*)
sorry

lemma sbegeth2 :assumes "\<forall>c. a c \<in> ctype (Rep c)"
  shows"sbegetter (Abs_sbElem (Some a)) = inv buildSBE a"
  by (metis assms(1) Abs_sbElem_inverse SBE.getter_def mem_Collect_eq option.simps(5) sbElem_well.simps(2))

lemma [code]:"sbegetter sbe = (case Rep_sbElem sbe of Some (f::channels \<Rightarrow> M)
\<Rightarrow> ((inv (Timed o Tsyn o map_tsyn boolSYNCConstr) (the (Rep_sbElem (sbe)) channel_control_val))), ((inv (Timed o Tsyn o map_tsyn stringSYNCConstr) (the (Rep_sbElem (sbe)) channel_input_val))))"
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

definition insbsetter_nc::" (bool tsyn stream \<times> string tsyn stream) \<Rightarrow> channels\<^sup>\<Omega>" where
"insbsetter_nc =  Abs_lsb o buildSB"

lemma[code]:"Rep_lsb(insbsetter_nc a) = buildSB a"
  using insbsetter_nc_def SB.setter.rep_eq SB.setter_rep by auto

lemma[code]:"Rep_cfun(sbsetter) =  insbsetter_nc"
  using insbsetter_nc_def SB.setter.rep_eq sbsetter_def by auto

lemma[code]:"Rep_cfun(sbgetter) = (inv buildSB) o  Rep_lsb"
  by(simp add: SB.getter.rep_eq)

lemma sbgetterh2:"Rep_lsb sb channel_control_val = smap (Timed o Tsyn o map_tsyn boolSYNCConstr)\<cdot>(fst ((inv buildSB o Rep_lsb) sb))"
(* Doesn't work for cc
  by (metis SB.getter.rep_eq SB.set_get SB.setter_rep buildSB_def channelsChan.simps)
*)
  sorry

lemma sbgetterh3:"Rep_lsb sb channel_input_val = smap (Timed o Tsyn o map_tsyn stringSYNCConstr)\<cdot>(snd ((inv buildSB o Rep_lsb) sb))"
(* Doesn't work for cc
  by (metis SB.getter.rep_eq SB.set_get SB.setter_rep buildSB_def channelsChan.simps)
*)
  sorry

lemma smap_conv_bool:" smap (inv  (Timed o Tsyn o map_tsyn boolSYNCConstr))\<cdot>s = smap conv_bool\<cdot>s"
  apply(induction s,simp_all)
  apply(subst inject_scons,simp_all)
  by(simp add: inv2conv_bool comp_def)

lemma smap_conv_string:" smap (inv  (Timed o Tsyn o map_tsyn stringSYNCConstr))\<cdot>s = smap conv_string\<cdot>s"
  apply(induction s,simp_all)
  apply(subst inject_scons,simp_all)
  by(simp add: inv2conv_string comp_def)


lemma sbgetterh:"sbgetter\<cdot> sb = ( 
  smap conv_bool\<cdot> (Rep_lsb sb channel_control_val)   , 

  smap conv_string\<cdot> (Rep_lsb sb channel_input_val)   
 ) "
  apply(simp add: sbgetter_def)
(*
  using SB.getter_def  smapsmap2smap sbgetterh2 sbgetterh3 
  SB.getter.abs_eq inj_compose inj_tonetimed sbgetter_def boolSYNCConstr_inj stringSYNCConstr_inj  smap_inv_eq
  by (metis prod.collapse smap_conv_bool smap_conv_string )
*)
  sorry

lemma [code_abbrev]:"(\<lambda>a. (smap conv_bool\<cdot> (Rep_lsb a channel_control_val), smap conv_string\<cdot> (Rep_lsb a channel_input_val))) = (\<lambda>a. ((inv buildSB) o  Rep_lsb) a)"
  apply(simp add: buildSB_def channelsChan_inv_def)
  using SB.getter.rep_eq buildSB_def sbgetterh smap_conv_bool smap_conv_string 
  by auto


end

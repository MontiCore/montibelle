theory Event3Output_gen
  imports
    (* Gen  *) Event3Output
    (* Core *) bundle.SBCodegen
    (* Hwl  *)

begin


lemma [code]:"Enum.enum_ex (P::channels \<Rightarrow> bool) =  (\<exists>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

lemma [code]:"Enum.enum_all (P::channels \<Rightarrow> bool) =  (\<forall>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

lemma [code,simp]:"Rep_channels beOutChannel_rep = (CH ''beOutChannel_rep'' TTLive TboolEVENT)"
using beOutChannel_rep_rep Rep_channels_def by auto

lemma[code]:" Abs_channels (CH ''beOutChannel_rep'' TTLive TboolEVENT) = beOutChannel_rep"
by(simp add: beOutChannel_rep_def)

lemma [code,simp]:"Rep_channels natOutChannel_rep = (CH ''natOutChannel_rep'' TTLive TnatEVENT)"
using natOutChannel_rep_rep Rep_channels_def by auto

lemma[code]:" Abs_channels (CH ''natOutChannel_rep'' TTLive TnatEVENT) = natOutChannel_rep"
by(simp add: natOutChannel_rep_def)

lemma [code,simp]:"Rep_channels sOutChannel_rep = (CH ''sOutChannel_rep'' TTLive TstringEVENT)"
using sOutChannel_rep_rep Rep_channels_def by auto

lemma[code]:" Abs_channels (CH ''sOutChannel_rep'' TTLive TstringEVENT) = sOutChannel_rep"
by(simp add: sOutChannel_rep_def)


fun conv_bool ::"M \<Rightarrow> bool event" where
"conv_bool (Timed ( TLive ( EventMsg (boolEVENTConstr a)))) = EventMsg a"|
"conv_bool (Timed (TLive Tick)) = Tick"|
"conv_bool  v = inv (Timed o TLive o map_event boolEVENTConstr) v"

lemma inv2conv_bool[code_abbrev]:"(conv_bool a) = inv (Timed o TLive o map_event boolEVENTConstr) a"
  apply(cases a,simp_all)
  apply(case_tac x2,simp_all)
(*  apply(case_tac x2a,simp_all)
  by (simp add: inv_f_eq) *)
sorry

fun conv_nat ::"M \<Rightarrow> nat event" where
"conv_nat (Timed ( TLive ( EventMsg (natEVENTConstr a)))) = EventMsg a"|
"conv_nat (Timed (TLive Tick)) = Tick"|
"conv_nat  v = inv (Timed o TLive o map_event natEVENTConstr) v"

lemma inv2conv_nat[code_abbrev]:"(conv_nat a) = inv (Timed o TLive o map_event natEVENTConstr) a"
  apply(cases a,simp_all)
  apply(case_tac x2,simp_all)
(*  apply(case_tac x2a,simp_all)
  by (simp add: inv_f_eq) *)
sorry

fun conv_string ::"M \<Rightarrow> string event" where
"conv_string (Timed ( TLive ( EventMsg (stringEVENTConstr a)))) = EventMsg a"|
"conv_string (Timed (TLive Tick)) = Tick"|
"conv_string  v = inv (Timed o TLive o map_event stringEVENTConstr) v"

lemma inv2conv_string[code_abbrev]:"(conv_string a) = inv (Timed o TLive o map_event stringEVENTConstr) a"
  apply(cases a,simp_all)
  apply(case_tac x2,simp_all)
(*  apply(case_tac x2a,simp_all)
  by (simp add: inv_f_eq) *)
sorry

lemma [code_abbrev]:"sbesetter = sbeGen.setter buildSBE"
  by(simp add: sbesetter_def)

lemma sbegeth: assumes "a beOutChannel_rep \<in> range (Timed o TLive o map_event boolEVENTConstr)"
                    and "a natOutChannel_rep \<in> range (Timed o TLive o map_event natEVENTConstr)"
                    and "a sOutChannel_rep \<in> range (Timed o TLive o map_event stringEVENTConstr)"
                        shows "inv (channelsChan (Timed o TLive o map_event boolEVENTConstr) (Timed o TLive o map_event natEVENTConstr) (Timed o TLive o map_event stringEVENTConstr)) a = channelsChan_inv (Timed o TLive o map_event boolEVENTConstr) (Timed o TLive o map_event natEVENTConstr) (Timed o TLive o map_event stringEVENTConstr) a"
  unfolding channelsChan_inv_def
(*
  using assms inv_f_f channelsChan_inv_def channelsChan_surj_helper buildSBE_def build_inj by metis
*)
sorry

lemma sbegeth2 :assumes "\<forall>c. a c \<in> ctype (Rep c)"
  shows"sbegetter (Abs_sbElem (Some a)) = inv buildSBE a"
  by (metis assms(1) Abs_sbElem_inverse SBE.getter_def mem_Collect_eq option.simps(5) sbElem_well.simps(2))

lemma [code]:"sbegetter sbe = (case Rep_sbElem sbe of Some (f::channels \<Rightarrow> M)
\<Rightarrow> ((inv (Timed o TLive o map_event boolEVENTConstr) (the (Rep_sbElem (sbe)) beOutChannel_rep))), ((inv (Timed o TLive o map_event natEVENTConstr) (the (Rep_sbElem (sbe)) natOutChannel_rep))), ((inv (Timed o TLive o map_event stringEVENTConstr) (the (Rep_sbElem (sbe)) sOutChannel_rep))))"
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

definition insbsetter_nc::" (bool event stream \<times> nat event stream \<times> string event stream) \<Rightarrow> channels\<^sup>\<Omega>" where
"insbsetter_nc =  Abs_lsb o buildSB"

lemma[code]:"Rep_lsb(insbsetter_nc a) = buildSB a"
  using insbsetter_nc_def SB.setter.rep_eq SB.setter_rep by auto

lemma[code]:"Rep_cfun(sbsetter) =  insbsetter_nc"
  using insbsetter_nc_def SB.setter.rep_eq sbsetter_def by auto

lemma[code]:"Rep_cfun(sbgetter) = (inv buildSB) o  Rep_lsb"
  by(simp add: SB.getter.rep_eq)

lemma sbgetterh2:"Rep_lsb sb beOutChannel_rep = smap (Timed o TLive o map_event boolEVENTConstr)\<cdot>(fst ((inv buildSB o Rep_lsb) sb))"
(* Doesn't work for cc
  by (metis SB.getter.rep_eq SB.set_get SB.setter_rep buildSB_def channelsChan.simps)
*)
  sorry

lemma sbgetterh3:"Rep_lsb sb natOutChannel_rep = smap (Timed o TLive o map_event natEVENTConstr)\<cdot>(fst (snd ((inv buildSB o Rep_lsb) sb)))"
(* Doesn't work for cc
  by (metis SB.getter.rep_eq SB.set_get SB.setter_rep buildSB_def channelsChan.simps)
*)
  sorry

lemma sbgetterh4:"Rep_lsb sb sOutChannel_rep = smap (Timed o TLive o map_event stringEVENTConstr)\<cdot>(snd (snd ((inv buildSB o Rep_lsb) sb)))"
(* Doesn't work for cc
  by (metis SB.getter.rep_eq SB.set_get SB.setter_rep buildSB_def channelsChan.simps)
*)
  sorry

lemma smap_conv_bool:" smap (inv  (Timed o TLive o map_event boolEVENTConstr))\<cdot>s = smap conv_bool\<cdot>s"
  apply(induction s,simp_all)
  apply(subst inject_scons,simp_all)
  by(simp add: inv2conv_bool comp_def)

lemma smap_conv_nat:" smap (inv  (Timed o TLive o map_event natEVENTConstr))\<cdot>s = smap conv_nat\<cdot>s"
  apply(induction s,simp_all)
  apply(subst inject_scons,simp_all)
  by(simp add: inv2conv_nat comp_def)

lemma smap_conv_string:" smap (inv  (Timed o TLive o map_event stringEVENTConstr))\<cdot>s = smap conv_string\<cdot>s"
  apply(induction s,simp_all)
  apply(subst inject_scons,simp_all)
  by(simp add: inv2conv_string comp_def)


lemma sbgetterh:"sbgetter\<cdot> sb = (
  smap conv_bool\<cdot> (Rep_lsb sb beOutChannel_rep)   ,

  smap conv_nat\<cdot> (Rep_lsb sb natOutChannel_rep)   ,

  smap conv_string\<cdot> (Rep_lsb sb sOutChannel_rep)
 ) "
  apply(simp add: sbgetter_def)
(*
  using SB.getter_def  smapsmap2smap sbgetterh2 sbgetterh3 sbgetterh4
  SB.getter.abs_eq inj_compose inj_tonetimed sbgetter_def boolEVENTConstr_inj natEVENTConstr_inj stringEVENTConstr_inj  smap_inv_eq
  by (metis prod.collapse smap_conv_bool smap_conv_nat smap_conv_string )
*)
  sorry

lemma [code_abbrev]:"(\<lambda>a. (smap conv_bool\<cdot> (Rep_lsb a beOutChannel_rep), smap conv_nat\<cdot> (Rep_lsb a natOutChannel_rep), smap conv_string\<cdot> (Rep_lsb a sOutChannel_rep))) = (\<lambda>a. ((inv buildSB) o  Rep_lsb) a)"
  apply(simp add: buildSB_def channelsChan_inv_def)
  using SB.getter.rep_eq buildSB_def sbgetterh smap_conv_bool smap_conv_nat smap_conv_string
  by auto


end

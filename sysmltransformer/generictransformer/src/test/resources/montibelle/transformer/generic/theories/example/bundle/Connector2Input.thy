theory Connector2Input
  imports
    (* Core *) bundle.MsgWithChan
    (* Gen  *) data_inc.Data_inc
    (* Hwl  *)

begin


default_sort type

declare len_prod_inf_snd[simp del]


typedef channels = "{(CH ''natInChannel_rep'' TTsyn TnatSYNC), (CH ''bInChannel_rep'' TTsyn TboolSYNC), (CH ''sInChannel_rep'' TTsyn TstringSYNC), (CH ''natOutChannel_instantiated_1_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_instantiated_1_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_instantiated_1_rep'' TTsyn TstringSYNC), (CH ''natOutChannel_instantiated_2_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_instantiated_2_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_instantiated_2_rep'' TTsyn TstringSYNC)}"
  by auto

instance channels::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_channels
        typedef_finite_UNIV by fastforce

instantiation channels::somechan
begin
  definition Rep_channels_def: "Rep = Rep_channels"
  definition Abs_channels_def:"Abs = Abs_channels"
  definition ChanDom_channels_def: "chanDom(a::channels myself) = {(CH ''natInChannel_rep'' TTsyn TnatSYNC), (CH ''bInChannel_rep'' TTsyn TboolSYNC), (CH ''sInChannel_rep'' TTsyn TstringSYNC), (CH ''natOutChannel_instantiated_1_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_instantiated_1_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_instantiated_1_rep'' TTsyn TstringSYNC), (CH ''natOutChannel_instantiated_2_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_instantiated_2_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_instantiated_2_rep'' TTsyn TstringSYNC)}"

  lemma rep_range[simp]: "range (Rep::channels \<Rightarrow> channel) = {(CH ''natInChannel_rep'' TTsyn TnatSYNC), (CH ''bInChannel_rep'' TTsyn TboolSYNC), (CH ''sInChannel_rep'' TTsyn TstringSYNC), (CH ''natOutChannel_instantiated_1_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_instantiated_1_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_instantiated_1_rep'' TTsyn TstringSYNC), (CH ''natOutChannel_instantiated_2_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_instantiated_2_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_instantiated_2_rep'' TTsyn TstringSYNC)}"
    apply(subst Rep_channels_def)
    using type_definition.Rep_range type_definition_channels by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_channels_def Rep_channels_def Rep_channels_inverse)
     apply(simp add:ChanDom_channels_def insert_Diff_if)
    by clarsimp
end

theorem channels_chdom[simp]: "chDom TYPE (channels) = {(CH ''natInChannel_rep'' TTsyn TnatSYNC), (CH ''bInChannel_rep'' TTsyn TboolSYNC), (CH ''sInChannel_rep'' TTsyn TstringSYNC), (CH ''natOutChannel_instantiated_1_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_instantiated_1_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_instantiated_1_rep'' TTsyn TstringSYNC), (CH ''natOutChannel_instantiated_2_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_instantiated_2_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_instantiated_2_rep'' TTsyn TstringSYNC)}"
  by (metis ChanDom_channels_def chandom_chdom_eq)

definition natInChannel_rep :: "channels" where
"natInChannel_rep \<equiv> Abs_channels (CH ''natInChannel_rep'' TTsyn TnatSYNC)"

lemma natInChannel_rep_rep [simp, code]: "Rep natInChannel_rep = (CH ''natInChannel_rep'' TTsyn TnatSYNC)"
  unfolding Rep_channels_def natInChannel_rep_def
  by (simp add: Abs_channels_inverse)

lemma natInChannel_abs [simp, code]: "Abs (CH ''natInChannel_rep'' TTsyn TnatSYNC) = natInChannel_rep"
  by (metis abs_rep_id natInChannel_rep_rep)

definition bInChannel_rep :: "channels" where
"bInChannel_rep \<equiv> Abs_channels (CH ''bInChannel_rep'' TTsyn TboolSYNC)"

lemma bInChannel_rep_rep [simp, code]: "Rep bInChannel_rep = (CH ''bInChannel_rep'' TTsyn TboolSYNC)"
  unfolding Rep_channels_def bInChannel_rep_def
  by (simp add: Abs_channels_inverse)

lemma bInChannel_abs [simp, code]: "Abs (CH ''bInChannel_rep'' TTsyn TboolSYNC) = bInChannel_rep"
  by (metis abs_rep_id bInChannel_rep_rep)

definition sInChannel_rep :: "channels" where
"sInChannel_rep \<equiv> Abs_channels (CH ''sInChannel_rep'' TTsyn TstringSYNC)"

lemma sInChannel_rep_rep [simp, code]: "Rep sInChannel_rep = (CH ''sInChannel_rep'' TTsyn TstringSYNC)"
  unfolding Rep_channels_def sInChannel_rep_def
  by (simp add: Abs_channels_inverse)

lemma sInChannel_abs [simp, code]: "Abs (CH ''sInChannel_rep'' TTsyn TstringSYNC) = sInChannel_rep"
  by (metis abs_rep_id sInChannel_rep_rep)

definition natOutChannel_instantiated_1_rep :: "channels" where
"natOutChannel_instantiated_1_rep \<equiv> Abs_channels (CH ''natOutChannel_instantiated_1_rep'' TTsyn TnatSYNC)"

lemma natOutChannel_instantiated_1_rep_rep [simp, code]: "Rep natOutChannel_instantiated_1_rep = (CH ''natOutChannel_instantiated_1_rep'' TTsyn TnatSYNC)"
  unfolding Rep_channels_def natOutChannel_instantiated_1_rep_def
  by (simp add: Abs_channels_inverse)

lemma natOutChannel_instantiated_1_abs [simp, code]: "Abs (CH ''natOutChannel_instantiated_1_rep'' TTsyn TnatSYNC) = natOutChannel_instantiated_1_rep"
  by (metis abs_rep_id natOutChannel_instantiated_1_rep_rep)

definition bOutChannel_instantiated_1_rep :: "channels" where
"bOutChannel_instantiated_1_rep \<equiv> Abs_channels (CH ''bOutChannel_instantiated_1_rep'' TTsyn TboolSYNC)"

lemma bOutChannel_instantiated_1_rep_rep [simp, code]: "Rep bOutChannel_instantiated_1_rep = (CH ''bOutChannel_instantiated_1_rep'' TTsyn TboolSYNC)"
  unfolding Rep_channels_def bOutChannel_instantiated_1_rep_def
  by (simp add: Abs_channels_inverse)

lemma bOutChannel_instantiated_1_abs [simp, code]: "Abs (CH ''bOutChannel_instantiated_1_rep'' TTsyn TboolSYNC) = bOutChannel_instantiated_1_rep"
  by (metis abs_rep_id bOutChannel_instantiated_1_rep_rep)

definition sOutChannel_instantiated_1_rep :: "channels" where
"sOutChannel_instantiated_1_rep \<equiv> Abs_channels (CH ''sOutChannel_instantiated_1_rep'' TTsyn TstringSYNC)"

lemma sOutChannel_instantiated_1_rep_rep [simp, code]: "Rep sOutChannel_instantiated_1_rep = (CH ''sOutChannel_instantiated_1_rep'' TTsyn TstringSYNC)"
  unfolding Rep_channels_def sOutChannel_instantiated_1_rep_def
  by (simp add: Abs_channels_inverse)

lemma sOutChannel_instantiated_1_abs [simp, code]: "Abs (CH ''sOutChannel_instantiated_1_rep'' TTsyn TstringSYNC) = sOutChannel_instantiated_1_rep"
  by (metis abs_rep_id sOutChannel_instantiated_1_rep_rep)

definition natOutChannel_instantiated_2_rep :: "channels" where
"natOutChannel_instantiated_2_rep \<equiv> Abs_channels (CH ''natOutChannel_instantiated_2_rep'' TTsyn TnatSYNC)"

lemma natOutChannel_instantiated_2_rep_rep [simp, code]: "Rep natOutChannel_instantiated_2_rep = (CH ''natOutChannel_instantiated_2_rep'' TTsyn TnatSYNC)"
  unfolding Rep_channels_def natOutChannel_instantiated_2_rep_def
  by (simp add: Abs_channels_inverse)

lemma natOutChannel_instantiated_2_abs [simp, code]: "Abs (CH ''natOutChannel_instantiated_2_rep'' TTsyn TnatSYNC) = natOutChannel_instantiated_2_rep"
  by (metis abs_rep_id natOutChannel_instantiated_2_rep_rep)

definition bOutChannel_instantiated_2_rep :: "channels" where
"bOutChannel_instantiated_2_rep \<equiv> Abs_channels (CH ''bOutChannel_instantiated_2_rep'' TTsyn TboolSYNC)"

lemma bOutChannel_instantiated_2_rep_rep [simp, code]: "Rep bOutChannel_instantiated_2_rep = (CH ''bOutChannel_instantiated_2_rep'' TTsyn TboolSYNC)"
  unfolding Rep_channels_def bOutChannel_instantiated_2_rep_def
  by (simp add: Abs_channels_inverse)

lemma bOutChannel_instantiated_2_abs [simp, code]: "Abs (CH ''bOutChannel_instantiated_2_rep'' TTsyn TboolSYNC) = bOutChannel_instantiated_2_rep"
  by (metis abs_rep_id bOutChannel_instantiated_2_rep_rep)

definition sOutChannel_instantiated_2_rep :: "channels" where
"sOutChannel_instantiated_2_rep \<equiv> Abs_channels (CH ''sOutChannel_instantiated_2_rep'' TTsyn TstringSYNC)"

lemma sOutChannel_instantiated_2_rep_rep [simp, code]: "Rep sOutChannel_instantiated_2_rep = (CH ''sOutChannel_instantiated_2_rep'' TTsyn TstringSYNC)"
  unfolding Rep_channels_def sOutChannel_instantiated_2_rep_def
  by (simp add: Abs_channels_inverse)

lemma sOutChannel_instantiated_2_abs [simp, code]: "Abs (CH ''sOutChannel_instantiated_2_rep'' TTsyn TstringSYNC) = sOutChannel_instantiated_2_rep"
  by (metis abs_rep_id sOutChannel_instantiated_2_rep_rep)

free_constructors channels for natInChannel_rep | bInChannel_rep | sInChannel_rep | natOutChannel_instantiated_1_rep | bOutChannel_instantiated_1_rep | sOutChannel_instantiated_1_rep | natOutChannel_instantiated_2_rep | bOutChannel_instantiated_2_rep | sOutChannel_instantiated_2_rep
  unfolding natInChannel_rep_def bInChannel_rep_def sInChannel_rep_def natOutChannel_instantiated_1_rep_def bOutChannel_instantiated_1_rep_def sOutChannel_instantiated_1_rep_def natOutChannel_instantiated_2_rep_def bOutChannel_instantiated_2_rep_def sOutChannel_instantiated_2_rep_def
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "P natInChannel_rep \<or> P bInChannel_rep \<or> P sInChannel_rep \<or> P natOutChannel_instantiated_1_rep \<or> P bOutChannel_instantiated_1_rep \<or> P sOutChannel_instantiated_1_rep \<or> P natOutChannel_instantiated_2_rep \<or> P bOutChannel_instantiated_2_rep \<or> P sOutChannel_instantiated_2_rep \<Longrightarrow> \<exists>c. P c"
  by auto

instance channels::tschan
  apply(intro_classes)
  by(case_tac c;simp)

instantiation channels::enum
begin
  definition "enum_channels \<equiv> [natInChannel_rep, bInChannel_rep, sInChannel_rep, natOutChannel_instantiated_1_rep, bOutChannel_instantiated_1_rep, sOutChannel_instantiated_1_rep, natOutChannel_instantiated_2_rep, bOutChannel_instantiated_2_rep, sOutChannel_instantiated_2_rep]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end


lift_definition natInChannelConstr :: "nat \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (natInChannel_rep, natSYNCConstr x)"
  by (simp add: well_def)

lift_definition bInChannelConstr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (bInChannel_rep, boolSYNCConstr x)"
  by (simp add: well_def)

lift_definition sInChannelConstr :: "string \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (sInChannel_rep, stringSYNCConstr x)"
  by (simp add: well_def)

lift_definition natOutChannel_instantiated_1Constr :: "nat \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (natOutChannel_instantiated_1_rep, natSYNCConstr x)"
  by (simp add: well_def)

lift_definition bOutChannel_instantiated_1Constr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (bOutChannel_instantiated_1_rep, boolSYNCConstr x)"
  by (simp add: well_def)

lift_definition sOutChannel_instantiated_1Constr :: "string \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (sOutChannel_instantiated_1_rep, stringSYNCConstr x)"
  by (simp add: well_def)

lift_definition natOutChannel_instantiated_2Constr :: "nat \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (natOutChannel_instantiated_2_rep, natSYNCConstr x)"
  by (simp add: well_def)

lift_definition bOutChannel_instantiated_2Constr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (bOutChannel_instantiated_2_rep, boolSYNCConstr x)"
  by (simp add: well_def)

lift_definition sOutChannel_instantiated_2Constr :: "string \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (sOutChannel_instantiated_2_rep, stringSYNCConstr x)"
  by (simp add: well_def)





fun channelsChan::"('boolSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('stringSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv\<times>'boolSYNCConv\<times>'stringSYNCConv\<times>'natSYNCConv\<times>'boolSYNCConv\<times>'stringSYNCConv\<times>'natSYNCConv\<times>'boolSYNCConv\<times>'stringSYNCConv) \<Rightarrow> channels \<Rightarrow> 'M" where
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) natInChannel_rep = natSYNCConv natInChannel_pattern" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) bInChannel_rep = boolSYNCConv bInChannel_pattern" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) sInChannel_rep = stringSYNCConv sInChannel_pattern" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) natOutChannel_instantiated_1_rep = natSYNCConv natOutChannel_pattern_instantiated_1" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) bOutChannel_instantiated_1_rep = boolSYNCConv bOutChannel_pattern_instantiated_1" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) sOutChannel_instantiated_1_rep = stringSYNCConv sOutChannel_pattern_instantiated_1" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) natOutChannel_instantiated_2_rep = natSYNCConv natOutChannel_pattern_instantiated_2" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) bOutChannel_instantiated_2_rep = boolSYNCConv bOutChannel_pattern_instantiated_2" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) sOutChannel_instantiated_2_rep = stringSYNCConv sOutChannel_pattern_instantiated_2"

definition %invisible channelsChan_inv :: "('boolSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('stringSYNCConv \<Rightarrow> 'M) \<Rightarrow> (channels \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv \<times> 'boolSYNCConv \<times> 'stringSYNCConv \<times> 'natSYNCConv \<times> 'boolSYNCConv \<times> 'stringSYNCConv \<times> 'natSYNCConv \<times> 'boolSYNCConv \<times> 'stringSYNCConv)" where
"channelsChan_inv boolSYNCConv natSYNCConv stringSYNCConv bundle = (inv natSYNCConv (bundle natInChannel_rep), inv boolSYNCConv (bundle bInChannel_rep), inv stringSYNCConv (bundle sInChannel_rep), inv natSYNCConv (bundle natOutChannel_instantiated_1_rep), inv boolSYNCConv (bundle bOutChannel_instantiated_1_rep), inv stringSYNCConv (bundle sOutChannel_instantiated_1_rep), inv natSYNCConv (bundle natOutChannel_instantiated_2_rep), inv boolSYNCConv (bundle bOutChannel_instantiated_2_rep), inv stringSYNCConv (bundle sOutChannel_instantiated_2_rep))"

lemma %invisible channelsChan_surj_helper:
  assumes "f natInChannel_rep \<in> range natSYNCConv"
      and "f bInChannel_rep \<in> range boolSYNCConv"
      and "f sInChannel_rep \<in> range stringSYNCConv"
      and "f natOutChannel_instantiated_1_rep \<in> range natSYNCConv"
      and "f bOutChannel_instantiated_1_rep \<in> range boolSYNCConv"
      and "f sOutChannel_instantiated_1_rep \<in> range stringSYNCConv"
      and "f natOutChannel_instantiated_2_rep \<in> range natSYNCConv"
      and "f bOutChannel_instantiated_2_rep \<in> range boolSYNCConv"
      and "f sOutChannel_instantiated_2_rep \<in> range stringSYNCConv"
    shows "channelsChan boolSYNCConv natSYNCConv stringSYNCConv (channelsChan_inv boolSYNCConv natSYNCConv stringSYNCConv f) = f"
  unfolding channelsChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma channelsChan_surj:
  assumes "f natInChannel_rep \<in> range natSYNCConv"
      and "f bInChannel_rep \<in> range boolSYNCConv"
      and "f sInChannel_rep \<in> range stringSYNCConv"
      and "f natOutChannel_instantiated_1_rep \<in> range natSYNCConv"
      and "f bOutChannel_instantiated_1_rep \<in> range boolSYNCConv"
      and "f sOutChannel_instantiated_1_rep \<in> range stringSYNCConv"
      and "f natOutChannel_instantiated_2_rep \<in> range natSYNCConv"
      and "f bOutChannel_instantiated_2_rep \<in> range boolSYNCConv"
      and "f sOutChannel_instantiated_2_rep \<in> range stringSYNCConv"
    shows "f \<in> range (channelsChan boolSYNCConv natSYNCConv stringSYNCConv)"
  apply(subst channelsChan_surj_helper[symmetric, where boolSYNCConv=boolSYNCConv and natSYNCConv=natSYNCConv and stringSYNCConv=stringSYNCConv])
  by(simp_all add: assms)

lemma channelsChan_inj:
  assumes "inj boolSYNCConv"
      and "inj natSYNCConv"
      and "inj stringSYNCConv"
    shows "inj (channelsChan boolSYNCConv natSYNCConv stringSYNCConv)"
  apply (auto simp add: inj_def)
  by (metis assms channelsChan.simps injD)+

definition buildSBE where
"buildSBE \<equiv> channelsChan
    (Timed o Tsyn o map_tsyn boolSYNCConstr)
    (Timed o Tsyn o map_tsyn natSYNCConstr)
    (Timed o Tsyn o map_tsyn stringSYNCConstr)"

declare buildSBE_def [simp]

theorem build_ctype[simp]: "buildSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a)
  by(auto simp add: ctype_def image_iff)

theorem build_inj[simp]: "inj buildSBE"
  by (simp add: channelsChan_inj)

lemma build_range:
  "range (\<lambda>a. buildSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis tsyn.simps(8))+

theorem build_surj[simp]:
  assumes "\<And>c. sbe c \<in> ctype (Rep c)"
    shows "sbe \<in> range buildSBE"
  apply(simp, rule channelsChan_surj)
  apply (metis natInChannel_rep_rep assms natSYNC_ran)
  apply (metis bInChannel_rep_rep assms boolSYNC_ran)
  apply (metis sInChannel_rep_rep assms stringSYNC_ran)
  apply (metis natOutChannel_instantiated_1_rep_rep assms natSYNC_ran)
  apply (metis bOutChannel_instantiated_1_rep_rep assms boolSYNC_ran)
  apply (metis sOutChannel_instantiated_1_rep_rep assms stringSYNC_ran)
  apply (metis natOutChannel_instantiated_2_rep_rep assms natSYNC_ran)
  apply (metis bOutChannel_instantiated_2_rep_rep assms boolSYNC_ran)
  apply (metis sOutChannel_instantiated_2_rep_rep assms stringSYNC_ran)
  done

declare buildSBE_def [simp del]

global_interpretation SBE: sbeGen "buildSBE"
  defines sbesetter = SBE.setter
  and sbegetter = SBE.getter
  and sbesettersb = SBE.setterSB
  by %visible(unfold_locales,simp_all)

definition buildSB where
"buildSB \<equiv> channelsChan
     (Rep_cfun (smap (Timed o Tsyn o map_tsyn boolSYNCConstr)))
     (Rep_cfun (smap (Timed o Tsyn o map_tsyn natSYNCConstr)))
     (Rep_cfun (smap (Timed o Tsyn o map_tsyn stringSYNCConstr)))"

declare buildSB_def [simp]

lemma conc2sconc: "buildSB a1 c \<Zcat> buildSB a2 c = buildSB (a1 \<Zcat>\<Zcat> a2) c"
  apply(cases a1; cases a2; cases c)
    by(auto simp add: conc_prod_apply smap_split)+

theorem buildsb_ctype[simp]: "sValues\<cdot>(buildSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  by (auto simp add: ctype_def smap_sValues image_iff)

theorem buildsb_inj[simp]: "inj buildSB"
  by (auto simp add: channelsChan_inj smap_inj)

theorem buildsb_surj[simp]:
  assumes "lsb_well sb"
    shows "sb \<in> range buildSB"
  apply (simp, rule channelsChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
  using natSYNC_ran apply simp
  using boolSYNC_ran apply simp
  using stringSYNC_ran apply simp
  using natSYNC_ran apply simp
  using boolSYNC_ran apply simp
  using stringSYNC_ran apply simp
  using natSYNC_ran apply simp
  using boolSYNC_ran apply simp
  using stringSYNC_ran apply simp
  done

lemma channelsChan_split: "channelsChan boolSYNCConv natSYNCConv stringSYNCConv x = channelsChan boolSYNCConv natSYNCConv stringSYNCConv ((fst x), (fst (snd x)), (fst (snd (snd x))), (fst (snd (snd (snd x)))), (fst (snd (snd (snd (snd x))))), (fst (snd (snd (snd (snd (snd x)))))), (fst (snd (snd (snd (snd (snd (snd x))))))), (fst (snd (snd (snd (snd (snd (snd (snd x)))))))), (snd (snd (snd (snd (snd (snd (snd (snd x)))))))))"
  by auto

lemma cont_h:
  shows "cont boolSYNCConv \<and> cont natSYNCConv \<and> cont stringSYNCConv \<Longrightarrow>
         cont (\<lambda>x. channelsChan boolSYNCConv natSYNCConv stringSYNCConv x c)"
  apply(cases c, auto)
  apply(subst channelsChan_split, simp only: channelsChan.simps, intro cont2cont; simp)+
  done

lemma cont[cont2cont]:
  shows "cont boolSYNCConv \<and> cont natSYNCConv \<and> cont stringSYNCConv \<Longrightarrow>
         cont (channelsChan boolSYNCConv natSYNCConv stringSYNCConv)"
  by (simp add: cont_h)

lemma [simp]: "cont buildSB"
  by(simp, rule cont, simp)

lemma [simp]:"\<not> x \<sqsubseteq> y \<Longrightarrow> \<not> buildSB x \<sqsubseteq> buildSB y"
  apply(subst fun_below_iff,auto)
  apply(cases x; cases y; auto)
  apply(      solves\<open>(rule_tac x="natInChannel_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="bInChannel_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="sInChannel_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="natOutChannel_instantiated_1_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="bOutChannel_instantiated_1_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="sOutChannel_instantiated_1_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="natOutChannel_instantiated_2_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="bOutChannel_instantiated_2_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="sOutChannel_instantiated_2_rep" in exI,simp)\<close>)+
  done

declare tlen_prod_inf_snd[simp del]

lemma [simp]: "#a \<le> #(buildSB a c)"
  apply(cases c; simp; fail)?
  apply (cases c; cases a; auto?, simp_all?)?
  by (simp_all add: len_prod_minl len_prod_rsmaller tlen_prod_minl tlen_prod_rsmaller)?

lemma [simp]: "\<exists>c. #a = #(buildSB a c)"
  apply ((rule channels_exists, simp); fail|cases a; auto?, simp?)
  apply (rule channels_exists, simp)?
  apply auto?
  apply ((subst len_prod_def2)+)?
  apply ((subst(asm) len_prod_def2)+)?
  apply ((subst tlen_prod_def2)+)?
  apply ((subst(asm) tlen_prod_def2)+)?
  by (smt min_def)?

lemma [simp]: "(#\<^sub>\<surd>a) <= (#\<^sub>\<surd>(buildSB a c))"
  apply (cases c; simp; fail)?
  apply (cases c;cases a; auto?, simp_all?)?
  by (simp_all add: tlen_prod_minl tlen_prod_rsmaller len_prod_minl len_prod_rsmaller)?

lemma [simp]: "\<exists>c. (#\<^sub>\<surd>a) = (#\<^sub>\<surd>(buildSB a c))"
  apply ((rule channels_exists, simp); fail|cases a; auto?, simp?)
  apply (rule channels_exists, simp)?
  apply auto?
  apply ((subst len_prod_def2)+)?
  apply ((subst(asm) len_prod_def2)+)?
  apply ((subst tlen_prod_def2)+)?
  apply ((subst(asm) tlen_prod_def2)+)?
  by (smt min_def)?

declare buildSB_def[simp del] tlen_len_eq[simp del] tlen_prod_inf_snd[simp]


global_interpretation SB: sbtGen "buildSB"
  defines sbsetter = SB.setter
      and sbgetter = SB.getter
  apply(unfold_locales)
        by(simp_all add: lsb_well_def)

lemma getter_fold: "sbGen.getter buildSB = sbgetter"
  by (simp add: sbgetter_def)

lemma setter_sbe2sb: "sbe2sb (SBE.setter(natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2)) = SB.setter\<cdot>(\<up>natInChannel_pattern, \<up>bInChannel_pattern, \<up>sInChannel_pattern, \<up>natOutChannel_pattern_instantiated_1, \<up>bOutChannel_pattern_instantiated_1, \<up>sOutChannel_pattern_instantiated_1, \<up>natOutChannel_pattern_instantiated_2, \<up>bOutChannel_pattern_instantiated_2, \<up>sOutChannel_pattern_instantiated_2)"
  apply(rule sb_eqI2)
  apply(case_tac c, auto)
  by(simp add: buildSBE_def buildSB_def)+

lemma setter_conc2sbconc: "SB.setter\<cdot>(s1 \<Zcat>\<Zcat> s2) = SB.setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> SB.setter\<cdot>s2"
  by(subst SB.getter_conc[symmetric], simp_all add: conc2sconc)

lemma getter_conc2sbconc: "SB.getter\<cdot>sb1 \<Zcat>\<Zcat> SB.getter\<cdot>sb2 = SB.getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  by (metis setter_conc2sbconc SB.get_set SB.set_get)

lemma setter_len[simp]: "#(SB.setter\<cdot>(natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2)) = Min {#natInChannel_pattern, #bInChannel_pattern, #sInChannel_pattern, #natOutChannel_pattern_instantiated_1, #bOutChannel_pattern_instantiated_1, #sOutChannel_pattern_instantiated_1, #natOutChannel_pattern_instantiated_2, #bOutChannel_pattern_instantiated_2, #sOutChannel_pattern_instantiated_2}"
  apply (subst SB.setter_len, simp)
  apply (simp only: len_prod_def2)+
  apply (subst Min2min, simp)+
  by (simp only: Min_singleton)

declare len_prod_inf_snd[simp]


end

theory Instance2Input
  imports
    (* Core *) bundle.MsgWithChan
    (* Gen  *) data_inc.Data_inc
    (* Hwl  *)

begin


default_sort type

declare len_prod_inf_snd[simp del]


typedef channels = "{(CH ''natInChannel_instantiated_2_rep'' TTsyn TnatSYNC), (CH ''bInChannel_instantiated_2_rep'' TTsyn TboolSYNC), (CH ''sInChannel_instantiated_2_rep'' TTsyn TstringSYNC)}"
  by auto

instance channels::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_channels
        typedef_finite_UNIV by fastforce

instantiation channels::somechan
begin
  definition Rep_channels_def: "Rep = Rep_channels"
  definition Abs_channels_def:"Abs = Abs_channels"
  definition ChanDom_channels_def: "chanDom(a::channels myself) = {(CH ''natInChannel_instantiated_2_rep'' TTsyn TnatSYNC), (CH ''bInChannel_instantiated_2_rep'' TTsyn TboolSYNC), (CH ''sInChannel_instantiated_2_rep'' TTsyn TstringSYNC)}"

  lemma rep_range[simp]: "range (Rep::channels \<Rightarrow> channel) = {(CH ''natInChannel_instantiated_2_rep'' TTsyn TnatSYNC), (CH ''bInChannel_instantiated_2_rep'' TTsyn TboolSYNC), (CH ''sInChannel_instantiated_2_rep'' TTsyn TstringSYNC)}"
    apply(subst Rep_channels_def)
    using type_definition.Rep_range type_definition_channels by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_channels_def Rep_channels_def Rep_channels_inverse)
     apply(simp add:ChanDom_channels_def insert_Diff_if)
    by clarsimp
end

theorem channels_chdom[simp]: "chDom TYPE (channels) = {(CH ''natInChannel_instantiated_2_rep'' TTsyn TnatSYNC), (CH ''bInChannel_instantiated_2_rep'' TTsyn TboolSYNC), (CH ''sInChannel_instantiated_2_rep'' TTsyn TstringSYNC)}"
  by (metis ChanDom_channels_def chandom_chdom_eq)

definition natInChannel_instantiated_2_rep :: "channels" where
"natInChannel_instantiated_2_rep \<equiv> Abs_channels (CH ''natInChannel_instantiated_2_rep'' TTsyn TnatSYNC)"

lemma natInChannel_instantiated_2_rep_rep [simp, code]: "Rep natInChannel_instantiated_2_rep = (CH ''natInChannel_instantiated_2_rep'' TTsyn TnatSYNC)"
  unfolding Rep_channels_def natInChannel_instantiated_2_rep_def
  by (simp add: Abs_channels_inverse)

lemma natInChannel_instantiated_2_abs [simp, code]: "Abs (CH ''natInChannel_instantiated_2_rep'' TTsyn TnatSYNC) = natInChannel_instantiated_2_rep"
  by (metis abs_rep_id natInChannel_instantiated_2_rep_rep)

definition bInChannel_instantiated_2_rep :: "channels" where
"bInChannel_instantiated_2_rep \<equiv> Abs_channels (CH ''bInChannel_instantiated_2_rep'' TTsyn TboolSYNC)"

lemma bInChannel_instantiated_2_rep_rep [simp, code]: "Rep bInChannel_instantiated_2_rep = (CH ''bInChannel_instantiated_2_rep'' TTsyn TboolSYNC)"
  unfolding Rep_channels_def bInChannel_instantiated_2_rep_def
  by (simp add: Abs_channels_inverse)

lemma bInChannel_instantiated_2_abs [simp, code]: "Abs (CH ''bInChannel_instantiated_2_rep'' TTsyn TboolSYNC) = bInChannel_instantiated_2_rep"
  by (metis abs_rep_id bInChannel_instantiated_2_rep_rep)

definition sInChannel_instantiated_2_rep :: "channels" where
"sInChannel_instantiated_2_rep \<equiv> Abs_channels (CH ''sInChannel_instantiated_2_rep'' TTsyn TstringSYNC)"

lemma sInChannel_instantiated_2_rep_rep [simp, code]: "Rep sInChannel_instantiated_2_rep = (CH ''sInChannel_instantiated_2_rep'' TTsyn TstringSYNC)"
  unfolding Rep_channels_def sInChannel_instantiated_2_rep_def
  by (simp add: Abs_channels_inverse)

lemma sInChannel_instantiated_2_abs [simp, code]: "Abs (CH ''sInChannel_instantiated_2_rep'' TTsyn TstringSYNC) = sInChannel_instantiated_2_rep"
  by (metis abs_rep_id sInChannel_instantiated_2_rep_rep)

free_constructors channels for natInChannel_instantiated_2_rep | bInChannel_instantiated_2_rep | sInChannel_instantiated_2_rep
  unfolding natInChannel_instantiated_2_rep_def bInChannel_instantiated_2_rep_def sInChannel_instantiated_2_rep_def
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "P natInChannel_instantiated_2_rep \<or> P bInChannel_instantiated_2_rep \<or> P sInChannel_instantiated_2_rep \<Longrightarrow> \<exists>c. P c"
  by auto

instance channels::tschan
  apply(intro_classes)
  by(case_tac c;simp)

instantiation channels::enum
begin
  definition "enum_channels \<equiv> [natInChannel_instantiated_2_rep, bInChannel_instantiated_2_rep, sInChannel_instantiated_2_rep]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end


lift_definition natInChannel_instantiated_2Constr :: "nat \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (natInChannel_instantiated_2_rep, natSYNCConstr x)"
  by (simp add: well_def)

lift_definition bInChannel_instantiated_2Constr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (bInChannel_instantiated_2_rep, boolSYNCConstr x)"
  by (simp add: well_def)

lift_definition sInChannel_instantiated_2Constr :: "string \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (sInChannel_instantiated_2_rep, stringSYNCConstr x)"
  by (simp add: well_def)





fun channelsChan::"('boolSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('stringSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv\<times>'boolSYNCConv\<times>'stringSYNCConv) \<Rightarrow> channels \<Rightarrow> 'M" where
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2) natInChannel_instantiated_2_rep = natSYNCConv natInChannel_pattern_instantiated_2" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2) bInChannel_instantiated_2_rep = boolSYNCConv bInChannel_pattern_instantiated_2" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2) sInChannel_instantiated_2_rep = stringSYNCConv sInChannel_pattern_instantiated_2"

definition %invisible channelsChan_inv :: "('boolSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('stringSYNCConv \<Rightarrow> 'M) \<Rightarrow> (channels \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv \<times> 'boolSYNCConv \<times> 'stringSYNCConv)" where
"channelsChan_inv boolSYNCConv natSYNCConv stringSYNCConv bundle = (inv natSYNCConv (bundle natInChannel_instantiated_2_rep), inv boolSYNCConv (bundle bInChannel_instantiated_2_rep), inv stringSYNCConv (bundle sInChannel_instantiated_2_rep))"

lemma %invisible channelsChan_surj_helper:
  assumes "f natInChannel_instantiated_2_rep \<in> range natSYNCConv"
      and "f bInChannel_instantiated_2_rep \<in> range boolSYNCConv"
      and "f sInChannel_instantiated_2_rep \<in> range stringSYNCConv"
    shows "channelsChan boolSYNCConv natSYNCConv stringSYNCConv (channelsChan_inv boolSYNCConv natSYNCConv stringSYNCConv f) = f"
  unfolding channelsChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma channelsChan_surj:
  assumes "f natInChannel_instantiated_2_rep \<in> range natSYNCConv"
      and "f bInChannel_instantiated_2_rep \<in> range boolSYNCConv"
      and "f sInChannel_instantiated_2_rep \<in> range stringSYNCConv"
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
  apply (metis natInChannel_instantiated_2_rep_rep assms natSYNC_ran)
  apply (metis bInChannel_instantiated_2_rep_rep assms boolSYNC_ran)
  apply (metis sInChannel_instantiated_2_rep_rep assms stringSYNC_ran)
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
  done

lemma channelsChan_split: "channelsChan boolSYNCConv natSYNCConv stringSYNCConv x = channelsChan boolSYNCConv natSYNCConv stringSYNCConv ((fst x), (fst (snd x)), (snd (snd x)))"
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
  apply(      solves\<open>(rule_tac x="natInChannel_instantiated_2_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="bInChannel_instantiated_2_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="sInChannel_instantiated_2_rep" in exI,simp)\<close>)+
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

lemma setter_sbe2sb: "sbe2sb (SBE.setter(natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2)) = SB.setter\<cdot>(\<up>natInChannel_pattern_instantiated_2, \<up>bInChannel_pattern_instantiated_2, \<up>sInChannel_pattern_instantiated_2)"
  apply(rule sb_eqI2)
  apply(case_tac c, auto)
  by(simp add: buildSBE_def buildSB_def)+

lemma setter_conc2sbconc: "SB.setter\<cdot>(s1 \<Zcat>\<Zcat> s2) = SB.setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> SB.setter\<cdot>s2"
  by(subst SB.getter_conc[symmetric], simp_all add: conc2sconc)

lemma getter_conc2sbconc: "SB.getter\<cdot>sb1 \<Zcat>\<Zcat> SB.getter\<cdot>sb2 = SB.getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  by (metis setter_conc2sbconc SB.get_set SB.set_get)

lemma setter_len[simp]: "#(SB.setter\<cdot>(natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2)) = Min {#natInChannel_pattern_instantiated_2, #bInChannel_pattern_instantiated_2, #sInChannel_pattern_instantiated_2}"
  apply (subst SB.setter_len, simp)
  apply (simp only: len_prod_def2)+
  apply (subst Min2min, simp)+
  by (simp only: Min_singleton)

declare len_prod_inf_snd[simp]


end

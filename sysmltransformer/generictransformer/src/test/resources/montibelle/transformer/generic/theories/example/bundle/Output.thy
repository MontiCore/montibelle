theory Output
  imports
    (* Core *) bundle.MsgWithChan
    (* Gen  *) data_inc.Data_inc
    (* Hwl  *)

begin


default_sort type

declare len_prod_inf_snd[simp del]


typedef channels = "{(CH ''natOutChannel_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_rep'' TTsyn TstringSYNC)}"
  by auto

instance channels::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_channels
        typedef_finite_UNIV by fastforce

instantiation channels::somechan
begin
  definition Rep_channels_def: "Rep = Rep_channels"
  definition Abs_channels_def:"Abs = Abs_channels"
  definition ChanDom_channels_def: "chanDom(a::channels myself) = {(CH ''natOutChannel_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_rep'' TTsyn TstringSYNC)}"

  lemma rep_range[simp]: "range (Rep::channels \<Rightarrow> channel) = {(CH ''natOutChannel_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_rep'' TTsyn TstringSYNC)}"
    apply(subst Rep_channels_def)
    using type_definition.Rep_range type_definition_channels by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_channels_def Rep_channels_def Rep_channels_inverse)
     apply(simp add:ChanDom_channels_def insert_Diff_if)
    by clarsimp
end

theorem channels_chdom[simp]: "chDom TYPE (channels) = {(CH ''natOutChannel_rep'' TTsyn TnatSYNC), (CH ''bOutChannel_rep'' TTsyn TboolSYNC), (CH ''sOutChannel_rep'' TTsyn TstringSYNC)}"
  by (metis ChanDom_channels_def chandom_chdom_eq)

definition natOutChannel_rep :: "channels" where
"natOutChannel_rep \<equiv> Abs_channels (CH ''natOutChannel_rep'' TTsyn TnatSYNC)"

lemma natOutChannel_rep_rep [simp, code]: "Rep natOutChannel_rep = (CH ''natOutChannel_rep'' TTsyn TnatSYNC)"
  unfolding Rep_channels_def natOutChannel_rep_def
  by (simp add: Abs_channels_inverse)

lemma natOutChannel_abs [simp, code]: "Abs (CH ''natOutChannel_rep'' TTsyn TnatSYNC) = natOutChannel_rep"
  by (metis abs_rep_id natOutChannel_rep_rep)

definition bOutChannel_rep :: "channels" where
"bOutChannel_rep \<equiv> Abs_channels (CH ''bOutChannel_rep'' TTsyn TboolSYNC)"

lemma bOutChannel_rep_rep [simp, code]: "Rep bOutChannel_rep = (CH ''bOutChannel_rep'' TTsyn TboolSYNC)"
  unfolding Rep_channels_def bOutChannel_rep_def
  by (simp add: Abs_channels_inverse)

lemma bOutChannel_abs [simp, code]: "Abs (CH ''bOutChannel_rep'' TTsyn TboolSYNC) = bOutChannel_rep"
  by (metis abs_rep_id bOutChannel_rep_rep)

definition sOutChannel_rep :: "channels" where
"sOutChannel_rep \<equiv> Abs_channels (CH ''sOutChannel_rep'' TTsyn TstringSYNC)"

lemma sOutChannel_rep_rep [simp, code]: "Rep sOutChannel_rep = (CH ''sOutChannel_rep'' TTsyn TstringSYNC)"
  unfolding Rep_channels_def sOutChannel_rep_def
  by (simp add: Abs_channels_inverse)

lemma sOutChannel_abs [simp, code]: "Abs (CH ''sOutChannel_rep'' TTsyn TstringSYNC) = sOutChannel_rep"
  by (metis abs_rep_id sOutChannel_rep_rep)

free_constructors channels for natOutChannel_rep | bOutChannel_rep | sOutChannel_rep
  unfolding natOutChannel_rep_def bOutChannel_rep_def sOutChannel_rep_def
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "P natOutChannel_rep \<or> P bOutChannel_rep \<or> P sOutChannel_rep \<Longrightarrow> \<exists>c. P c"
  by auto

instance channels::tschan
  apply(intro_classes)
  by(case_tac c;simp)

instantiation channels::enum
begin
  definition "enum_channels \<equiv> [natOutChannel_rep, bOutChannel_rep, sOutChannel_rep]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end


lift_definition natOutChannelConstr :: "nat \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (natOutChannel_rep, natSYNCConstr x)"
  by (simp add: well_def)

lift_definition bOutChannelConstr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (bOutChannel_rep, boolSYNCConstr x)"
  by (simp add: well_def)

lift_definition sOutChannelConstr :: "string \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (sOutChannel_rep, stringSYNCConstr x)"
  by (simp add: well_def)





fun channelsChan::"('boolSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('stringSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv\<times>'boolSYNCConv\<times>'stringSYNCConv) \<Rightarrow> channels \<Rightarrow> 'M" where
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) natOutChannel_rep = natSYNCConv natOutChannel_pattern" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) bOutChannel_rep = boolSYNCConv bOutChannel_pattern" |
"channelsChan boolSYNCConv natSYNCConv stringSYNCConv (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern) sOutChannel_rep = stringSYNCConv sOutChannel_pattern"

definition %invisible channelsChan_inv :: "('boolSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv \<Rightarrow> 'M) \<Rightarrow> ('stringSYNCConv \<Rightarrow> 'M) \<Rightarrow> (channels \<Rightarrow> 'M) \<Rightarrow> ('natSYNCConv \<times> 'boolSYNCConv \<times> 'stringSYNCConv)" where
"channelsChan_inv boolSYNCConv natSYNCConv stringSYNCConv bundle = (inv natSYNCConv (bundle natOutChannel_rep), inv boolSYNCConv (bundle bOutChannel_rep), inv stringSYNCConv (bundle sOutChannel_rep))"

lemma %invisible channelsChan_surj_helper:
  assumes "f natOutChannel_rep \<in> range natSYNCConv"
      and "f bOutChannel_rep \<in> range boolSYNCConv"
      and "f sOutChannel_rep \<in> range stringSYNCConv"
    shows "channelsChan boolSYNCConv natSYNCConv stringSYNCConv (channelsChan_inv boolSYNCConv natSYNCConv stringSYNCConv f) = f"
  unfolding channelsChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma channelsChan_surj:
  assumes "f natOutChannel_rep \<in> range natSYNCConv"
      and "f bOutChannel_rep \<in> range boolSYNCConv"
      and "f sOutChannel_rep \<in> range stringSYNCConv"
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
  apply (metis natOutChannel_rep_rep assms natSYNC_ran)
  apply (metis bOutChannel_rep_rep assms boolSYNC_ran)
  apply (metis sOutChannel_rep_rep assms stringSYNC_ran)
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
  apply(      solves\<open>(rule_tac x="natOutChannel_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="bOutChannel_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="sOutChannel_rep" in exI,simp)\<close>)+
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

lemma setter_sbe2sb: "sbe2sb (SBE.setter(natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)) = SB.setter\<cdot>(\<up>natOutChannel_pattern, \<up>bOutChannel_pattern, \<up>sOutChannel_pattern)"
  apply(rule sb_eqI2)
  apply(case_tac c, auto)
  by(simp add: buildSBE_def buildSB_def)+

lemma setter_conc2sbconc: "SB.setter\<cdot>(s1 \<Zcat>\<Zcat> s2) = SB.setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> SB.setter\<cdot>s2"
  by(subst SB.getter_conc[symmetric], simp_all add: conc2sconc)

lemma getter_conc2sbconc: "SB.getter\<cdot>sb1 \<Zcat>\<Zcat> SB.getter\<cdot>sb2 = SB.getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  by (metis setter_conc2sbconc SB.get_set SB.set_get)

lemma setter_len[simp]: "#(SB.setter\<cdot>(natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)) = Min {#natOutChannel_pattern, #bOutChannel_pattern, #sOutChannel_pattern}"
  apply (subst SB.setter_len, simp)
  apply (simp only: len_prod_def2)+
  apply (subst Min2min, simp)+
  by (simp only: Min_singleton)

declare len_prod_inf_snd[simp]


end

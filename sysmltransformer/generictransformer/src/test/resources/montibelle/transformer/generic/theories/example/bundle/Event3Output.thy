theory Event3Output
  imports
    (* Core *) bundle.MsgWithChan
    (* Gen  *) data_inc.Data_inc
    (* Hwl  *)

begin


default_sort type

declare len_prod_inf_snd[simp del]


typedef channels = "{(CH ''beOutChannel_rep'' TTLive TboolEVENT), (CH ''natOutChannel_rep'' TTLive TnatEVENT), (CH ''sOutChannel_rep'' TTLive TstringEVENT)}"
  by auto

instance channels::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_channels
        typedef_finite_UNIV by fastforce

instantiation channels::somechan
begin
  definition Rep_channels_def: "Rep = Rep_channels"
  definition Abs_channels_def:"Abs = Abs_channels"
  definition ChanDom_channels_def: "chanDom(a::channels myself) = {(CH ''beOutChannel_rep'' TTLive TboolEVENT), (CH ''natOutChannel_rep'' TTLive TnatEVENT), (CH ''sOutChannel_rep'' TTLive TstringEVENT)}"

  lemma rep_range[simp]: "range (Rep::channels \<Rightarrow> channel) = {(CH ''beOutChannel_rep'' TTLive TboolEVENT), (CH ''natOutChannel_rep'' TTLive TnatEVENT), (CH ''sOutChannel_rep'' TTLive TstringEVENT)}"
    apply(subst Rep_channels_def)
    using type_definition.Rep_range type_definition_channels by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_channels_def Rep_channels_def Rep_channels_inverse)
     apply(simp add:ChanDom_channels_def insert_Diff_if)
    by clarsimp
end

theorem channels_chdom[simp]: "chDom TYPE (channels) = {(CH ''beOutChannel_rep'' TTLive TboolEVENT), (CH ''natOutChannel_rep'' TTLive TnatEVENT), (CH ''sOutChannel_rep'' TTLive TstringEVENT)}"
  by (metis ChanDom_channels_def chandom_chdom_eq)

definition beOutChannel_rep :: "channels" where
"beOutChannel_rep \<equiv> Abs_channels (CH ''beOutChannel_rep'' TTLive TboolEVENT)"

lemma beOutChannel_rep_rep [simp, code]: "Rep beOutChannel_rep = (CH ''beOutChannel_rep'' TTLive TboolEVENT)"
  unfolding Rep_channels_def beOutChannel_rep_def
  by (simp add: Abs_channels_inverse)

lemma beOutChannel_abs [simp, code]: "Abs (CH ''beOutChannel_rep'' TTLive TboolEVENT) = beOutChannel_rep"
  by (metis abs_rep_id beOutChannel_rep_rep)

definition natOutChannel_rep :: "channels" where
"natOutChannel_rep \<equiv> Abs_channels (CH ''natOutChannel_rep'' TTLive TnatEVENT)"

lemma natOutChannel_rep_rep [simp, code]: "Rep natOutChannel_rep = (CH ''natOutChannel_rep'' TTLive TnatEVENT)"
  unfolding Rep_channels_def natOutChannel_rep_def
  by (simp add: Abs_channels_inverse)

lemma natOutChannel_abs [simp, code]: "Abs (CH ''natOutChannel_rep'' TTLive TnatEVENT) = natOutChannel_rep"
  by (metis abs_rep_id natOutChannel_rep_rep)

definition sOutChannel_rep :: "channels" where
"sOutChannel_rep \<equiv> Abs_channels (CH ''sOutChannel_rep'' TTLive TstringEVENT)"

lemma sOutChannel_rep_rep [simp, code]: "Rep sOutChannel_rep = (CH ''sOutChannel_rep'' TTLive TstringEVENT)"
  unfolding Rep_channels_def sOutChannel_rep_def
  by (simp add: Abs_channels_inverse)

lemma sOutChannel_abs [simp, code]: "Abs (CH ''sOutChannel_rep'' TTLive TstringEVENT) = sOutChannel_rep"
  by (metis abs_rep_id sOutChannel_rep_rep)

free_constructors channels for beOutChannel_rep | natOutChannel_rep | sOutChannel_rep
  unfolding beOutChannel_rep_def natOutChannel_rep_def sOutChannel_rep_def
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "P beOutChannel_rep \<or> P natOutChannel_rep \<or> P sOutChannel_rep \<Longrightarrow> \<exists>c. P c"
  by auto

instance channels::echan
  apply(intro_classes)
  by(case_tac c;simp)

instantiation channels::enum
begin
  definition "enum_channels \<equiv> [beOutChannel_rep, natOutChannel_rep, sOutChannel_rep]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end


lift_definition beOutChannelConstr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (beOutChannel_rep, boolEVENTConstr x)"
  by (simp add: well_def)

lift_definition natOutChannelConstr :: "nat \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (natOutChannel_rep, natEVENTConstr x)"
  by (simp add: well_def)

lift_definition sOutChannelConstr :: "string \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (sOutChannel_rep, stringEVENTConstr x)"
  by (simp add: well_def)





fun channelsChan::"('boolEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('natEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('stringEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('boolEVENTConv\<times>'natEVENTConv\<times>'stringEVENTConv) \<Rightarrow> channels \<Rightarrow> 'M" where
"channelsChan boolEVENTConv natEVENTConv stringEVENTConv (beOutChannel_pattern, natOutChannel_pattern, sOutChannel_pattern) beOutChannel_rep = boolEVENTConv beOutChannel_pattern" |
"channelsChan boolEVENTConv natEVENTConv stringEVENTConv (beOutChannel_pattern, natOutChannel_pattern, sOutChannel_pattern) natOutChannel_rep = natEVENTConv natOutChannel_pattern" |
"channelsChan boolEVENTConv natEVENTConv stringEVENTConv (beOutChannel_pattern, natOutChannel_pattern, sOutChannel_pattern) sOutChannel_rep = stringEVENTConv sOutChannel_pattern"

definition %invisible channelsChan_inv :: "('boolEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('natEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('stringEVENTConv \<Rightarrow> 'M) \<Rightarrow> (channels \<Rightarrow> 'M) \<Rightarrow> ('boolEVENTConv \<times> 'natEVENTConv \<times> 'stringEVENTConv)" where
"channelsChan_inv boolEVENTConv natEVENTConv stringEVENTConv bundle = (inv boolEVENTConv (bundle beOutChannel_rep), inv natEVENTConv (bundle natOutChannel_rep), inv stringEVENTConv (bundle sOutChannel_rep))"

lemma %invisible channelsChan_surj_helper:
  assumes "f beOutChannel_rep \<in> range boolEVENTConv"
      and "f natOutChannel_rep \<in> range natEVENTConv"
      and "f sOutChannel_rep \<in> range stringEVENTConv"
    shows "channelsChan boolEVENTConv natEVENTConv stringEVENTConv (channelsChan_inv boolEVENTConv natEVENTConv stringEVENTConv f) = f"
  unfolding channelsChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma channelsChan_surj:
  assumes "f beOutChannel_rep \<in> range boolEVENTConv"
      and "f natOutChannel_rep \<in> range natEVENTConv"
      and "f sOutChannel_rep \<in> range stringEVENTConv"
    shows "f \<in> range (channelsChan boolEVENTConv natEVENTConv stringEVENTConv)"
  apply(subst channelsChan_surj_helper[symmetric, where boolEVENTConv=boolEVENTConv and natEVENTConv=natEVENTConv and stringEVENTConv=stringEVENTConv])
  by(simp_all add: assms)

lemma channelsChan_inj:
  assumes "inj boolEVENTConv"
      and "inj natEVENTConv"
      and "inj stringEVENTConv"
    shows "inj (channelsChan boolEVENTConv natEVENTConv stringEVENTConv)"
  apply (auto simp add: inj_def)
  by (metis assms channelsChan.simps injD)+

definition buildSBE where
"buildSBE \<equiv> channelsChan
    (Timed o TLive o map_event boolEVENTConstr)
    (Timed o TLive o map_event natEVENTConstr)
    (Timed o TLive o map_event stringEVENTConstr)"

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
  by (metis event.simps(8))+

theorem build_surj[simp]:
  assumes "\<And>c. sbe c \<in> ctype (Rep c)"
    shows "sbe \<in> range buildSBE"
  apply(simp, rule channelsChan_surj)
  apply (metis beOutChannel_rep_rep assms boolEVENT_ran)
  apply (metis natOutChannel_rep_rep assms natEVENT_ran)
  apply (metis sOutChannel_rep_rep assms stringEVENT_ran)
  done

declare buildSBE_def [simp del]

global_interpretation SBE: sbeGen "buildSBE"
  defines sbesetter = SBE.setter
  and sbegetter = SBE.getter
  and sbesettersb = SBE.setterSB
  by %visible(unfold_locales,simp_all)

definition buildSB where
"buildSB \<equiv> channelsChan
     (Rep_cfun (smap (Timed o TLive o map_event boolEVENTConstr)))
     (Rep_cfun (smap (Timed o TLive o map_event natEVENTConstr)))
     (Rep_cfun (smap (Timed o TLive o map_event stringEVENTConstr)))"

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
  using boolEVENT_ran apply simp
  using natEVENT_ran apply simp
  using stringEVENT_ran apply simp
  done

lemma channelsChan_split: "channelsChan boolEVENTConv natEVENTConv stringEVENTConv x = channelsChan boolEVENTConv natEVENTConv stringEVENTConv ((fst x), (fst (snd x)), (snd (snd x)))"
  by auto

lemma cont_h:
  shows "cont boolEVENTConv \<and> cont natEVENTConv \<and> cont stringEVENTConv \<Longrightarrow>
         cont (\<lambda>x. channelsChan boolEVENTConv natEVENTConv stringEVENTConv x c)"
  apply(cases c, auto)
  apply(subst channelsChan_split, simp only: channelsChan.simps, intro cont2cont; simp)+
  done

lemma cont[cont2cont]:
  shows "cont boolEVENTConv \<and> cont natEVENTConv \<and> cont stringEVENTConv \<Longrightarrow>
         cont (channelsChan boolEVENTConv natEVENTConv stringEVENTConv)"
  by (simp add: cont_h)

lemma [simp]: "cont buildSB"
  by(simp, rule cont, simp)

lemma [simp]:"\<not> x \<sqsubseteq> y \<Longrightarrow> \<not> buildSB x \<sqsubseteq> buildSB y"
  apply(subst fun_below_iff,auto)
  apply(cases x; cases y; auto)
  apply(      solves\<open>(rule_tac x="beOutChannel_rep" in exI,simp)\<close> |
          solves\<open>(rule_tac x="natOutChannel_rep" in exI,simp)\<close> |
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

lemma setter_sbe2sb: "sbe2sb (SBE.setter(beOutChannel_pattern, natOutChannel_pattern, sOutChannel_pattern)) = SB.setter\<cdot>(\<up>beOutChannel_pattern, \<up>natOutChannel_pattern, \<up>sOutChannel_pattern)"
  apply(rule sb_eqI2)
  apply(case_tac c, auto)
  by(simp add: buildSBE_def buildSB_def)+

lemma setter_conc2sbconc: "SB.setter\<cdot>(s1 \<Zcat>\<Zcat> s2) = SB.setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> SB.setter\<cdot>s2"
  by(subst SB.getter_conc[symmetric], simp_all add: conc2sconc)

lemma getter_conc2sbconc: "SB.getter\<cdot>sb1 \<Zcat>\<Zcat> SB.getter\<cdot>sb2 = SB.getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  by (metis setter_conc2sbconc SB.get_set SB.set_get)

lemma setter_len[simp]: "#(SB.setter\<cdot>(beOutChannel_pattern, natOutChannel_pattern, sOutChannel_pattern)) = Min {#beOutChannel_pattern, #natOutChannel_pattern, #sOutChannel_pattern}"
  apply (subst SB.setter_len, simp)
  apply (simp only: len_prod_def2)+
  apply (subst Min2min, simp)+
  by (simp only: Min_singleton)

declare len_prod_inf_snd[simp]


end

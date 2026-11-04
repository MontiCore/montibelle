theory def_TelecommandAndTelemetry_HLR_router_Output
  imports
    (* Core *) bundle.MsgWithChan
    (* Gen  *) data_inc.Data_inc
    (* Hwl  *)

begin


default_sort type

declare len_prod_inf_snd[simp del]


typedef channels = "{(CH ''channel_router_b1Out_data'' TTLive TPacketEVENT), (CH ''channel_router_b2Out_data'' TTLive TPacketEVENT), (CH ''channel_router_cocaOut_data'' TTLive TPacketEVENT), (CH ''channel_router_dfpOut_data'' TTLive TPacketEVENT), (CH ''channel_router_maniacOut_data'' TTLive TPacketEVENT), (CH ''channel_router_mirmisOut_data'' TTLive TPacketEVENT)}"
  by auto

instance channels::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_channels
        typedef_finite_UNIV by fastforce

instantiation channels::somechan
begin
  definition Rep_channels_def: "Rep = Rep_channels"
  definition Abs_channels_def:"Abs = Abs_channels"
  definition ChanDom_channels_def: "chanDom(a::channels myself) = {(CH ''channel_router_b1Out_data'' TTLive TPacketEVENT), (CH ''channel_router_b2Out_data'' TTLive TPacketEVENT), (CH ''channel_router_cocaOut_data'' TTLive TPacketEVENT), (CH ''channel_router_dfpOut_data'' TTLive TPacketEVENT), (CH ''channel_router_maniacOut_data'' TTLive TPacketEVENT), (CH ''channel_router_mirmisOut_data'' TTLive TPacketEVENT)}"

  lemma rep_range[simp]: "range (Rep::channels \<Rightarrow> channel) = {(CH ''channel_router_b1Out_data'' TTLive TPacketEVENT), (CH ''channel_router_b2Out_data'' TTLive TPacketEVENT), (CH ''channel_router_cocaOut_data'' TTLive TPacketEVENT), (CH ''channel_router_dfpOut_data'' TTLive TPacketEVENT), (CH ''channel_router_maniacOut_data'' TTLive TPacketEVENT), (CH ''channel_router_mirmisOut_data'' TTLive TPacketEVENT)}"
    apply(subst Rep_channels_def)
    using type_definition.Rep_range type_definition_channels by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_channels_def Rep_channels_def Rep_channels_inverse)
     apply(simp add:ChanDom_channels_def insert_Diff_if)
    by clarsimp
end

theorem channels_chdom[simp]: "chDom TYPE (channels) = {(CH ''channel_router_b1Out_data'' TTLive TPacketEVENT), (CH ''channel_router_b2Out_data'' TTLive TPacketEVENT), (CH ''channel_router_cocaOut_data'' TTLive TPacketEVENT), (CH ''channel_router_dfpOut_data'' TTLive TPacketEVENT), (CH ''channel_router_maniacOut_data'' TTLive TPacketEVENT), (CH ''channel_router_mirmisOut_data'' TTLive TPacketEVENT)}"
  by (metis ChanDom_channels_def chandom_chdom_eq)

definition channel_router_b1Out_data :: "channels" where
"channel_router_b1Out_data \<equiv> Abs_channels (CH ''channel_router_b1Out_data'' TTLive TPacketEVENT)"

lemma channel_router_b1Out_data_rep [simp, code]: "Rep channel_router_b1Out_data = (CH ''channel_router_b1Out_data'' TTLive TPacketEVENT)"
  unfolding Rep_channels_def channel_router_b1Out_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_TelecommandAndTelemetry_HLR_router_b1Out_data_abs [simp, code]: "Abs (CH ''channel_router_b1Out_data'' TTLive TPacketEVENT) = channel_router_b1Out_data"
  by (metis abs_rep_id channel_router_b1Out_data_rep)

definition channel_router_b2Out_data :: "channels" where
"channel_router_b2Out_data \<equiv> Abs_channels (CH ''channel_router_b2Out_data'' TTLive TPacketEVENT)"

lemma channel_router_b2Out_data_rep [simp, code]: "Rep channel_router_b2Out_data = (CH ''channel_router_b2Out_data'' TTLive TPacketEVENT)"
  unfolding Rep_channels_def channel_router_b2Out_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_TelecommandAndTelemetry_HLR_router_b2Out_data_abs [simp, code]: "Abs (CH ''channel_router_b2Out_data'' TTLive TPacketEVENT) = channel_router_b2Out_data"
  by (metis abs_rep_id channel_router_b2Out_data_rep)

definition channel_router_cocaOut_data :: "channels" where
"channel_router_cocaOut_data \<equiv> Abs_channels (CH ''channel_router_cocaOut_data'' TTLive TPacketEVENT)"

lemma channel_router_cocaOut_data_rep [simp, code]: "Rep channel_router_cocaOut_data = (CH ''channel_router_cocaOut_data'' TTLive TPacketEVENT)"
  unfolding Rep_channels_def channel_router_cocaOut_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_TelecommandAndTelemetry_HLR_router_cocaOut_data_abs [simp, code]: "Abs (CH ''channel_router_cocaOut_data'' TTLive TPacketEVENT) = channel_router_cocaOut_data"
  by (metis abs_rep_id channel_router_cocaOut_data_rep)

definition channel_router_dfpOut_data :: "channels" where
"channel_router_dfpOut_data \<equiv> Abs_channels (CH ''channel_router_dfpOut_data'' TTLive TPacketEVENT)"

lemma channel_router_dfpOut_data_rep [simp, code]: "Rep channel_router_dfpOut_data = (CH ''channel_router_dfpOut_data'' TTLive TPacketEVENT)"
  unfolding Rep_channels_def channel_router_dfpOut_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_TelecommandAndTelemetry_HLR_router_dfpOut_data_abs [simp, code]: "Abs (CH ''channel_router_dfpOut_data'' TTLive TPacketEVENT) = channel_router_dfpOut_data"
  by (metis abs_rep_id channel_router_dfpOut_data_rep)

definition channel_router_maniacOut_data :: "channels" where
"channel_router_maniacOut_data \<equiv> Abs_channels (CH ''channel_router_maniacOut_data'' TTLive TPacketEVENT)"

lemma channel_router_maniacOut_data_rep [simp, code]: "Rep channel_router_maniacOut_data = (CH ''channel_router_maniacOut_data'' TTLive TPacketEVENT)"
  unfolding Rep_channels_def channel_router_maniacOut_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_TelecommandAndTelemetry_HLR_router_maniacOut_data_abs [simp, code]: "Abs (CH ''channel_router_maniacOut_data'' TTLive TPacketEVENT) = channel_router_maniacOut_data"
  by (metis abs_rep_id channel_router_maniacOut_data_rep)

definition channel_router_mirmisOut_data :: "channels" where
"channel_router_mirmisOut_data \<equiv> Abs_channels (CH ''channel_router_mirmisOut_data'' TTLive TPacketEVENT)"

lemma channel_router_mirmisOut_data_rep [simp, code]: "Rep channel_router_mirmisOut_data = (CH ''channel_router_mirmisOut_data'' TTLive TPacketEVENT)"
  unfolding Rep_channels_def channel_router_mirmisOut_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_TelecommandAndTelemetry_HLR_router_mirmisOut_data_abs [simp, code]: "Abs (CH ''channel_router_mirmisOut_data'' TTLive TPacketEVENT) = channel_router_mirmisOut_data"
  by (metis abs_rep_id channel_router_mirmisOut_data_rep)

free_constructors channels for channel_router_b1Out_data | channel_router_b2Out_data | channel_router_cocaOut_data | channel_router_dfpOut_data | channel_router_maniacOut_data | channel_router_mirmisOut_data
  unfolding channel_router_b1Out_data_def channel_router_b2Out_data_def channel_router_cocaOut_data_def channel_router_dfpOut_data_def channel_router_maniacOut_data_def channel_router_mirmisOut_data_def
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "P channel_router_b1Out_data \<or> P channel_router_b2Out_data \<or> P channel_router_cocaOut_data \<or> P channel_router_dfpOut_data \<or> P channel_router_maniacOut_data \<or> P channel_router_mirmisOut_data \<Longrightarrow> \<exists>c. P c"
  by auto

instance channels::echan
  apply(intro_classes)
  by(case_tac c;simp)

instantiation channels::enum
begin
  definition "enum_channels \<equiv> [channel_router_b1Out_data, channel_router_b2Out_data, channel_router_cocaOut_data, channel_router_dfpOut_data, channel_router_maniacOut_data, channel_router_mirmisOut_data]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end


lift_definition channel_TelecommandAndTelemetry_HLR_router_b1Out_dataConstr :: "Packet \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_router_b1Out_data, PacketEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_TelecommandAndTelemetry_HLR_router_b2Out_dataConstr :: "Packet \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_router_b2Out_data, PacketEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_TelecommandAndTelemetry_HLR_router_cocaOut_dataConstr :: "Packet \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_router_cocaOut_data, PacketEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_TelecommandAndTelemetry_HLR_router_dfpOut_dataConstr :: "Packet \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_router_dfpOut_data, PacketEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_TelecommandAndTelemetry_HLR_router_maniacOut_dataConstr :: "Packet \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_router_maniacOut_data, PacketEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_TelecommandAndTelemetry_HLR_router_mirmisOut_dataConstr :: "Packet \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_router_mirmisOut_data, PacketEVENTConstr x)"
  by (simp add: well_def)





fun channelsChan::"('PacketEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('PacketEVENTConv\<times>'PacketEVENTConv\<times>'PacketEVENTConv\<times>'PacketEVENTConv\<times>'PacketEVENTConv\<times>'PacketEVENTConv) \<Rightarrow> channels \<Rightarrow> 'M" where
"channelsChan PacketEVENTConv (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern) channel_router_b1Out_data = PacketEVENTConv channel_router_b1Out_data_pattern" |
"channelsChan PacketEVENTConv (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern) channel_router_b2Out_data = PacketEVENTConv channel_router_b2Out_data_pattern" |
"channelsChan PacketEVENTConv (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern) channel_router_cocaOut_data = PacketEVENTConv channel_router_cocaOut_data_pattern" |
"channelsChan PacketEVENTConv (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern) channel_router_dfpOut_data = PacketEVENTConv channel_router_dfpOut_data_pattern" |
"channelsChan PacketEVENTConv (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern) channel_router_maniacOut_data = PacketEVENTConv channel_router_maniacOut_data_pattern" |
"channelsChan PacketEVENTConv (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern) channel_router_mirmisOut_data = PacketEVENTConv channel_router_mirmisOut_data_pattern"

definition %invisible channelsChan_inv :: "('PacketEVENTConv \<Rightarrow> 'M) \<Rightarrow> (channels \<Rightarrow> 'M) \<Rightarrow> ('PacketEVENTConv \<times> 'PacketEVENTConv \<times> 'PacketEVENTConv \<times> 'PacketEVENTConv \<times> 'PacketEVENTConv \<times> 'PacketEVENTConv)" where
"channelsChan_inv PacketEVENTConv bundle = (inv PacketEVENTConv (bundle channel_router_b1Out_data), inv PacketEVENTConv (bundle channel_router_b2Out_data), inv PacketEVENTConv (bundle channel_router_cocaOut_data), inv PacketEVENTConv (bundle channel_router_dfpOut_data), inv PacketEVENTConv (bundle channel_router_maniacOut_data), inv PacketEVENTConv (bundle channel_router_mirmisOut_data))"

lemma %invisible channelsChan_surj_helper:
  assumes "f channel_router_b1Out_data \<in> range PacketEVENTConv"
      and "f channel_router_b2Out_data \<in> range PacketEVENTConv"
      and "f channel_router_cocaOut_data \<in> range PacketEVENTConv"
      and "f channel_router_dfpOut_data \<in> range PacketEVENTConv"
      and "f channel_router_maniacOut_data \<in> range PacketEVENTConv"
      and "f channel_router_mirmisOut_data \<in> range PacketEVENTConv"
    shows "channelsChan PacketEVENTConv (channelsChan_inv PacketEVENTConv f) = f"
  unfolding channelsChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma channelsChan_surj:
  assumes "f channel_router_b1Out_data \<in> range PacketEVENTConv"
      and "f channel_router_b2Out_data \<in> range PacketEVENTConv"
      and "f channel_router_cocaOut_data \<in> range PacketEVENTConv"
      and "f channel_router_dfpOut_data \<in> range PacketEVENTConv"
      and "f channel_router_maniacOut_data \<in> range PacketEVENTConv"
      and "f channel_router_mirmisOut_data \<in> range PacketEVENTConv"
    shows "f \<in> range (channelsChan PacketEVENTConv)"
  apply(subst channelsChan_surj_helper[symmetric, where PacketEVENTConv=PacketEVENTConv])
  by(simp_all add: assms)

lemma channelsChan_inj:
  assumes "inj PacketEVENTConv"
    shows "inj (channelsChan PacketEVENTConv)"
  apply (auto simp add: inj_def)
  by (metis assms channelsChan.simps injD)+

definition buildSBE where
"buildSBE \<equiv> channelsChan
    (Timed o TLive o map_event PacketEVENTConstr)"

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
  apply (metis channel_router_b1Out_data_rep assms PacketEVENT_ran)
  apply (metis channel_router_b2Out_data_rep assms PacketEVENT_ran)
  apply (metis channel_router_cocaOut_data_rep assms PacketEVENT_ran)
  apply (metis channel_router_dfpOut_data_rep assms PacketEVENT_ran)
  apply (metis channel_router_maniacOut_data_rep assms PacketEVENT_ran)
  apply (metis channel_router_mirmisOut_data_rep assms PacketEVENT_ran)
  done

declare buildSBE_def [simp del]

global_interpretation SBE: sbeGen "buildSBE"
  defines sbesetter = SBE.setter
  and sbegetter = SBE.getter
  and sbesettersb = SBE.setterSB
  by %visible(unfold_locales,simp_all)

definition buildSB where
"buildSB \<equiv> channelsChan
     (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr)))"

declare buildSB_def [simp]

lemma conc2sconc: "buildSB a1 c \<Zcat> buildSB a2 c = buildSB (a1 \<Zcat>\<Zcat> a2) c"
  apply(cases a1; cases a2; cases c)
    by(auto simp add: conc_prod_apply smap_split)+

theorem buildsb_ctype[simp]: "sValues\<cdot>(buildSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  apply (auto simp add: ctype_def smap_sValues image_iff)
  apply (metis surj_pair tsyn.exhaust)?
  done

theorem buildsb_inj[simp]: "inj buildSB"
  by (auto simp add: channelsChan_inj smap_inj)

theorem buildsb_surj[simp]:
  assumes "lsb_well sb"
    shows "sb \<in> range buildSB"
  apply (simp, rule channelsChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
  using PacketEVENT_ran apply simp
  using PacketEVENT_ran apply simp
  using PacketEVENT_ran apply simp
  using PacketEVENT_ran apply simp
  using PacketEVENT_ran apply simp
  using PacketEVENT_ran apply simp
  done

lemma channelsChan_split: "channelsChan PacketEVENTConv x = channelsChan PacketEVENTConv ((fst x), (fst (snd x)), (fst (snd (snd x))), (fst (snd (snd (snd x)))), (fst (snd (snd (snd (snd x))))), (snd (snd (snd (snd (snd x))))))"
  by auto

lemma cont_h:
  shows "cont PacketEVENTConv \<Longrightarrow>
         cont (\<lambda>x. channelsChan PacketEVENTConv x c)"
  apply(cases c, auto)
  apply(subst channelsChan_split, simp only: channelsChan.simps, intro cont2cont; simp)+
  done

lemma cont[cont2cont]:
  shows "cont PacketEVENTConv \<Longrightarrow>
         cont (channelsChan PacketEVENTConv)"
  by (simp add: cont_h)

lemma [simp]: "cont buildSB"
  by(simp, rule cont, simp)

lemma [simp]:"\<not> x \<sqsubseteq> y \<Longrightarrow> \<not> buildSB x \<sqsubseteq> buildSB y"
  apply(subst fun_below_iff,auto)
  apply(cases x; cases y; auto)
  apply(      solves\<open>(rule_tac x="channel_router_b1Out_data" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_router_b2Out_data" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_router_cocaOut_data" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_router_dfpOut_data" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_router_maniacOut_data" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_router_mirmisOut_data" in exI,simp)\<close>)+
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

lemma setter_sbe2sb: "sbe2sb (SBE.setter(channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern)) = SB.setter\<cdot>(\<up>channel_router_b1Out_data_pattern, \<up>channel_router_b2Out_data_pattern, \<up>channel_router_cocaOut_data_pattern, \<up>channel_router_dfpOut_data_pattern, \<up>channel_router_maniacOut_data_pattern, \<up>channel_router_mirmisOut_data_pattern)"
  apply(rule sb_eqI2)
  apply(case_tac c, auto)
  by(simp add: buildSBE_def buildSB_def)+

lemma setter_conc2sbconc: "SB.setter\<cdot>(s1 \<Zcat>\<Zcat> s2) = SB.setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> SB.setter\<cdot>s2"
  by(subst SB.getter_conc[symmetric], simp_all add: conc2sconc)

lemma getter_conc2sbconc: "SB.getter\<cdot>sb1 \<Zcat>\<Zcat> SB.getter\<cdot>sb2 = SB.getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  by (metis setter_conc2sbconc SB.get_set SB.set_get)

lemma setter_len[simp]: "#(SB.setter\<cdot>(channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern)) = Min {#channel_router_b1Out_data_pattern, #channel_router_b2Out_data_pattern, #channel_router_cocaOut_data_pattern, #channel_router_dfpOut_data_pattern, #channel_router_maniacOut_data_pattern, #channel_router_mirmisOut_data_pattern}"
  apply (subst SB.setter_len, simp)
  apply (simp only: len_prod_def2)+
  apply (subst Min2min, simp)+
  by (simp only: Min_singleton)

declare len_prod_inf_snd[simp]


end

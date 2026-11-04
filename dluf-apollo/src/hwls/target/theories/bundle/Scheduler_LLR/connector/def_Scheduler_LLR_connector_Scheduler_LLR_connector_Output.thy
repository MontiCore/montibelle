theory def_Scheduler_LLR_connector_Scheduler_LLR_connector_Output
  imports
    (* Core *) bundle.MsgWithChan
    (* Gen  *) data_inc.Data_inc
    (* Hwl  *)

begin


default_sort type

declare len_prod_inf_snd[simp del]


typedef channels = "{(CH ''channel_buffer_control_data'' TTLive TCtrlEnumEVENT), (CH ''channel_buffer_input_data'' TTLive TPacketEVENT), (CH ''channel_capacity_input_data'' TTLive TPacketEVENT), (CH ''channel_output_data'' TTLive TPacketEVENT)}"
  by auto

instance channels::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_channels
        typedef_finite_UNIV by fastforce

instantiation channels::somechan
begin
  definition Rep_channels_def: "Rep = Rep_channels"
  definition Abs_channels_def:"Abs = Abs_channels"
  definition ChanDom_channels_def: "chanDom(a::channels myself) = {(CH ''channel_buffer_control_data'' TTLive TCtrlEnumEVENT), (CH ''channel_buffer_input_data'' TTLive TPacketEVENT), (CH ''channel_capacity_input_data'' TTLive TPacketEVENT), (CH ''channel_output_data'' TTLive TPacketEVENT)}"

  lemma rep_range[simp]: "range (Rep::channels \<Rightarrow> channel) = {(CH ''channel_buffer_control_data'' TTLive TCtrlEnumEVENT), (CH ''channel_buffer_input_data'' TTLive TPacketEVENT), (CH ''channel_capacity_input_data'' TTLive TPacketEVENT), (CH ''channel_output_data'' TTLive TPacketEVENT)}"
    apply(subst Rep_channels_def)
    using type_definition.Rep_range type_definition_channels by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_channels_def Rep_channels_def Rep_channels_inverse)
     apply(simp add:ChanDom_channels_def insert_Diff_if)
    by clarsimp
end

theorem channels_chdom[simp]: "chDom TYPE (channels) = {(CH ''channel_buffer_control_data'' TTLive TCtrlEnumEVENT), (CH ''channel_buffer_input_data'' TTLive TPacketEVENT), (CH ''channel_capacity_input_data'' TTLive TPacketEVENT), (CH ''channel_output_data'' TTLive TPacketEVENT)}"
  by (metis ChanDom_channels_def chandom_chdom_eq)

definition channel_buffer_control_data :: "channels" where
"channel_buffer_control_data \<equiv> Abs_channels (CH ''channel_buffer_control_data'' TTLive TCtrlEnumEVENT)"

lemma channel_buffer_control_data_rep [simp, code]: "Rep channel_buffer_control_data = (CH ''channel_buffer_control_data'' TTLive TCtrlEnumEVENT)"
  unfolding Rep_channels_def channel_buffer_control_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_Scheduler_LLR_buffer_control_data_abs [simp, code]: "Abs (CH ''channel_buffer_control_data'' TTLive TCtrlEnumEVENT) = channel_buffer_control_data"
  by (metis abs_rep_id channel_buffer_control_data_rep)

definition channel_buffer_input_data :: "channels" where
"channel_buffer_input_data \<equiv> Abs_channels (CH ''channel_buffer_input_data'' TTLive TPacketEVENT)"

lemma channel_buffer_input_data_rep [simp, code]: "Rep channel_buffer_input_data = (CH ''channel_buffer_input_data'' TTLive TPacketEVENT)"
  unfolding Rep_channels_def channel_buffer_input_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_Scheduler_LLR_buffer_input_data_abs [simp, code]: "Abs (CH ''channel_buffer_input_data'' TTLive TPacketEVENT) = channel_buffer_input_data"
  by (metis abs_rep_id channel_buffer_input_data_rep)

definition channel_capacity_input_data :: "channels" where
"channel_capacity_input_data \<equiv> Abs_channels (CH ''channel_capacity_input_data'' TTLive TPacketEVENT)"

lemma channel_capacity_input_data_rep [simp, code]: "Rep channel_capacity_input_data = (CH ''channel_capacity_input_data'' TTLive TPacketEVENT)"
  unfolding Rep_channels_def channel_capacity_input_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_Scheduler_LLR_capacity_input_data_abs [simp, code]: "Abs (CH ''channel_capacity_input_data'' TTLive TPacketEVENT) = channel_capacity_input_data"
  by (metis abs_rep_id channel_capacity_input_data_rep)

definition channel_output_data :: "channels" where
"channel_output_data \<equiv> Abs_channels (CH ''channel_output_data'' TTLive TPacketEVENT)"

lemma channel_output_data_rep [simp, code]: "Rep channel_output_data = (CH ''channel_output_data'' TTLive TPacketEVENT)"
  unfolding Rep_channels_def channel_output_data_def
  by (simp add: Abs_channels_inverse)

lemma channel_Scheduler_HLR2_output_data_abs [simp, code]: "Abs (CH ''channel_output_data'' TTLive TPacketEVENT) = channel_output_data"
  by (metis abs_rep_id channel_output_data_rep)

free_constructors channels for channel_buffer_control_data | channel_buffer_input_data | channel_capacity_input_data | channel_output_data
  unfolding channel_buffer_control_data_def channel_buffer_input_data_def channel_capacity_input_data_def channel_output_data_def
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "P channel_buffer_control_data \<or> P channel_buffer_input_data \<or> P channel_capacity_input_data \<or> P channel_output_data \<Longrightarrow> \<exists>c. P c"
  by auto

instance channels::echan
  apply(intro_classes)
  by(case_tac c;simp)

instantiation channels::enum
begin
  definition "enum_channels \<equiv> [channel_buffer_control_data, channel_buffer_input_data, channel_capacity_input_data, channel_output_data]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end


lift_definition channel_Scheduler_LLR_buffer_control_dataConstr :: "CtrlEnum \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_buffer_control_data, CtrlEnumEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_Scheduler_LLR_buffer_input_dataConstr :: "Packet \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_buffer_input_data, PacketEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_Scheduler_LLR_capacity_input_dataConstr :: "Packet \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_capacity_input_data, PacketEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_Scheduler_HLR2_output_dataConstr :: "Packet \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_output_data, PacketEVENTConstr x)"
  by (simp add: well_def)





fun channelsChan::"('CtrlEnumEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('PacketEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('CtrlEnumEVENTConv\<times>'PacketEVENTConv\<times>'PacketEVENTConv\<times>'PacketEVENTConv) \<Rightarrow> channels \<Rightarrow> 'M" where
"channelsChan CtrlEnumEVENTConv PacketEVENTConv (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern) channel_buffer_control_data = CtrlEnumEVENTConv channel_buffer_control_data_pattern" |
"channelsChan CtrlEnumEVENTConv PacketEVENTConv (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern) channel_buffer_input_data = PacketEVENTConv channel_buffer_input_data_pattern" |
"channelsChan CtrlEnumEVENTConv PacketEVENTConv (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern) channel_capacity_input_data = PacketEVENTConv channel_capacity_input_data_pattern" |
"channelsChan CtrlEnumEVENTConv PacketEVENTConv (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern) channel_output_data = PacketEVENTConv channel_output_data_pattern"

definition %invisible channelsChan_inv :: "('CtrlEnumEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('PacketEVENTConv \<Rightarrow> 'M) \<Rightarrow> (channels \<Rightarrow> 'M) \<Rightarrow> ('CtrlEnumEVENTConv \<times> 'PacketEVENTConv \<times> 'PacketEVENTConv \<times> 'PacketEVENTConv)" where
"channelsChan_inv CtrlEnumEVENTConv PacketEVENTConv bundle = (inv CtrlEnumEVENTConv (bundle channel_buffer_control_data), inv PacketEVENTConv (bundle channel_buffer_input_data), inv PacketEVENTConv (bundle channel_capacity_input_data), inv PacketEVENTConv (bundle channel_output_data))"

lemma %invisible channelsChan_surj_helper:
  assumes "f channel_buffer_control_data \<in> range CtrlEnumEVENTConv"
      and "f channel_buffer_input_data \<in> range PacketEVENTConv"
      and "f channel_capacity_input_data \<in> range PacketEVENTConv"
      and "f channel_output_data \<in> range PacketEVENTConv"
    shows "channelsChan CtrlEnumEVENTConv PacketEVENTConv (channelsChan_inv CtrlEnumEVENTConv PacketEVENTConv f) = f"
  unfolding channelsChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma channelsChan_surj:
  assumes "f channel_buffer_control_data \<in> range CtrlEnumEVENTConv"
      and "f channel_buffer_input_data \<in> range PacketEVENTConv"
      and "f channel_capacity_input_data \<in> range PacketEVENTConv"
      and "f channel_output_data \<in> range PacketEVENTConv"
    shows "f \<in> range (channelsChan CtrlEnumEVENTConv PacketEVENTConv)"
  apply(subst channelsChan_surj_helper[symmetric, where CtrlEnumEVENTConv=CtrlEnumEVENTConv and PacketEVENTConv=PacketEVENTConv])
  by(simp_all add: assms)

lemma channelsChan_inj:
  assumes "inj CtrlEnumEVENTConv"
      and "inj PacketEVENTConv"
    shows "inj (channelsChan CtrlEnumEVENTConv PacketEVENTConv)"
  apply (auto simp add: inj_def)
  by (metis assms channelsChan.simps injD)+

definition buildSBE where
"buildSBE \<equiv> channelsChan
    (Timed o TLive o map_event CtrlEnumEVENTConstr) 
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
  apply (metis channel_buffer_control_data_rep assms CtrlEnumEVENT_ran)
  apply (metis channel_buffer_input_data_rep assms PacketEVENT_ran)
  apply (metis channel_capacity_input_data_rep assms PacketEVENT_ran)
  apply (metis channel_output_data_rep assms PacketEVENT_ran)
  done

declare buildSBE_def [simp del]

global_interpretation SBE: sbeGen "buildSBE"
  defines sbesetter = SBE.setter
  and sbegetter = SBE.getter
  and sbesettersb = SBE.setterSB
  by %visible(unfold_locales,simp_all)

definition buildSB where
"buildSB \<equiv> channelsChan
     (Rep_cfun (smap (Timed o TLive o map_event CtrlEnumEVENTConstr)))
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
  using CtrlEnumEVENT_ran apply simp
  using PacketEVENT_ran apply simp
  using PacketEVENT_ran apply simp
  using PacketEVENT_ran apply simp
  done

lemma channelsChan_split: "channelsChan CtrlEnumEVENTConv PacketEVENTConv x = channelsChan CtrlEnumEVENTConv PacketEVENTConv ((fst x), (fst (snd x)), (fst (snd (snd x))), (snd (snd (snd x))))"
  by auto

lemma cont_h:
  shows "cont CtrlEnumEVENTConv \<and> cont PacketEVENTConv \<Longrightarrow>
         cont (\<lambda>x. channelsChan CtrlEnumEVENTConv PacketEVENTConv x c)"
  apply(cases c, auto)
  apply(subst channelsChan_split, simp only: channelsChan.simps, intro cont2cont; simp)+
  done

lemma cont[cont2cont]:
  shows "cont CtrlEnumEVENTConv \<and> cont PacketEVENTConv \<Longrightarrow>
         cont (channelsChan CtrlEnumEVENTConv PacketEVENTConv)"
  by (simp add: cont_h)

lemma [simp]: "cont buildSB"
  by(simp, rule cont, simp)

lemma [simp]:"\<not> x \<sqsubseteq> y \<Longrightarrow> \<not> buildSB x \<sqsubseteq> buildSB y"
  apply(subst fun_below_iff,auto)
  apply(cases x; cases y; auto)
  apply(      solves\<open>(rule_tac x="channel_buffer_control_data" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_buffer_input_data" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_capacity_input_data" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_output_data" in exI,simp)\<close>)+
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

lemma setter_sbe2sb: "sbe2sb (SBE.setter(channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern)) = SB.setter\<cdot>(\<up>channel_buffer_control_data_pattern, \<up>channel_buffer_input_data_pattern, \<up>channel_capacity_input_data_pattern, \<up>channel_output_data_pattern)"
  apply(rule sb_eqI2)
  apply(case_tac c, auto)
  by(simp add: buildSBE_def buildSB_def)+

lemma setter_conc2sbconc: "SB.setter\<cdot>(s1 \<Zcat>\<Zcat> s2) = SB.setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> SB.setter\<cdot>s2"
  by(subst SB.getter_conc[symmetric], simp_all add: conc2sconc)

lemma getter_conc2sbconc: "SB.getter\<cdot>sb1 \<Zcat>\<Zcat> SB.getter\<cdot>sb2 = SB.getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  by (metis setter_conc2sbconc SB.get_set SB.set_get)

lemma setter_len[simp]: "#(SB.setter\<cdot>(channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern)) = Min {#channel_buffer_control_data_pattern, #channel_buffer_input_data_pattern, #channel_capacity_input_data_pattern, #channel_output_data_pattern}"
  apply (subst SB.setter_len, simp)
  apply (simp only: len_prod_def2)+
  apply (subst Min2min, simp)+
  by (simp only: Min_singleton)

declare len_prod_inf_snd[simp]


end

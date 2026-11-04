theory def_SecurityGate_LLR_Output
  imports
    (* Core *) bundle.MsgWithChan
    (* Gen  *) data_inc.Data_inc
    (* Hwl  *)

begin


default_sort type

declare len_prod_inf_snd[simp del]


typedef channels = "{(CH ''cempty'' TUntimed TNone)}"
  by auto

abbreviation "def_securitygate_llr_output_buildSB \<equiv> (\<lambda>(u::unit) cs::channels. \<epsilon>)"

instance channels::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_channels
        typedef_finite_UNIV by fastforce

instantiation channels::emptychan
begin
  definition Rep_channels_def: "Rep = Rep_channels"
  definition Abs_channels_def:"Abs = Abs_channels"
  definition ChanDom_channels_def: "chanDom(a::channels myself) = {}"

  lemma rep_range[simp]: "range (Rep::channels \<Rightarrow> channel) = {(CH ''cempty'' TUntimed TNone)}"
    apply(subst Rep_channels_def)
    using type_definition.Rep_range type_definition_channels by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_channels_def Rep_channels_def Rep_channels_inverse)
     apply(simp add:ChanDom_channels_def insert_Diff_if)
    by clarsimp
end

theorem channels_chdom[simp]: "chDom TYPE (channels) = {}"
  by (metis ChanDom_channels_def chandom_chdom_eq)


definition channel_cempty :: "channels" where
"channel_cempty \<equiv> Abs_channels (CH ''cempty'' TUntimed TNone)"

lemma channel_cempty_rep [simp, code]: "Rep channel_cempty = (CH ''cempty'' TUntimed TNone)"
  unfolding Rep_channels_def channel_cempty_def
  by (simp add: Abs_channels_inverse)

lemma channel_cempty_abs [simp, code]: "Abs (CH ''cempty'' TUntimed TNone) = channel_cempty"
  by (metis abs_rep_id channel_cempty_rep)

free_constructors channels for channel_cempty
  unfolding channel_cempty_def
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "P channel_cempty \<Longrightarrow> \<exists>c. P c"
  by auto

instance channels::echan
  apply(intro_classes)
  by(case_tac c;simp)

instantiation channels::enum
begin
  definition "enum_channels \<equiv> [channel_cempty]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end





definition buildSBE :: "unit \<Rightarrow> channels \<Rightarrow> M" where
"buildSBE = undefined"

declare buildSBE_def [simp del]

global_interpretation SBE: sbeGen_empty
  defines sbesetter = SBE.setter
  and sbegetter = SBE.getter
  and sbesettersb = SBE.setterSB
  done

global_interpretation SB: sbGen_empty
  defines sbsetter = SB.setter
      and sbgetter = SB.getter
  done

lemma getter_fold: "sbGen.getter def_securitygate_llr_output_buildSB = sbgetter"
  by (simp add: sbgetter_def)

lemma setter_sbe2sb: "sbe2sb (SBE.setter()) = SB.setter\<cdot>()"
  by auto

lemma setter_conc2sbconc: "SB.setter\<cdot>(s1 \<Zcat>\<Zcat> s2) = SB.setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> SB.setter\<cdot>s2"
  by(subst SB.getter_conc[symmetric], simp_all)

lemma getter_conc2sbconc: "SB.getter\<cdot>sb1 \<Zcat>\<Zcat> SB.getter\<cdot>sb2 = SB.getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  by (metis setter_conc2sbconc SB.get_set SB.set_get)

lemma "SB.setter\<cdot>() = \<bottom>"
  by simp

declare len_prod_inf_snd[simp]


end

theory def_SecureProtocol_LLR_connector_SecureProtocol_LLR_connector_Input
  imports
    (* Core *) bundle.MsgWithChan
    (* Gen  *) data_inc.Data_inc
    (* Hwl  *)

begin


default_sort type

declare len_prod_inf_snd[simp del]


typedef channels = "{(CH ''channel_alice_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_bob_control_val'' TTsyn TboolEVENT), (CH ''channel_bob_output_val'' TTsyn TnatEVENT), (CH ''channel_decrypt1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_decrypt2_output_val'' TTsyn TboolEVENT), (CH ''channel_encrypt1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_encrypt2_output_val'' TTsyn TboolEVENT), (CH ''channel_eve1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_eve2_output_val'' TTsyn TboolEVENT), (CH ''channel_input_val'' TTsyn TnatEVENT)}"
  by auto

instance channels::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_channels
        typedef_finite_UNIV by fastforce

instantiation channels::somechan
begin
  definition Rep_channels_def: "Rep = Rep_channels"
  definition Abs_channels_def:"Abs = Abs_channels"
  definition ChanDom_channels_def: "chanDom(a::channels myself) = {(CH ''channel_alice_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_bob_control_val'' TTsyn TboolEVENT), (CH ''channel_bob_output_val'' TTsyn TnatEVENT), (CH ''channel_decrypt1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_decrypt2_output_val'' TTsyn TboolEVENT), (CH ''channel_encrypt1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_encrypt2_output_val'' TTsyn TboolEVENT), (CH ''channel_eve1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_eve2_output_val'' TTsyn TboolEVENT), (CH ''channel_input_val'' TTsyn TnatEVENT)}"

  lemma rep_range[simp]: "range (Rep::channels \<Rightarrow> channel) = {(CH ''channel_alice_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_bob_control_val'' TTsyn TboolEVENT), (CH ''channel_bob_output_val'' TTsyn TnatEVENT), (CH ''channel_decrypt1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_decrypt2_output_val'' TTsyn TboolEVENT), (CH ''channel_encrypt1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_encrypt2_output_val'' TTsyn TboolEVENT), (CH ''channel_eve1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_eve2_output_val'' TTsyn TboolEVENT), (CH ''channel_input_val'' TTsyn TnatEVENT)}"
    apply(subst Rep_channels_def)
    using type_definition.Rep_range type_definition_channels by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_channels_def Rep_channels_def Rep_channels_inverse)
     apply(simp add:ChanDom_channels_def insert_Diff_if)
    by clarsimp
end

theorem channels_chdom[simp]: "chDom TYPE (channels) = {(CH ''channel_alice_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_bob_control_val'' TTsyn TboolEVENT), (CH ''channel_bob_output_val'' TTsyn TnatEVENT), (CH ''channel_decrypt1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_decrypt2_output_val'' TTsyn TboolEVENT), (CH ''channel_encrypt1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_encrypt2_output_val'' TTsyn TboolEVENT), (CH ''channel_eve1_output_val'' TTsyn TDataBoolTupleEVENT), (CH ''channel_eve2_output_val'' TTsyn TboolEVENT), (CH ''channel_input_val'' TTsyn TnatEVENT)}"
  by (metis ChanDom_channels_def chandom_chdom_eq)

definition channel_alice_output_val :: "channels" where
"channel_alice_output_val \<equiv> Abs_channels (CH ''channel_alice_output_val'' TTsyn TDataBoolTupleEVENT)"

lemma channel_alice_output_val_rep [simp, code]: "Rep channel_alice_output_val = (CH ''channel_alice_output_val'' TTsyn TDataBoolTupleEVENT)"
  unfolding Rep_channels_def channel_alice_output_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_LLR_alice_output_val_abs [simp, code]: "Abs (CH ''channel_alice_output_val'' TTsyn TDataBoolTupleEVENT) = channel_alice_output_val"
  by (metis abs_rep_id channel_alice_output_val_rep)

definition channel_bob_control_val :: "channels" where
"channel_bob_control_val \<equiv> Abs_channels (CH ''channel_bob_control_val'' TTsyn TboolEVENT)"

lemma channel_bob_control_val_rep [simp, code]: "Rep channel_bob_control_val = (CH ''channel_bob_control_val'' TTsyn TboolEVENT)"
  unfolding Rep_channels_def channel_bob_control_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_LLR_bob_control_val_abs [simp, code]: "Abs (CH ''channel_bob_control_val'' TTsyn TboolEVENT) = channel_bob_control_val"
  by (metis abs_rep_id channel_bob_control_val_rep)

definition channel_bob_output_val :: "channels" where
"channel_bob_output_val \<equiv> Abs_channels (CH ''channel_bob_output_val'' TTsyn TnatEVENT)"

lemma channel_bob_output_val_rep [simp, code]: "Rep channel_bob_output_val = (CH ''channel_bob_output_val'' TTsyn TnatEVENT)"
  unfolding Rep_channels_def channel_bob_output_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_LLR_bob_output_val_abs [simp, code]: "Abs (CH ''channel_bob_output_val'' TTsyn TnatEVENT) = channel_bob_output_val"
  by (metis abs_rep_id channel_bob_output_val_rep)

definition channel_decrypt1_output_val :: "channels" where
"channel_decrypt1_output_val \<equiv> Abs_channels (CH ''channel_decrypt1_output_val'' TTsyn TDataBoolTupleEVENT)"

lemma channel_decrypt1_output_val_rep [simp, code]: "Rep channel_decrypt1_output_val = (CH ''channel_decrypt1_output_val'' TTsyn TDataBoolTupleEVENT)"
  unfolding Rep_channels_def channel_decrypt1_output_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_LLR_decrypt1_output_val_abs [simp, code]: "Abs (CH ''channel_decrypt1_output_val'' TTsyn TDataBoolTupleEVENT) = channel_decrypt1_output_val"
  by (metis abs_rep_id channel_decrypt1_output_val_rep)

definition channel_decrypt2_output_val :: "channels" where
"channel_decrypt2_output_val \<equiv> Abs_channels (CH ''channel_decrypt2_output_val'' TTsyn TboolEVENT)"

lemma channel_decrypt2_output_val_rep [simp, code]: "Rep channel_decrypt2_output_val = (CH ''channel_decrypt2_output_val'' TTsyn TboolEVENT)"
  unfolding Rep_channels_def channel_decrypt2_output_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_LLR_decrypt2_output_val_abs [simp, code]: "Abs (CH ''channel_decrypt2_output_val'' TTsyn TboolEVENT) = channel_decrypt2_output_val"
  by (metis abs_rep_id channel_decrypt2_output_val_rep)

definition channel_encrypt1_output_val :: "channels" where
"channel_encrypt1_output_val \<equiv> Abs_channels (CH ''channel_encrypt1_output_val'' TTsyn TDataBoolTupleEVENT)"

lemma channel_encrypt1_output_val_rep [simp, code]: "Rep channel_encrypt1_output_val = (CH ''channel_encrypt1_output_val'' TTsyn TDataBoolTupleEVENT)"
  unfolding Rep_channels_def channel_encrypt1_output_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_LLR_encrypt1_output_val_abs [simp, code]: "Abs (CH ''channel_encrypt1_output_val'' TTsyn TDataBoolTupleEVENT) = channel_encrypt1_output_val"
  by (metis abs_rep_id channel_encrypt1_output_val_rep)

definition channel_encrypt2_output_val :: "channels" where
"channel_encrypt2_output_val \<equiv> Abs_channels (CH ''channel_encrypt2_output_val'' TTsyn TboolEVENT)"

lemma channel_encrypt2_output_val_rep [simp, code]: "Rep channel_encrypt2_output_val = (CH ''channel_encrypt2_output_val'' TTsyn TboolEVENT)"
  unfolding Rep_channels_def channel_encrypt2_output_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_LLR_encrypt2_output_val_abs [simp, code]: "Abs (CH ''channel_encrypt2_output_val'' TTsyn TboolEVENT) = channel_encrypt2_output_val"
  by (metis abs_rep_id channel_encrypt2_output_val_rep)

definition channel_eve1_output_val :: "channels" where
"channel_eve1_output_val \<equiv> Abs_channels (CH ''channel_eve1_output_val'' TTsyn TDataBoolTupleEVENT)"

lemma channel_eve1_output_val_rep [simp, code]: "Rep channel_eve1_output_val = (CH ''channel_eve1_output_val'' TTsyn TDataBoolTupleEVENT)"
  unfolding Rep_channels_def channel_eve1_output_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_LLR_eve1_output_val_abs [simp, code]: "Abs (CH ''channel_eve1_output_val'' TTsyn TDataBoolTupleEVENT) = channel_eve1_output_val"
  by (metis abs_rep_id channel_eve1_output_val_rep)

definition channel_eve2_output_val :: "channels" where
"channel_eve2_output_val \<equiv> Abs_channels (CH ''channel_eve2_output_val'' TTsyn TboolEVENT)"

lemma channel_eve2_output_val_rep [simp, code]: "Rep channel_eve2_output_val = (CH ''channel_eve2_output_val'' TTsyn TboolEVENT)"
  unfolding Rep_channels_def channel_eve2_output_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_LLR_eve2_output_val_abs [simp, code]: "Abs (CH ''channel_eve2_output_val'' TTsyn TboolEVENT) = channel_eve2_output_val"
  by (metis abs_rep_id channel_eve2_output_val_rep)

definition channel_input_val :: "channels" where
"channel_input_val \<equiv> Abs_channels (CH ''channel_input_val'' TTsyn TnatEVENT)"

lemma channel_input_val_rep [simp, code]: "Rep channel_input_val = (CH ''channel_input_val'' TTsyn TnatEVENT)"
  unfolding Rep_channels_def channel_input_val_def
  by (simp add: Abs_channels_inverse)

lemma channel_SecureProtocol_HLR1_input_val_abs [simp, code]: "Abs (CH ''channel_input_val'' TTsyn TnatEVENT) = channel_input_val"
  by (metis abs_rep_id channel_input_val_rep)

free_constructors channels for channel_alice_output_val | channel_bob_control_val | channel_bob_output_val | channel_decrypt1_output_val | channel_decrypt2_output_val | channel_encrypt1_output_val | channel_encrypt2_output_val | channel_eve1_output_val | channel_eve2_output_val | channel_input_val
  unfolding channel_alice_output_val_def channel_bob_control_val_def channel_bob_output_val_def channel_decrypt1_output_val_def channel_decrypt2_output_val_def channel_encrypt1_output_val_def channel_encrypt2_output_val_def channel_eve1_output_val_def channel_eve2_output_val_def channel_input_val_def
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "P channel_alice_output_val \<or> P channel_bob_control_val \<or> P channel_bob_output_val \<or> P channel_decrypt1_output_val \<or> P channel_decrypt2_output_val \<or> P channel_encrypt1_output_val \<or> P channel_encrypt2_output_val \<or> P channel_eve1_output_val \<or> P channel_eve2_output_val \<or> P channel_input_val \<Longrightarrow> \<exists>c. P c"
  by auto

instance channels::tschan
  apply(intro_classes)
  by(case_tac c;simp)

instantiation channels::enum
begin
  definition "enum_channels \<equiv> [channel_alice_output_val, channel_bob_control_val, channel_bob_output_val, channel_decrypt1_output_val, channel_decrypt2_output_val, channel_encrypt1_output_val, channel_encrypt2_output_val, channel_eve1_output_val, channel_eve2_output_val, channel_input_val]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end


lift_definition channel_SecureProtocol_LLR_alice_output_valConstr :: "Data_Bool_Tuple \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_alice_output_val, DataBoolTupleEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_SecureProtocol_LLR_bob_control_valConstr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_bob_control_val, boolEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_SecureProtocol_LLR_bob_output_valConstr :: "nat \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_bob_output_val, natEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_SecureProtocol_LLR_decrypt1_output_valConstr :: "Data_Bool_Tuple \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_decrypt1_output_val, DataBoolTupleEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_SecureProtocol_LLR_decrypt2_output_valConstr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_decrypt2_output_val, boolEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_SecureProtocol_LLR_encrypt1_output_valConstr :: "Data_Bool_Tuple \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_encrypt1_output_val, DataBoolTupleEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_SecureProtocol_LLR_encrypt2_output_valConstr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_encrypt2_output_val, boolEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_SecureProtocol_LLR_eve1_output_valConstr :: "Data_Bool_Tuple \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_eve1_output_val, DataBoolTupleEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_SecureProtocol_LLR_eve2_output_valConstr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_eve2_output_val, boolEVENTConstr x)"
  by (simp add: well_def)

lift_definition channel_SecureProtocol_HLR1_input_valConstr :: "nat \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_input_val, natEVENTConstr x)"
  by (simp add: well_def)





fun channelsChan::"('DataBoolTupleEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('boolEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('natEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('DataBoolTupleEVENTConv\<times>'boolEVENTConv\<times>'natEVENTConv\<times>'DataBoolTupleEVENTConv\<times>'boolEVENTConv\<times>'DataBoolTupleEVENTConv\<times>'boolEVENTConv\<times>'DataBoolTupleEVENTConv\<times>'boolEVENTConv\<times>'natEVENTConv) \<Rightarrow> channels \<Rightarrow> 'M" where
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_alice_output_val = DataBoolTupleEVENTConv channel_alice_output_val_pattern" |
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_bob_control_val = boolEVENTConv channel_bob_control_val_pattern" |
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_bob_output_val = natEVENTConv channel_bob_output_val_pattern" |
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_decrypt1_output_val = DataBoolTupleEVENTConv channel_decrypt1_output_val_pattern" |
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_decrypt2_output_val = boolEVENTConv channel_decrypt2_output_val_pattern" |
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_encrypt1_output_val = DataBoolTupleEVENTConv channel_encrypt1_output_val_pattern" |
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_encrypt2_output_val = boolEVENTConv channel_encrypt2_output_val_pattern" |
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_eve1_output_val = DataBoolTupleEVENTConv channel_eve1_output_val_pattern" |
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_eve2_output_val = boolEVENTConv channel_eve2_output_val_pattern" |
"channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern) channel_input_val = natEVENTConv channel_input_val_pattern"

definition %invisible channelsChan_inv :: "('DataBoolTupleEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('boolEVENTConv \<Rightarrow> 'M) \<Rightarrow> ('natEVENTConv \<Rightarrow> 'M) \<Rightarrow> (channels \<Rightarrow> 'M) \<Rightarrow> ('DataBoolTupleEVENTConv \<times> 'boolEVENTConv \<times> 'natEVENTConv \<times> 'DataBoolTupleEVENTConv \<times> 'boolEVENTConv \<times> 'DataBoolTupleEVENTConv \<times> 'boolEVENTConv \<times> 'DataBoolTupleEVENTConv \<times> 'boolEVENTConv \<times> 'natEVENTConv)" where
"channelsChan_inv DataBoolTupleEVENTConv boolEVENTConv natEVENTConv bundle = (inv DataBoolTupleEVENTConv (bundle channel_alice_output_val), inv boolEVENTConv (bundle channel_bob_control_val), inv natEVENTConv (bundle channel_bob_output_val), inv DataBoolTupleEVENTConv (bundle channel_decrypt1_output_val), inv boolEVENTConv (bundle channel_decrypt2_output_val), inv DataBoolTupleEVENTConv (bundle channel_encrypt1_output_val), inv boolEVENTConv (bundle channel_encrypt2_output_val), inv DataBoolTupleEVENTConv (bundle channel_eve1_output_val), inv boolEVENTConv (bundle channel_eve2_output_val), inv natEVENTConv (bundle channel_input_val))"

lemma %invisible channelsChan_surj_helper:
  assumes "f channel_alice_output_val \<in> range DataBoolTupleEVENTConv"
      and "f channel_bob_control_val \<in> range boolEVENTConv"
      and "f channel_bob_output_val \<in> range natEVENTConv"
      and "f channel_decrypt1_output_val \<in> range DataBoolTupleEVENTConv"
      and "f channel_decrypt2_output_val \<in> range boolEVENTConv"
      and "f channel_encrypt1_output_val \<in> range DataBoolTupleEVENTConv"
      and "f channel_encrypt2_output_val \<in> range boolEVENTConv"
      and "f channel_eve1_output_val \<in> range DataBoolTupleEVENTConv"
      and "f channel_eve2_output_val \<in> range boolEVENTConv"
      and "f channel_input_val \<in> range natEVENTConv"
    shows "channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv (channelsChan_inv DataBoolTupleEVENTConv boolEVENTConv natEVENTConv f) = f"
  unfolding channelsChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma channelsChan_surj:
  assumes "f channel_alice_output_val \<in> range DataBoolTupleEVENTConv"
      and "f channel_bob_control_val \<in> range boolEVENTConv"
      and "f channel_bob_output_val \<in> range natEVENTConv"
      and "f channel_decrypt1_output_val \<in> range DataBoolTupleEVENTConv"
      and "f channel_decrypt2_output_val \<in> range boolEVENTConv"
      and "f channel_encrypt1_output_val \<in> range DataBoolTupleEVENTConv"
      and "f channel_encrypt2_output_val \<in> range boolEVENTConv"
      and "f channel_eve1_output_val \<in> range DataBoolTupleEVENTConv"
      and "f channel_eve2_output_val \<in> range boolEVENTConv"
      and "f channel_input_val \<in> range natEVENTConv"
    shows "f \<in> range (channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv)"
  apply(subst channelsChan_surj_helper[symmetric, where DataBoolTupleEVENTConv=DataBoolTupleEVENTConv and boolEVENTConv=boolEVENTConv and natEVENTConv=natEVENTConv])
  by(simp_all add: assms)

lemma channelsChan_inj:
  assumes "inj DataBoolTupleEVENTConv"
      and "inj boolEVENTConv"
      and "inj natEVENTConv"
    shows "inj (channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv)"
  apply (auto simp add: inj_def)
  by (metis assms channelsChan.simps injD)+

definition buildSBE where
"buildSBE \<equiv> channelsChan
    (Timed o Tsyn o map_tsyn DataBoolTupleEVENTConstr) 
    (Timed o Tsyn o map_tsyn boolEVENTConstr) 
    (Timed o Tsyn o map_tsyn natEVENTConstr)"

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
  apply (metis channel_alice_output_val_rep assms Data_Bool_TupleEVENT_ran)
  apply (metis channel_bob_control_val_rep assms boolEVENT_ran)
  apply (metis channel_bob_output_val_rep assms natEVENT_ran)
  apply (metis channel_decrypt1_output_val_rep assms Data_Bool_TupleEVENT_ran)
  apply (metis channel_decrypt2_output_val_rep assms boolEVENT_ran)
  apply (metis channel_encrypt1_output_val_rep assms Data_Bool_TupleEVENT_ran)
  apply (metis channel_encrypt2_output_val_rep assms boolEVENT_ran)
  apply (metis channel_eve1_output_val_rep assms Data_Bool_TupleEVENT_ran)
  apply (metis channel_eve2_output_val_rep assms boolEVENT_ran)
  apply (metis channel_input_val_rep assms natEVENT_ran)
  done

declare buildSBE_def [simp del]

global_interpretation SBE: sbeGen "buildSBE"
  defines sbesetter = SBE.setter
  and sbegetter = SBE.getter
  and sbesettersb = SBE.setterSB
  by %visible(unfold_locales,simp_all)

definition buildSB where
"buildSB \<equiv> channelsChan
     (Rep_cfun (smap (Timed o Tsyn o map_tsyn DataBoolTupleEVENTConstr)))
     (Rep_cfun (smap (Timed o Tsyn o map_tsyn boolEVENTConstr)))
     (Rep_cfun (smap (Timed o Tsyn o map_tsyn natEVENTConstr)))"

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
  using Data_Bool_TupleEVENT_ran apply simp
  using boolEVENT_ran apply simp
  using natEVENT_ran apply simp
  using Data_Bool_TupleEVENT_ran apply simp
  using boolEVENT_ran apply simp
  using Data_Bool_TupleEVENT_ran apply simp
  using boolEVENT_ran apply simp
  using Data_Bool_TupleEVENT_ran apply simp
  using boolEVENT_ran apply simp
  using natEVENT_ran apply simp
  done

lemma channelsChan_split: "channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv x = channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv ((fst x), (fst (snd x)), (fst (snd (snd x))), (fst (snd (snd (snd x)))), (fst (snd (snd (snd (snd x))))), (fst (snd (snd (snd (snd (snd x)))))), (fst (snd (snd (snd (snd (snd (snd x))))))), (fst (snd (snd (snd (snd (snd (snd (snd x)))))))), (fst (snd (snd (snd (snd (snd (snd (snd (snd x))))))))), (snd (snd (snd (snd (snd (snd (snd (snd (snd x))))))))))"
  by auto

lemma cont_h:
  shows "cont DataBoolTupleEVENTConv \<and> cont boolEVENTConv \<and> cont natEVENTConv \<Longrightarrow>
         cont (\<lambda>x. channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv x c)"
  apply(cases c, auto)
  apply(subst channelsChan_split, simp only: channelsChan.simps, intro cont2cont; simp)+
  done

lemma cont[cont2cont]:
  shows "cont DataBoolTupleEVENTConv \<and> cont boolEVENTConv \<and> cont natEVENTConv \<Longrightarrow>
         cont (channelsChan DataBoolTupleEVENTConv boolEVENTConv natEVENTConv)"
  by (simp add: cont_h)

lemma [simp]: "cont buildSB"
  by(simp, rule cont, simp)

lemma [simp]:"\<not> x \<sqsubseteq> y \<Longrightarrow> \<not> buildSB x \<sqsubseteq> buildSB y"
  apply(subst fun_below_iff,auto)
  apply(cases x; cases y; auto)
  apply(      solves\<open>(rule_tac x="channel_alice_output_val" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_bob_control_val" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_bob_output_val" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_decrypt1_output_val" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_decrypt2_output_val" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_encrypt1_output_val" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_encrypt2_output_val" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_eve1_output_val" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_eve2_output_val" in exI,simp)\<close> |
          solves\<open>(rule_tac x="channel_input_val" in exI,simp)\<close>)+
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

lemma [simp]: "(#a) <= (#\<^sub>\<surd>(buildSB a c))"
  apply (cases c; simp; fail)?
  apply (cases c;cases a; auto?, simp_all?)?
  by (simp_all add: tlen_prod_minl tlen_prod_rsmaller len_prod_minl len_prod_rsmaller)?
lemma [simp]: "(#\<^sub>\<surd>a) <= (#\<^sub>\<surd>(buildSB a c))"
  apply (cases c; simp; fail)?
  apply (cases c;cases a; auto?, simp_all?)?
  by (simp_all add: tlen_prod_minl tlen_prod_rsmaller len_prod_minl len_prod_rsmaller)?

lemma [simp]: "\<exists>c. (#a) = (#\<^sub>\<surd>(buildSB a c))"
  apply ((rule channels_exists, simp); fail|cases a; auto?, simp?)
  apply (rule channels_exists, simp)?
  apply auto?
  apply ((subst len_prod_def2)+)?
  apply ((subst(asm) len_prod_def2)+)?
  apply ((subst tlen_prod_def2)+)?
  apply ((subst(asm) tlen_prod_def2)+)?
  by (smt min_def)?
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

lemma setter_sbe2sb: "sbe2sb (SBE.setter(channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern)) = SB.setter\<cdot>(\<up>channel_alice_output_val_pattern, \<up>channel_bob_control_val_pattern, \<up>channel_bob_output_val_pattern, \<up>channel_decrypt1_output_val_pattern, \<up>channel_decrypt2_output_val_pattern, \<up>channel_encrypt1_output_val_pattern, \<up>channel_encrypt2_output_val_pattern, \<up>channel_eve1_output_val_pattern, \<up>channel_eve2_output_val_pattern, \<up>channel_input_val_pattern)"
  apply(rule sb_eqI2)
  apply(case_tac c, auto)
  by(simp add: buildSBE_def buildSB_def)+

lemma setter_conc2sbconc: "SB.setter\<cdot>(s1 \<Zcat>\<Zcat> s2) = SB.setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> SB.setter\<cdot>s2"
  by(subst SB.getter_conc[symmetric], simp_all add: conc2sconc)

lemma getter_conc2sbconc: "SB.getter\<cdot>sb1 \<Zcat>\<Zcat> SB.getter\<cdot>sb2 = SB.getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  by (metis setter_conc2sbconc SB.get_set SB.set_get)

lemma setter_len[simp]: "#(SB.setter\<cdot>(channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern)) = Min {#channel_alice_output_val_pattern, #channel_bob_control_val_pattern, #channel_bob_output_val_pattern, #channel_decrypt1_output_val_pattern, #channel_decrypt2_output_val_pattern, #channel_encrypt1_output_val_pattern, #channel_encrypt2_output_val_pattern, #channel_eve1_output_val_pattern, #channel_eve2_output_val_pattern, #channel_input_val_pattern}"
  apply (subst SB.setter_len, simp)
  apply (simp only: len_prod_def2)+
  apply (subst Min2min, simp)+
  by (simp only: Min_singleton)

declare len_prod_inf_snd[simp]


end

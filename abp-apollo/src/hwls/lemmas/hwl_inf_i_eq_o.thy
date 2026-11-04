theory hwl_inf_i_eq_o
  imports

    move_to_core.TsynSBFunctionExtension
    move_to_core.TsynStreamExtension
    stream.StreamIterate

    to_be_generated.hwl_tsynSBlens

    hwl_fin_i_eq_o
    hwl_live
begin



lemma inf_i_eq_o:
  assumes "spf\<in> def_SecureProtocol_HLR2.Sps ()"
    and "output = (spf\<cdot>(sb)\<star> :: def_SecureProtocol_HLR1_Output.channels\<^sup>\<Omega>)"
    and "input = (sb\<star> :: def_SecureProtocol_HLR1_Input.channels\<^sup>\<Omega>)"
    and "#input = \<infinity>"
    and "tsynSBlen input = \<infinity>"
  shows "(def_SecureProtocol_HLR1_Input.sbgetter\<cdot>input)\<^sup>- = (def_SecureProtocol_HLR1_Output.sbgetter\<cdot>output)\<^sup>-"
proof -
  obtain ins where ins_def: "ins = def_SecureProtocol_HLR1_Input.sbgetter\<cdot>input"
    by blast

  define K where "K \<equiv> def_SecureProtocol_HLR1_Output.sbgetter oo spf oo def_SecureProtocol_HLR1_Input.sbsetter"
  define P where "P \<equiv> \<lambda>x. (K\<cdot>x)\<^sup>- = x\<^sup>-"

  have out_eq: "def_SecureProtocol_HLR1_Output.sbgetter\<cdot>output = K\<cdot>ins"
    by (simp add: K_def ins_def assms)

  have ins_inf: "#ins = \<infinity>"
    by (simp add: assms(4) ins_def)

  have adm: "\<And>s. #s = \<infinity> \<and> #\<^sub>-s < \<infinity> \<Longrightarrow> P s"
    using P_def K_def assms(1) fin_i_eq_o by auto

  have live: "\<And>s. #\<^sub>-s = \<infinity> \<Longrightarrow> #\<^sub>-(K\<cdot>s) = \<infinity>"
    by(simp add: K_def live_stream assms(1))

  have "P ins"
    apply(rule tsyn_abp_adm[OF P_def])
      apply(fact adm)
     apply(fact live)
    by(fact ins_inf)

  thus ?thesis
    by(simp add: out_eq ins_def[symmetric] P_def)
qed


end

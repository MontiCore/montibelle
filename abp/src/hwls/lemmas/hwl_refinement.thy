theory hwl_refinement
  imports hwl_inf_i_eq_o sps_SecureProtocol_HLR1.def_SecureProtocol_HLR1

begin

lemma pred_0_lifted:
  assumes "spf\<in> def_SecureProtocol_HLR2.Sps ()"
    and "output = (spf\<cdot>(sb)\<star> :: def_SecureProtocol_HLR1_Output.channels\<^sup>\<Omega>)"
    and "input = (sb\<star> :: def_SecureProtocol_HLR1_Input.channels\<^sup>\<Omega>)"
    and "#input = \<infinity>"
  shows "(def_SecureProtocol_HLR1_Input.sbgetter\<cdot>input)\<^sup>- = (def_SecureProtocol_HLR1_Output.sbgetter\<cdot>output)\<^sup>-"
  apply(case_tac "tsynSBlen input = \<infinity>")
   apply(fact inf_i_eq_o[OF assms])
  apply(rule fin_i_eq_o2[OF assms])
  by (simp add: min.strict_order_iff)


lemma len_prod_leq: "#a \<le> #b \<Longrightarrow> #(b, a) <\<^sup>l #c \<Longrightarrow> #a <\<^sup>l #c"
  by(simp add: len_prod_def2)

lemma
  not_that_hard:
  assumes "#(decrypt2_output, input) <\<^sup>l #alice_output"
    and "#alice_output \<le> #encrypt1_output"
    and "#encrypt1_output \<le> #eve1_output"
    and "#eve1_output \<le> #decrypt1_output"
    and "#decrypt1_output <\<^sup>l #(bob_control, bob_output)"
    and "#bob_control \<le> #encrypt2_output"
    and "#encrypt2_output \<le> #eve2_output"
    and "#eve2_output \<le> #decrypt2_output"
  shows "#input \<le> #decrypt2_output"
proof(rule ccontr)
  assume a: "\<not> #input \<le> #decrypt2_output"
  then have b: "#input \<ge> #decrypt2_output"
    by simp
  then have "#decrypt2_output <\<^sup>l #alice_output"
    apply (insert assms(1))
    by(simp add: len_prod_def2 b)
  thus "False"
    by (metis a assms inf_ub len_prod_minl less_lnsuc lnle_and_gt_inf(2) order_trans)
qed

lemma refinement[simp]: "def_SecureProtocol_HLR2.Sps () \<subseteq> def_SecureProtocol_HLR1.Sps ()"
 (* by(simp add: subsetI def_SecureProtocol_HLR1.Sps_def comp_pred_whole)
*) oops
end

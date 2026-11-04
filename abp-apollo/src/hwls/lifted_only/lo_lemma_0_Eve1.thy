theory lo_lemma_0_Eve1
  imports
    lo_sps_Eve1
    lo_lemma_util
    to_be_generated.hwl_tsynSBlens
begin


(*
thm tsynSBlen_rule

thm def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter
(* def_SecureProtocol_HLR2_eve1_Output.tsynSBlen_setter *)
lemma def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter: "tsynSBlen (f (def_SecureProtocol_HLR2_eve1_Output.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f out)}"
  apply(rule tsynSBlen_rule, simp_all)
  defer (* allows us to do the simps only once *)
   apply (rule def_SecureProtocol_HLR2_eve1_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve1_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

text \<open>Lifts a function from stream level to bundle level on a per-channel basis.\<close>
locale liftedSpf =
  fixes fn::"M stream \<rightarrow> M stream"
  assumes well: "\<And>sb::'cs::{chan}\<^sup>\<Omega>. lsb_well (\<lambda>c. fn\<cdot>(sb  \<^enum>  c))"
(*<*)
begin
(*>*)

lift_definition lifted::"'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>"
  is "\<lambda>sb. Abs_lsb (\<lambda>c. fn\<cdot>(sb \<^enum> c))"
  apply (intro cont2cont)
  by (fact well)

lemma sbChGet: "(liftedSpf.lifted fn\<cdot>sb)  \<^enum>  (c::'cs) = fn\<cdot>(sb \<^enum> c)"
  by (metis lifted.rep_eq sb_rep_abs sbgetch_insert2 well)

end


locale liftedTsynSpf =
  fixes tsynfn::"msg tsyn stream \<rightarrow> msg tsyn stream"
  assumes fn_well: "\<And>sb::'cs::{chan}\<^sup>\<Omega>. lsb_well (\<lambda>c. (tsynMsgToMStream oo tsynfn oo toTsynMsgStream)\<cdot>(sb  \<^enum>  c))"
(*<*)
begin
(*>*)

lift_definition lifted_tsyn::"'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>"
  is "\<lambda>sb. Abs_lsb (\<lambda>c. (tsynMsgToMStream oo tsynfn oo toTsynMsgStream)\<cdot>(sb \<^enum> c))"
  apply (intro cont2cont)
  by (fact fn_well)


lemma sbChGet_tsyn: "(liftedTsynSpf.lifted_tsyn tsynfn\<cdot>sb)  \<^enum>  (c::'cs) = (tsynMsgToMStream oo tsynfn oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
  by (metis (no_types, lifting) fn_well lifted_tsyn.rep_eq sb_rep_abs sbgetch_insert2)

end

sublocale liftedTsynSpf \<subseteq> liftedSpf "tsynMsgToMStream oo tsynfn oo toTsynMsgStream"
  apply(unfold_locales)
  using fn_well by blast

theorem tsynSBlen_rule_liftedSpf:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
    and f:: "M stream \<rightarrow> M stream"
  assumes "\<not>chDomEmpty TYPE('cs)" 
      and "\<And>c. k \<le> tsynLenM\<cdot>(f\<cdot>(sb \<^enum> c))"
      and "\<exists>c. tsynLenM\<cdot>(f\<cdot>(sb \<^enum> c)) = k"
      and "liftedSpf TYPE('cs) f"
    shows "tsynSBlen ((liftedSpf.lifted f)\<cdot>sb) = k"
  apply(rule tsynSBlen_rule)
  by(auto simp add: assms liftedSpf.sbChGet)

theorem tsynSBlen_rule_liftedTsynSpf:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
    and f:: "msg tsyn stream \<rightarrow> msg tsyn stream"
  assumes "\<not>chDomEmpty TYPE('cs)" 
      and "\<And>c. k \<le> tsynLen\<cdot>(f\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c)))"
      and "\<exists>c. tsynLen\<cdot>(f\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))) = k"
      and "liftedTsynSpf TYPE('cs) f"
    shows "tsynSBlen ((liftedTsynSpf.lifted_tsyn f)\<cdot>sb) = k"
  apply(rule tsynSBlen_rule)
  by (auto simp add: assms liftedTsynSpf.sbChGet_tsyn tsynLenM_def)

lemma
  assumes "liftedTsynSpf TYPE('cs) f"
  shows "tsynSBlen ((liftedTsynSpf.lifted_tsyn f)\<cdot>(def_SecureProtocol_HLR2_eve1_Output.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>(smap (map_tsyn DataBoolTupleEVENTConstr)\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf, simp_all)
  defer (* allows us to do the simps only once *)
   apply (rule def_SecureProtocol_HLR2_eve1_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve1_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

interpretation tsynSBRemDups2: liftedSpf "(tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)"
  apply(unfold_locales)
  sorry
*)



lemma
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_SecureProtocol_HLR2_eve1_Output.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn DataBoolTupleEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_SecureProtocol_HLR2_eve1_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve1_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?




definition lemma0_sb :: "'ca::{tsynchan}\<^sup>\<Omega> \<Rightarrow> 'cb::{tsynchan}\<^sup>\<Omega> \<Rightarrow> bool" where
  "lemma0_sb \<equiv> \<lambda> input output.
                  tsynSBlen (tsynSBRemDups\<cdot>input) \<ge> tsynSBlen (tsynSBRemDups\<cdot>output)"



lemma
  eve1_lemma0_sb:
  assumes "spf \<in> def_Eve1_HLR.Sps ()"
  shows "lemma0_sb sb (spf\<cdot>sb)"
  apply(auto simp add: lemma0_sb_def)
  apply(insert def_Eve1_HLR_sps_def2[OF assms])
  apply (drule_tac x=sb in meta_spec, auto)
  by (smt abs_rep_id assms cfcomp2 chdom_in def_Eve1_HLR_Input.channel_input_val_rep def_Eve1_HLR_Input.channels_chdom def_Eve1_HLR_sps_def2_pred insert_compr mem_Collect_eq singleton_conv2 somechannotempty toTsynMsgStream_tsynMsgToMStream_id
    tsynLenM_def tsynlen_remdups_boolfilter_leq tsynsbremdups_tsynsblen_ex)

lemma eve1_lemma0_general:
  assumes "spf \<in> (def_SecureProtocol_HLR2.rawSps ())"
    shows "lemma0_sb ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve1_Input.channels\<^sup>\<Omega>)
             ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve1_Output.channels\<^sup>\<Omega>)"
proof(rule eve1_pred_general_sb[OF assms])
  fix spf
  fix sb
  assume a: "spf \<in> def_Eve1_HLR.Sps ()"

  have b: "tsynSBlen (tsynSBRemDups\<cdot>sb) \<ge> tsynSBlen (tsynSBRemDups\<cdot>(spf\<cdot>sb))"
    using a eve1_lemma0_sb lemma0_sb_def by metis

  show "lemma0_sb
          (def_SecureProtocol_HLR2_eve1_Input.sbsetter\<cdot>(def_Eve1_HLR_Input.sbgetter\<cdot>sb))
          (def_SecureProtocol_HLR2_eve1_Output.sbsetter\<cdot>(def_Eve1_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb)))"
    apply(simp add: lemma0_sb_def)
    by (smt b def_SecureProtocol_HLR2_eve1_Input_tsynSBlen_setter_f def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter_f def_Eve1_HLR_Input.SB.set_get def_Eve1_HLR_Input_tsynSBlen_setter_f def_Eve1_HLR_Output.SB.set_get
        def_Eve1_HLR_Output_tsynSBlen_setter_f tsynSBRemDups_is_lifted)
qed

end

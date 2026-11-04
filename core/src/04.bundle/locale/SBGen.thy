theory SBGen

imports bundle.SB inc.Causality

begin





locale sbGen = 
 fixes lConstructor::" 'a::{pcpo,len,conc} \<Rightarrow> 'cs::{chan}  \<Rightarrow> M stream"
 assumes c_type: "\<And>a . lsb_well (lConstructor a)"
   and c_inj: "inj lConstructor"
   and c_surj: "\<And>f. lsb_well f \<Longrightarrow> f\<in>range lConstructor"
   and c_cont: "cont lConstructor"
   and c_nbelow: "\<And>x y. \<not>(x \<sqsubseteq> y) \<Longrightarrow> 
                             \<not>(lConstructor x \<sqsubseteq> lConstructor y)"
   and c_len:"\<And> a c. \<not>chDomEmpty TYPE('cs)\<Longrightarrow> #a \<le> # (lConstructor a c)"
   and c_lenex:"\<And> a. \<not>chDomEmpty TYPE('cs)\<Longrightarrow> \<exists>c.#a = #(lConstructor a c)"

begin

lemma lconstr_empty:"chDomEmpty TYPE('cs) \<Longrightarrow> lConstructor a c = \<epsilon>"
  using c_type
  by (simp add: strict_sValues_rev)


lift_definition setter::"'a \<rightarrow> 'cs\<^sup>\<Omega>" 
  is "Abs_lsb o lConstructor"
  apply(intro cont2cont)
  using c_type lsbwellI apply blast
  by (simp add: c_cont cont2cont_fun)

lemma setter_rep[simp]: "Rep_lsb (setter\<cdot>a) = lConstructor a"
  apply(simp add: setter.rep_eq)
  by (simp add: c_type lsbwellI)

lemma set_inj: "inj (Rep_cfun setter)"
  apply(rule injI)
  apply(simp add: setter.rep_eq)
  by (metis abs_rep_sb_sb c_inj injD setter_rep)

lemma set_surj: "surj (Rep_cfun setter)"
  unfolding setter.rep_eq setter_def
proof(simp add: surj_def,auto)
  fix y::"'cs\<^sup>\<Omega>"
 obtain f where f_def:"Rep_lsb y=f"
   by simp
 then obtain x where x_def:"f = lConstructor x"
    by (metis c_inj c_surj f_the_inv_into_f sbwell2fwell)
  then have "\<exists>x::'a. y = Abs_lsb (lConstructor x)" 
    by (metis Rep_lsb_inverse f_def)
  thus "\<exists>x::'a. y = Abs_cfun (Abs_lsb \<circ> lConstructor)\<cdot>x"
    using setter.rep_eq setter_def by auto 
qed

lemma set_bij: "bij (Rep_cfun setter)"
  using bij_betw_def set_inj set_surj by auto

lemma set_inv: "inv (Rep_cfun setter) = (inv lConstructor) o  Rep_lsb"
  by (simp add: c_inj set_surj surj_imp_inv_eq)

lemma cont_inv_set:"cont (inv (Rep_cfun setter))"
  apply(intro cont2cont)
   apply (simp add: set_surj)
  using c_nbelow cont2monofunE sbrep_cont by (metis setter_rep)

lift_definition getter::"'cs\<^sup>\<Omega> \<rightarrow> 'a" 
  is "(inv lConstructor) o  Rep_lsb"
  apply(intro cont2cont)
  using cont_inv_set set_inv by auto



theorem get_set[simp]: "getter\<cdot>(setter\<cdot>a) = a"
  apply (simp add: getter.rep_eq setter.rep_eq )
  using c_inj setter.rep_eq setter_rep by auto

lemma sbgetter_to_setter_lhs_eq:
assumes "setter oo f = g"
  shows "f = getter oo g"
  by (metis assms(1) cfcomp2 cfun_eqI get_set)


theorem set_get[simp]: "setter\<cdot>(getter\<cdot>sb) = sb"
  apply (simp add: getter.rep_eq setter.rep_eq )
  by (simp add: c_surj f_inv_into_f)

lemma sbgetter_to_setter_rhs_eq:
assumes "f oo setter = g"
  shows "f = g oo getter"
  by (metis assms(1) cfcomp2 cfun_eqI set_get)

lemma get_eq: "getter\<cdot>A = getter\<cdot>B \<Longrightarrow> A = B"
  by (metis set_get)

lemma setter_getch: "setter\<cdot>a \<^enum> c = lConstructor a c"
  by (simp add: sbgetch_insert2)

lemma setter_getch2[simp]: "(Rep c) \<in> chDom TYPE ('cs) \<Longrightarrow> 
    setter\<cdot>a  \<^enum>\<^sub>\<star>  c = lConstructor a (Abs (Rep c))"
  by (auto simp add: sbgetch_insert)

theorem setter_len[simp]: assumes "chDom TYPE('cs) \<noteq> {}"
  shows "#(setter\<cdot>a) = #a"
  apply (rule sblen_rule, simp add: assms)
  apply (simp add: assms setter_getch)
  apply (simp add: assms c_len)
  by (metis assms c_lenex setter_getch)

lemma getter_len[simp]: assumes "chDom TYPE('cs) \<noteq> {}"
  shows "#(getter\<cdot>sb) = #sb"
  by (metis assms set_get setter_len) 

lemma getter_conc[simp]:
  assumes c_conc: "\<And>c a1 a2. \<not>chDomEmpty TYPE('cs)\<Longrightarrow> 
                    lConstructor (a1 \<Zcat>\<Zcat> a2) c = (lConstructor a1 c) \<Zcat> (lConstructor a2 c)"
  shows "setter\<cdot>(getter\<cdot>sb1 \<Zcat>\<Zcat> getter\<cdot>sb2) = sb1 \<Zcat>\<^sup>\<Omega> sb2"
  apply(rule sb_eqI )
  apply(simp add: setter_getch)
  apply(subst c_conc, blast)
  by (metis set_get setter_getch)

lemma setter_conc[simp]: 
  assumes c_conc: "\<And>c a1 a2. \<not>chDomEmpty TYPE('cs)\<Longrightarrow> 
                    lConstructor (a1 \<Zcat>\<Zcat> a2) c = (lConstructor a1 c) \<Zcat> (lConstructor a2 c)"
  shows "getter\<cdot>(setter\<cdot>a1 \<Zcat>\<^sup>\<Omega> setter\<cdot>a2) = a1 \<Zcat>\<Zcat> a2"
  by (metis get_set getter_conc c_conc)

lemma setter_strict[simp]:"setter\<cdot>\<bottom> = \<bottom>"
  using set_get strictI by blast 

lemma getter_strict[simp]:"getter\<cdot>\<bottom> = \<bottom>" 
  using get_set strictI by blast 

lemma setter_conc2sbconc: 
  assumes "\<And>c a1 a2. \<not>chDomEmpty TYPE('cs)\<Longrightarrow> 
            lConstructor (a1 \<Zcat>\<Zcat> a2) c = (lConstructor a1 c) \<Zcat> (lConstructor a2 c)"
  shows "setter\<cdot>(s1 \<Zcat>\<Zcat> s2) = setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> setter\<cdot>s2"
  by (simp add: getter_conc[symmetric] assms)

lemma getter_sbconc2conc: 
  assumes "\<And>c a1 a2. \<not>chDomEmpty TYPE('cs)\<Longrightarrow> 
            lConstructor (a1 \<Zcat>\<Zcat> a2) c = (lConstructor a1 c) \<Zcat> (lConstructor a2 c)"
  shows "getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2) = getter\<cdot>sb1 \<Zcat>\<Zcat> getter\<cdot>sb2"
  by (metis setter_conc2sbconc get_set set_get assms)

lemma sbsetter2_eq:
  fixes f1 :: "'a \<Rightarrow> 'cs1 \<Rightarrow> M stream"
  assumes "\<And>c i. f1 i  (Abs(Rep c)) = lConstructor i c"
  and "sbGen f1"
  and "chDom TYPE ('cs1) = chDom TYPE('cs)"
shows "(sbGen.setter f1\<cdot>(s))\<star> = setter\<cdot>s"
  apply(subst sb_eqI)
  by (simp_all add: assms sbGen.setter_getch2)

lemma rename_sbsetter_eq: 
assumes ctype_f: "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and sb_gen: "sbGen f1"
    and mapping_well: "\<And>x c. f1 x (f c) = lConstructor x c"
  shows "sbRenameCh f oo sbGen.setter f1 = sbGen.setter lConstructor"
  apply(rule cfun_eqI, rule sb_eqI, simp add: ctype_f sbGen.setter_getch[OF sb_gen])
  by(rule mapping_well)

lemma rename_sbgetter_eq: 
assumes ctype_f: "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and sb_gen: "sbGen f2"
    and mapping_well: "\<And>x c. lConstructor x (f c) = f2 x c"
  shows "sbGen.getter f2 oo sbRenameCh f = sbGen.getter lConstructor"
  apply(subgoal_tac "sbRenameCh f oo sbGen.setter lConstructor = sbGen.setter f2")
  apply(metis sb_gen sbGen.sbgetter_to_setter_lhs_eq sbgetter_to_setter_rhs_eq)
  using ctype_f mapping_well sbGen.rename_sbsetter_eq sbGen_axioms sb_gen by blast

end

lemma sbgetter_eq:
  fixes f1 :: "'b::{len,conc} \<Rightarrow> 'cs1 \<Rightarrow> M stream"
  and f2 :: "'b \<Rightarrow> 'cs2 \<Rightarrow> M stream" 
  assumes "\<And>c i. f1 i  (Abs(Rep c)) = f2 i c"
  and "sbGen f1"
  and "sbGen f2"
  and "chDom TYPE ('cs1) = chDom TYPE('cs2)"
shows "sbGen.getter f1\<cdot>(sb\<star>) = sbGen.getter f2\<cdot>sb"
proof-
  obtain t where t_def:"sb = sbGen.setter f2\<cdot>t"
    by (metis assms(3) sbGen.set_get) 
  then have "(sb\<star>) = sbGen.setter f1\<cdot>t"
    apply (auto simp add: t_def)[1]
    apply(rule sb_eqI)
    apply(simp add: assms)
    by (metis assms(1,2,3,4) rep_reduction sbGen.setter_getch2)
  thus ?thesis
    by (simp add: assms sbGen.get_set t_def)
qed

lemma sbsetter_eq:
  fixes f1 :: "'b::{len,conc} \<Rightarrow> 'cs1 \<Rightarrow> M stream"
  and f2 :: "'b \<Rightarrow> 'cs2 \<Rightarrow> M stream" 
  assumes "\<And>c i. f1 i  (Abs(Rep c)) = f2 i c"
  and "sbGen f1"
  and "sbGen f2"
  and "chDom TYPE ('cs1) = chDom TYPE('cs2)"
shows "(sbGen.setter f1\<cdot>(s))\<star> = sbGen.setter f2\<cdot>s"
  apply(subst sb_eqI)
  by (simp_all add: assms sbGen.setter_getch2)

lemma simulation_connector_eq:
  assumes con_eq: "connector1 = connector2"
      and sb_gen1_in: "sbGen constrIn1"
      and sb_gen2_in: "sbGen constrIn2"
      and sb_gen1_out: "sbGen constrOut1"
      and sb_gen2_out: "sbGen constrOut2"
      and ctype_in: "\<And>c. ctype (Rep (inputMapping c)) \<subseteq> ctype (Rep c)"
      and ctype_out: "\<And>c. ctype (Rep (outputMapping c)) \<subseteq> ctype (Rep c)"
      and mapping_well_in: "\<And>x c. constrIn2 x (inputMapping c) = constrIn1 x c"
      and mapping_well_out: "\<And>x c. constrOut1 x (outputMapping c) = constrOut2 x c"
  shows "{sbRenameCh inputMapping} \<then> {sbGen.setter constrOut1 oo connector1 oo sbGen.getter constrIn1} \<then> {sbRenameCh outputMapping} =
                                      {sbGen.setter constrOut2 oo connector2 oo sbGen.getter constrIn2}"
  apply(subst seqcomp_image3[symmetric])+
  apply(subst seqcomp_assoc)+
  apply(subst con_eq)
  apply(rule seqcomp_wrapped_eq)
  apply(rule sbGen.rename_sbgetter_eq[OF sb_gen2_in ctype_in sb_gen1_in mapping_well_in])
  by(rule sbGen.rename_sbsetter_eq[OF sb_gen2_out ctype_out sb_gen1_out mapping_well_out])

lemma usimulation_component_refinement:
  assumes sps_ref: "SPS1 \<subseteq> SPS2"
      and in_con_eq: "in_connector1 = in_connector2"
      and out_con_eq: "out_connector1 = out_connector2"
      and sb_gen1_in: "sbGen constrIn1"
      and sb_gen2_in: "sbGen constrIn2"
      and sb_gen1_out: "sbGen constrOut1"
      and sb_gen2_out: "sbGen constrOut2"
      and ctype_in: "\<And>c. ctype (Rep (inputMapping c)) \<subseteq> ctype (Rep c)"
      and ctype_out: "\<And>c. ctype (Rep (outputMapping c)) \<subseteq> ctype (Rep c)"
      and mapping_well_in: "\<And>x c. constrIn2 x (inputMapping c) = constrIn1 x c"
      and mapping_well_out: "\<And>x c. constrOut1 x (outputMapping c) = constrOut2 x c"
    shows "{sbRenameCh inputMapping} \<then> {setter oo in_connector1 oo sbGen.getter constrIn1} \<then> SPS1 \<then> {sbGen.setter constrOut1 oo out_connector1 oo getter} \<then> {sbRenameCh outputMapping} \<subseteq>
                                        {setter oo in_connector2 oo sbGen.getter constrIn2} \<then> SPS2 \<then> {sbGen.setter constrOut2 oo out_connector2 oo getter}"
  apply(rule seqcomp_wrapped_subset1[OF sps_ref])
  apply(subst assoc_oo[symmetric])+
  apply(subst sbGen.rename_sbgetter_eq[OF sb_gen2_in ctype_in sb_gen1_in mapping_well_in])
  apply(subst in_con_eq, simp)
  apply(subst assoc_oo)
  apply(subst sbGen.rename_sbsetter_eq[OF sb_gen2_out ctype_out sb_gen1_out mapping_well_out])
  by(subst out_con_eq, simp)

lemma u1simulation_component_refinement:
  assumes sps_ref: "SPS1 \<subseteq> SPS2"
      and in_con_eq: "in_connector1 = in_connector2"
      and out_con_eq: "out_connector1 = out_connector2"
      and sb_gen1_in: "sbGen constrIn1"
      and sb_gen2_in: "sbGen constrIn2"
      and sb_gen1_out: "sbGen constrOut1"
      and sb_gen2_out: "sbGen constrOut2"
      and ctype_in: "\<And>c. ctype (Rep (inputMapping c)) \<subseteq> ctype (Rep c)"
      and ctype_out: "\<And>c. ctype (Rep (outputMapping c)) \<subseteq> ctype (Rep c)"
      and mapping_well_in: "\<And>x c. constrIn1 x (inputMapping c) = constrIn2 x c"
      and mapping_well_out: "\<And>x c. constrOut2 x (outputMapping c) = constrOut1 x c"
    shows "{setter oo in_connector1 oo sbGen.getter constrIn1} \<then> SPS1 \<then> {sbGen.setter constrOut1 oo out_connector1 oo getter} \<subseteq>
           {sbRenameCh inputMapping} \<then> {setter oo in_connector2 oo sbGen.getter constrIn2} \<then> SPS2 \<then> {sbGen.setter constrOut2 oo out_connector2 oo getter}  \<then> {sbRenameCh outputMapping}"
  apply(rule seqcomp_wrapped_subset2[OF sps_ref])
  apply(subst assoc_oo[symmetric])+
  apply(subst sbGen.rename_sbgetter_eq[OF sb_gen1_in ctype_in sb_gen2_in mapping_well_in])
  apply(subst in_con_eq, simp)
  apply(subst assoc_oo)
  apply(subst sbGen.rename_sbsetter_eq[OF sb_gen1_out ctype_out sb_gen2_out mapping_well_out])
  by(subst out_con_eq, simp)

lemma simulation_component_eq:
  assumes in_con_eq: "in_connector1 = in_connector2"
      and out_con_eq: "out_connector1 = out_connector2"
      and sb_gen1_in: "sbGen constrIn1"
      and sb_gen2_in: "sbGen constrIn2"
      and sb_gen1_out: "sbGen constrOut1"
      and sb_gen2_out: "sbGen constrOut2"
      and ctype_in: "\<And>c. ctype (Rep (inputMapping c)) \<subseteq> ctype (Rep c)"
      and ctype_out: "\<And>c. ctype (Rep (outputMapping c)) \<subseteq> ctype (Rep c)"
      and mapping_well_in: "\<And>x c. constrIn2 x (inputMapping c) = constrIn1 x c"
      and mapping_well_out: "\<And>x c. constrOut1 x (outputMapping c) = constrOut2 x c"
    shows "{sbRenameCh inputMapping} \<then> {setter oo in_connector1 oo sbGen.getter constrIn1} \<then> SPS \<then> {sbGen.setter constrOut1 oo out_connector1 oo getter} \<then> {sbRenameCh outputMapping} =
                                        {setter oo in_connector2 oo sbGen.getter constrIn2} \<then> SPS \<then> {sbGen.setter constrOut2 oo out_connector2 oo getter}"
  apply(rule subset_antisym)
  apply(rule usimulation_component_refinement[OF _ assms], simp)
  by(rule u1simulation_component_refinement[OF _ assms(1)[symmetric] assms(2)[symmetric] assms(4,3,6,5,7-10)], simp)

(*
lemma getterweakpredts[simp]:
  fixes fin::"'a::{conc,len} \<Rightarrow> 'in \<Rightarrow> M stream"
  fixes fout::"'b::{conc,len} \<Rightarrow> 'out \<Rightarrow> M stream"
  assumes "sbGen fin"
  and "sbGen fout"
  and "chDom TYPE('in) \<noteq> {}"
  and "chDom TYPE('out) \<noteq> {}"
  and "weakpred_ts (sb1) (sb2)"
  shows"weakpred_ts (sbGen.getter fin\<cdot>sb1) (sbGen.getter fout\<cdot>sb2)"
  using assms by(auto simp add: weakpred_ts_def sbGen.getter_len)

lemma getterstrongpredts[simp]:
  fixes fin::"'a::{len,conc} \<Rightarrow> 'in \<Rightarrow> M stream"
  fixes fout::"'b::{len,conc} \<Rightarrow> 'out \<Rightarrow> M stream"
  assumes "sbGen fin"
  and "sbGen fout"
  and "chDom TYPE('in) \<noteq> {}"
  and "chDom TYPE('out) \<noteq> {}"
  and "strongpred_ts (sb1) (sb2)"
  shows"strongpred_ts (sbGen.getter fin\<cdot>sb1) (sbGen.getter fout\<cdot>sb2)"
  using assms by(auto simp add: strongpred_ts_def sbGen.getter_len)
*)

locale sbGen_empty = 
  fixes t::"'cs::{emptychan} itself"
begin

end

sublocale sbGen_empty \<subseteq> sbGen "(\<lambda>(u::unit) cs::'cs. \<epsilon>)"
  apply(standard, simp_all)
  apply(rule injI, simp)
  by(auto simp add: lsb_well_def)

context sbGen_empty
begin

lemma setter_len_empty[simp]:"#(setter\<cdot>u) = \<infinity>"
  by simp

lemma getter_len_empty[simp]:"#(getter\<cdot>sb) = \<infinity>"
  by (simp add: len_unit_def)

end

(* TODO:
lemma empty_weakpred[simp]:"weakpred (sbGen.getter (\<lambda>(u::unit) cs::'cs1. \<epsilon>)\<cdot>sb1) 
                  (sbGen.getter (\<lambda>(u::unit) cs::'cs2. \<epsilon>)\<cdot>sb2)"
  by(simp add: weakpred_def len_unit_def)

lemma empty_strongpred[simp]:"strongpred (sbGen.getter (\<lambda>(u::unit) cs::'cs1. \<epsilon>)\<cdot>sb1) 
                  (sbGen.getter (\<lambda>(u::unit) cs::'cs2. \<epsilon>)\<cdot>sb2)"
  by(simp add: strongpred_def len_unit_def)
*)

locale sbtGen =
  fixes lConstructor::" 'a::{pcpo,len,tlen,conc} \<Rightarrow> 'cs::{tchan}  \<Rightarrow> M stream"
  assumes c_sbgen: "sbGen lConstructor"
  and c_tlen:"\<And> a c. \<not>chDomEmpty TYPE('cs)\<Longrightarrow> #\<^sub>\<surd>a \<le> #\<^sub>\<surd>(lConstructor a c)"
  and c_tlenex:"\<And> a. \<not>chDomEmpty TYPE('cs)\<Longrightarrow> \<exists>c. #\<^sub>\<surd>a = #\<^sub>\<surd>(lConstructor a c)"
begin

end

sublocale  sbtGen \<subseteq> sbGen 
  by (simp_all add: c_sbgen)

context sbtGen 
begin

theorem setter_tlen[simp]: assumes "chDom TYPE('cs) \<noteq> {}"
  shows "#\<^sub>\<surd>(setter\<cdot>a) = #\<^sub>\<surd>a"
  apply (rule sbtlen_rule, simp add: assms)
  apply (simp add: assms setter_getch)
  apply (simp add: assms c_tlen)
  by (metis assms c_tlenex setter_getch)

lemma getter_tlen[simp]: assumes "chDom TYPE('cs) \<noteq> {}"
  shows "#\<^sub>\<surd>(getter\<cdot>sb) = #\<^sub>\<surd>sb"
  by (metis assms set_get setter_tlen) 

end

lemma wellformed_sbsetter:
assumes "sbtGen f"
    and "wellformed s"
  shows "wellformed(sbGen.setter f\<cdot>s)"
  apply(rule wellformed_weakI[OF _ assms(2)])
  apply(rule weakI)
  using sbtGen.setter_tlen[OF assms(1)] by fastforce

lemma wellformed_sbgetter:
assumes "sbtGen f"
    and "wellformed sb"
  shows "wellformed (sbGen.getter f\<cdot>sb)"
  apply(rule wellformed_weakI[OF _ assms(2)])
  apply(rule weakI)
  by (metis (mono_tags) sbtGen.getter_tlen assms(1) sb_empty_eq dual_order.refl sbGen.get_set sbtGen.c_sbgen well_ex well_superEx2)

lemma wellformed_sbgetter_inv:
assumes "sbtGen f"
    and "wellformed (sbGen.getter f\<cdot>sb)"
  shows "wellformed sb"
  by (metis assms(1) assms(2) sbGen.set_get sbtGen.c_sbgen wellformed_sbsetter)

lemma getterweakpred[simp]:
  fixes fin::"'a::{conc,tlen,len} \<Rightarrow> 'in::tchan \<Rightarrow> M stream"
  fixes fout::"'b::{conc,tlen,len} \<Rightarrow> 'out::tchan \<Rightarrow> M stream"
  assumes "sbtGen fin"
  and "sbtGen fout"
  and "chDom TYPE('in) \<noteq> {}"
  and "chDom TYPE('out) \<noteq> {}"
  and "weakpred (sb1) (sb2)"
  shows"weakpred (sbGen.getter fin\<cdot>sb1) (sbGen.getter fout\<cdot>sb2)"
  using assms by(auto simp add: weakpred_def sbtGen.getter_tlen)

lemma getterstrongpred[simp]:
  fixes fin::"'a::{tlen,len,conc} \<Rightarrow> 'in::tchan \<Rightarrow> M stream"
  fixes fout::"'b::{tlen,len,conc} \<Rightarrow> 'out::tchan \<Rightarrow> M stream"
  assumes "sbtGen fin"
  and "sbtGen fout"
  and "chDom TYPE('in) \<noteq> {}"
  and "chDom TYPE('out) \<noteq> {}"
  and "strongpred (sb1) (sb2)"
  shows"strongpred (sbGen.getter fin\<cdot>sb1) (sbGen.getter fout\<cdot>sb2)"
  using assms by(auto simp add: strongpred_def sbtGen.getter_tlen)

end

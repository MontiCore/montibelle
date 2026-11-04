theory SBRenameGen

imports SBGen

begin


locale sbGen_surjrename = 
  fixes f :: "'cs2::{chan} \<Rightarrow> 'cs1::{chan}"
    and lCons::"'b::{pcpo, len,conc} \<Rightarrow> 'cs1::{chan} \<Rightarrow> M stream"
  assumes sbgen_s:"sbGen lCons"
      and surj_fs: "surj f"
      and ctype_fs: "\<And>c. ctype (Rep (f c)) = ctype (Rep c)"
begin

lemma ren_ctype [simp]:
  "sValues\<cdot>(lCons a (f c)) \<subseteq> ctype (Rep c)"
  using ctype_fs sbGen.c_type sbgen_s lsb_well_def by blast

lemma ren_sb_well[simp]:
  "lsb_well (lCons a o f)"
  by(simp add: lsb_well_def)

lemma inv_inj[simp]:"inj (inv f)"
  by (simp add: surj_fs surj_imp_inj_inv)

lemma invf_ctype [simp]:"\<And>c. ctype (Rep (inv f c)) = ctype (Rep c)"
  by (metis ctype_fs surj_fs surj_f_inv_f)

lemma ren_inj [simp]: "inj (\<lambda>a c. lCons a (f c))"
  apply(rule injI)
  by (metis (no_types, opaque_lifting) surj_fs injD sbGen.set_inj sbGen.setter_getch sb_eqI sbgen_s 
      surj_f_inv_f)

lemma ren_cont[simp]:"cont (\<lambda>b c. lCons b (f c))"
  apply(intro cont2cont)
  by (simp add: cont2cont_fun sbGen.c_cont sbgen_s)

lemma ren_not_below [simp]:assumes "\<not> x \<sqsubseteq> y"
  shows "\<not> lCons x o f \<sqsubseteq> lCons y o f"
proof -
  have f1: "\<not> lCons x \<sqsubseteq> lCons y"
    by(rule sbGen.c_nbelow, auto simp add: assms sbgen_s)
  obtain c where "\<not>lCons x c \<sqsubseteq> lCons y c"
    by (meson f1 fun_belowI)
  hence "\<not> lCons x (f ((inv f)c)) \<sqsubseteq> lCons y (f ((inv f)c))"
    by (simp add: surj_fs surj_f_inv_f)
  thus ?thesis
    using fun_belowD by fastforce 
qed

lemma empty_iff:  "chDomEmpty TYPE('cs2) \<longleftrightarrow> chDomEmpty TYPE('cs1)"
  by (metis dom2ctypeempty dom2ctypenempty invf_ctype)

lemma ren_len [simp]: assumes "\<not>chDomEmpty TYPE('cs2)"
  shows "#a \<le> #(lCons a (f c))"
  using empty_iff assms sbGen_def sbgen_s by blast

lemma ren_lenex [simp]: assumes "\<not>chDomEmpty TYPE('cs2)"
  shows "\<exists>c. #a = #(lCons a (f c))"
  by (metis UNIV_I assms local.empty_iff rangeE sbGen.c_lenex sbgen_s surj_fs)

definition rename:: "'cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>" where
"rename \<equiv> sbRenameCh f"

definition invRename:: "'cs2\<^sup>\<Omega> \<rightarrow> 'cs1\<^sup>\<Omega>" where
"invRename \<equiv> sbRenameCh (inv f)"


lemma rename2id:"invRename oo rename = ID"
  apply(simp add: rename_def invRename_def)
  apply(rule sbrename_id_surj)
  apply (simp add: surj_fs)
  using ctype_fs by blast

text\<open>@{const invRename} range is UNIV of the small \gls{sb} domain.\<close>
lemma invrename_surj[simp]:"surj (Rep_cfun invRename)"
  apply(auto simp add: surj_def)[1]
  apply(rule_tac x="rename\<cdot>y" in exI)
  by (metis ID1 cfcomp2 rename2id)

lemma rename_inj[simp]:"inj (Rep_cfun rename)"
  apply(rule injI)
  by (metis ID1 cfcomp2 rename2id)

lemma rename_strict [simp]:"rename\<cdot>\<bottom> = \<bottom>"
  by (metis ctype_fs order_refl rename_def sbbot_getch sbconv_eq sbrenamech_rep sbtypecast_rep)

lemma invRename_strict [simp]:"invRename\<cdot>\<bottom> = \<bottom>"
  by (metis ID1 cfcomp2 rename2id strictI)

lemma rename_sbconc: "rename\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2) = (rename\<cdot>sb1) \<Zcat>\<^sup>\<Omega> (rename\<cdot>sb2)"
  apply (rule sb_eqI)
  by (simp add: rename_def ctype_fs)

lemma invrename_sbconc: "invRename\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2) = (invRename\<cdot>sb1) \<Zcat>\<^sup>\<Omega> (invRename\<cdot>sb2)"
  apply (rule sb_eqI)
  by (simp add: invRename_def)

end


locale sbGen_rename = 
  fixes f :: "'cs2::{chan} \<Rightarrow> 'cs1::{chan}"
    and lCons::"'b::{pcpo, len,conc} \<Rightarrow> 'cs1::{chan} \<Rightarrow> M stream"
  assumes sbgen:"sbGen lCons"
      and bij_f: "bij f"
      and ctype_f: "\<And>c. ctype (Rep (f c)) = ctype (Rep c)"
begin


lemma ren_surj[simp]: assumes "lsb_well sb"
  shows "sb \<in> range (\<lambda>a c. lCons a (f c))"
proof -
  have "lsb_well (sb  o(inv f))"
    by (metis assms bij_def bij_f comp_def ctype_f lsb_well_def surj_f_inv_f)
  obtain a where "lCons a = (sb  o(inv f))"
    by (meson \<open>lsb_well ((sb::'cs2 \<Rightarrow> M stream) \<circ> inv (f::'cs2 \<Rightarrow> 'cs1))\<close> f_inv_into_f sbGen.c_surj sbgen)
  hence "\<And>c. lCons a (f c) = sb c"
    by (simp add: bij_f bij_is_inj)
  hence "sb = (\<lambda>c. lCons a (f c))"
    by simp
  thus ?thesis
    by auto
qed


end

sublocale sbGen_rename \<subseteq> sbGen_surjrename
  by (simp add: bij_betw_imp_surj_on bij_f ctype_f sbGen_surjrename.intro sbgen)


sublocale sbGen_rename \<subseteq> sbGen "\<lambda>b. (lCons b) o f"
  apply(standard)
  using o_def apply auto[7]
  by(simp add: o_def)+



context sbGen_rename
begin

lemma rename2id2:"rename oo invRename = ID"
  apply(simp add: rename_def invRename_def)
  apply(rule sbrename_id_inj)
  apply (simp add: bij_f bij_is_inj) 
  by simp
  
lemma rename_setter_eq[simp]:  "rename\<cdot>(sbGen.setter lCons\<cdot>b) = setter\<cdot>b"
  apply(rule sb_eqI, simp add: rename_def)
  apply(subst sbrenamech_getch, simp add: ctype_f)
  by (simp add: sbGen.setter_getch sbgen setter_getch)

lemma invrename_setter_eq[simp]:  "invRename\<cdot>(setter\<cdot>b) = (sbGen.setter lCons\<cdot>b)"
  apply(rule sb_eqI, simp add: invRename_def)
  by (simp add: sbGen.setter_getch2 sbgen setter_getch surj_fs surj_f_inv_f)

lemma rename_getter[simp]: "getter\<cdot>(rename\<cdot>sb) = sbGen.getter lCons\<cdot>sb"
  by (metis get_set rename_setter_eq sbGen.set_get sbgen)

lemma invrename_getter[simp]: "sbGen.getter lCons\<cdot>(invRename\<cdot>sb) = getter\<cdot>sb"
  by (metis invrename_setter_eq sbGen.get_set sbgen_s set_get)

end



lemma invrename_eq[simp]:
  fixes f1::"'cs1 \<Rightarrow> 'cs"
  and f2::"'cs2 \<Rightarrow> 'cs"
  assumes "sbGen_rename f1 lCons1"
  and "sbGen_rename f2 lCons2"
  and "chDom TYPE('cs1) = chDom TYPE ('cs2)"
  and "\<And>c. f1 (Abs (Rep c)) = f2 c"
shows"sbGen_surjrename.invRename f1\<cdot>(sb\<star>) = sbGen_surjrename.invRename f2\<cdot>(sb)"
  apply(rule sb_eqI,simp add: assms sbgetch_insert)
  apply(subst sbGen_surjrename.invRename_def[of f1 lCons1])
  using assms(1) sbGen_rename_def[of f1 lCons1] apply(simp add: sbGen_surjrename_def bij_def)
  apply(subst sbGen_surjrename.invRename_def[of f2 lCons2])
  using assms(2) sbGen_rename_def[of f2 lCons2] apply(simp add: sbGen_surjrename_def bij_def)
  apply(subst sbrenamech_rep)
   apply (metis \<open>sbGen_rename (f1::'cs1 \<Rightarrow> 'cs) (lCons1::'a \<Rightarrow> 'cs \<Rightarrow> M stream) \<equiv> sbGen lCons1 
\<and> bij f1 \<and> (\<forall>c::'cs1. ctype (Rep (f1 c)) = ctype (Rep c))\<close> assms(1) bij_inv_eq_iff equalityE)
  apply(subst sbrenamech_rep)
   apply (metis \<open>sbGen_rename (f2::'cs2 \<Rightarrow> 'cs) (lCons2::'b \<Rightarrow> 'cs \<Rightarrow> M stream) \<equiv> sbGen lCons2 \<and>
 bij f2 \<and> (\<forall>c::'cs2. ctype (Rep (f2 c)) = ctype (Rep c))\<close> assms(2) bij_inv_eq_iff equalityE) 
  apply(auto simp add: sbgetch_insert assms)[1]
  subgoal
proof -
  fix c :: 'cs
  assume a1: "Rep (inv f1 c) \<in> chDom (TYPE('cs2)::'cs2 itself)"
  have "bij f1"
    by (metis sbGen_rename_def assms(1))
  then show "Rep_lsb sb (Abs (Rep (inv f1 c))) = Rep_lsb sb (inv f2 c)"
    using a1 by (metis UNIV_I sbGen_rename_def[of f2 lCons2] abs_rep_id assms(2) 
       assms(4) bij_betw_inv_into_left bij_betw_inv_into_right rep_reduction)
qed
  using cnotempty_rule notcdom_empty apply auto[1]
  by (metis UNIV_I sbGen_rename_def[of f1 lCons1] sbGen_rename_def[of f2 lCons2]
       assms bij_betw_inv_into_left bij_pointE rep_reduction)


lemma rename_eq[simp]:
  fixes f1::"'cs1 \<Rightarrow> 'cs"
  and f2::"'cs2 \<Rightarrow> 'cs"
  assumes "sbGen_rename f1 lCons1"
  and "sbGen_rename f2 lCons2"
  and "chDom TYPE('cs1) = chDom TYPE ('cs2)"
  and "\<And>c. f1 (Abs (Rep c)) = f2 c"
shows"sbGen_surjrename.rename f1\<cdot>(sb)\<star> = sbGen_surjrename.rename f2\<cdot>(sb)"
  apply(rule sb_eqI,simp add: assms sbgetch_insert)
  apply(subst sbGen_surjrename.rename_def[of f1 lCons1])
  using assms(1) sbGen_rename_def[of f1 lCons1] apply(simp add: sbGen_surjrename_def bij_def)
  apply(subst sbGen_surjrename.rename_def[of f2 lCons2])
  using assms(2) sbGen_rename_def[of f2 lCons2] apply(simp add: sbGen_surjrename_def bij_def)
  apply(subst sbrenamech_rep)
  using assms(1) sbGen_rename.ctype_f apply auto[1]
  apply(subst sbrenamech_rep)
  using assms(2) sbGen_rename.ctype_f apply auto[1]
  by(auto simp add: sbgetch_insert assms)
 





end
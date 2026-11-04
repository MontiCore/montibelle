theory SBERenameGen

imports SBEGen

begin

locale sbeGen_surjrename = 
  fixes f :: "'cs2::{chan,finite} \<Rightarrow> 'cs1::{chan,finite}"
    and lCons::"'a::countable \<Rightarrow> 'cs1::{chan,finite} \<Rightarrow> M"
  assumes sbegen_s:"sbeGen lCons"
      and surj_fs: "surj f"
      and ctype_fs: "\<And>c. ctype (Rep (f c)) = ctype (Rep c)"
      and not_empty_s: "chDom TYPE('cs1) \<noteq> {}"
begin

lemma ren_ctype [simp]:
  " \<not>chDomEmpty TYPE ('cs1) \<Longrightarrow> (lCons a (f c)) \<in> ctype (Rep c)"
  using ctype_fs sbeGen.c_well sbegen_s by blast

lemma inv_inj[simp]:"inj (inv f)"
  by (simp add: surj_fs surj_imp_inj_inv)

lemma invf_ctype [simp]:"\<And>c. ctype (Rep (inv f c)) = ctype (Rep c)"
  by (metis ctype_fs surj_fs surj_f_inv_f)

lemma ren_inj : "inj (\<lambda>a c. lCons a (f c))"
  apply (rule injI)
  apply (insert sbeGen.set_inj [of lCons])
  apply (simp add: sbegen_s)
  apply (subst injD [of "(sbeGen.setter lCons)" x y for x y])
  apply simp_all
  apply (rule sbe_eqI)
  apply (simp add: sbeGen.setter.rep_eq sbegen_s )
  apply (rule impI, rule fun_eqI)
  by (metis surj_f_inv_f surj_fs) 

lemma empty_iff:  "chDomEmpty TYPE('cs2) \<longleftrightarrow> chDomEmpty TYPE('cs1)"
  by (metis dom2ctypeempty dom2ctypenempty invf_ctype)

definition rename:: "'cs1\<^sup>\<surd> \<Rightarrow> 'cs2\<^sup>\<surd>" where
"rename \<equiv> sbeRenameCh f"

definition invRename:: "'cs2\<^sup>\<surd> \<Rightarrow> 'cs1\<^sup>\<surd>" where
"invRename \<equiv> sbeRenameCh (inv f)"


lemma rename2id:"invRename o rename = id"
  apply(simp add: rename_def invRename_def)
  apply(rule sberename_id_surj)
  apply (simp add: surj_fs)
  using ctype_fs apply blast
  by (simp add: not_empty_s)
 
text\<open>@{const invRename} range is UNIV of the small \gls{sb} domain.\<close>
lemma invrename_surj[simp]:"surj (invRename)"
  apply(auto simp add: surj_def)[1]
  apply(rule_tac x="rename y" in exI)
  by (simp add: pointfree_idE rename2id)

lemma rename_surj[simp]:"inj (rename)"
  apply(rule injI)
  by (metis pointfree_idE rename2id)

end


locale sbeGen_rename = 
  fixes f :: "'cs2::{chan,finite} \<Rightarrow> 'cs1::{chan,finite}"
    and lCons::"'a::countable \<Rightarrow> 'cs1::{chan,finite} \<Rightarrow> M"
  assumes sbegen:"sbeGen lCons"
      and bij_f: "bij f"
      and ctype_f: "\<And>c. ctype (Rep (f c)) = ctype (Rep c)"
      and not_empty: "chDom TYPE('cs1) \<noteq> {}"
begin


lemma ren_surj[simp]: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range (\<lambda>a c. lCons a (f c))"
proof -
  have "sbElem_well (Some (sbe  o (inv f)))"
    apply (insert assms)
    apply (simp,rule allI)
    by (metis bij_f bij_inv_eq_iff ctype_f)
  then obtain a where "lCons a = (sbe  o(inv f))"
    apply (simp add: comp_def not_empty)
    apply (insert sbeGen.c_surj [of lCons])
    apply (simp add: sbegen not_empty)
    by (meson f_inv_into_f)
  hence "\<And>c. lCons a (f c) = sbe c"
    by (simp add: bij_f bij_is_inj)
  hence "sbe = (\<lambda>c. lCons a (f c))"
    by simp
  thus ?thesis
    by auto
qed


end

sublocale sbeGen_rename \<subseteq> sbeGen_surjrename
  by (simp add: bij_betw_imp_surj_on bij_f ctype_f sbeGen_surjrename.intro sbegen not_empty)

sublocale sbeGen_rename \<subseteq> sbeGen "\<lambda>b. (lCons b) o f"
  apply (standard)
  apply (rule allI)
  apply (simp_all)
  using local.empty_iff ren_ctype apply blast
  apply (simp_all add: comp_def)
  using ren_inj apply blast
  apply (simp add: local.empty_iff)
  using sbeGen.c_empty sbegen by blast

context sbeGen_rename
begin

lemma rename2id2:"rename o invRename = id"
  apply(simp add: rename_def invRename_def)
  apply(rule sberename_id_inj)
  apply (simp add: bij_f bij_is_inj)
  using invf_ctype apply blast
  using local.empty_iff not_empty by blast 
  
lemma rename_setter_eq[simp]: "rename (sbeGen.setter lCons b) = setter b"
  apply (rule sbe_eqI,simp add: rename_def)
  apply (simp add: sberenamech_rep ctype_fs setter.rep_eq not_empty local.empty_iff)
  apply (rule fun_eqI)
  by (simp add: sbegetch_insert sbegen sbeGen.setter.rep_eq not_empty)

lemma invrename_setter_eq[simp]:  "invRename (setter b) = (sbeGen.setter lCons b)"
  apply(rule sbe_eqI, simp add: invRename_def)
  apply (simp add: sberenamech_rep ctype_fs setter.rep_eq not_empty local.empty_iff)
  apply (simp add: sbegetch_insert sbegen sbeGen.setter.rep_eq not_empty)
  apply (rule fun_eqI)
  by (simp add: surj_f_inv_f surj_fs)

lemma rename_getter[simp]: "getter (rename sb) = sbeGen.getter lCons sb"
  by (metis get_set rename_setter_eq sbeGen.set_get sbegen)

lemma invrename_getter[simp]: "sbeGen.getter lCons (invRename sb) = getter sb"
  by (metis invrename_setter_eq sbeGen.get_set sbegen_s set_get)

end

lemma sbe_invrename_eq[simp]:
  fixes f1::"'cs1::{chan,finite} \<Rightarrow> 'cs::{chan,finite}"
  and f2::"'cs2::{chan,finite} \<Rightarrow> 'cs"
  assumes "sbeGen_rename f1 lCons1"
  and "sbeGen_rename f2 lCons2"
  and "chDom TYPE('cs1) = chDom TYPE ('cs2)"
  and "\<And>c. f1 (Abs (Rep c)) = f2 c"
shows"sbeGen_surjrename.invRename f1 (sbeConvert sbe) = sbeGen_surjrename.invRename f2 (sbe)"
  apply (rule sbe_eqI)
  apply (subst sbeGen_surjrename.invRename_def[of f1 lCons1])
  apply (meson assms(1) bij_betw_imp_surj_on sbeGen_rename_def sbeGen_surjrename_def)
  apply (subst sbeGen_surjrename.invRename_def[of f2 lCons2])
  apply (meson assms(2) bij_betw_imp_surj_on sbeGen_rename_def sbeGen_surjrename_def)
  apply (subst sberenamech_rep)
  apply (insert  sbeGen_rename_def [of f1 lCons1])
  apply (metis assms(1) dom2ctypeempty dom2ctypenempty)
  apply (metis assms(1) bij_inv_eq_iff order_refl)
  apply (subst sberenamech_rep)
  apply (insert  sbeGen_rename_def [of f2 lCons2])
  apply (metis assms(2) dom2ctypeempty dom2ctypenempty)
  apply (metis assms(2) bij_inv_eq_iff order_refl)
  apply simp
  apply (rule fun_eqI)
  apply (subst sbegetch_insert)
  apply (metis assms(1) chdom_in dom2ctypeempty dom2ctypenempty)
  apply (subst sbegetch_insert)
  apply (metis assms(2) chdom_in dom2ctypeempty dom2ctypenempty)
  apply(simp add: sbeConvert.rep_eq )
  apply (intro impI conjI)
  apply (metis assms(1) dom2ctypeempty dom2ctypenempty)
  apply (subst sbegetch_insert)
  using assms(3) chdom_in apply blast
  by (metis assms(1) assms(2) assms(3) assms(4) bij_inv_eq_iff chdom_in rep_reduction)
  

lemma sbe_rename_eq[simp]:
  fixes f1::"'cs1::{chan,finite} \<Rightarrow> 'cs::{chan,finite}"
  and f2::"'cs2::{chan,finite} \<Rightarrow> 'cs"
  assumes "sbeGen_rename f1 lCons1"
  and "sbeGen_rename f2 lCons2"
  and "chDom TYPE('cs1) = chDom TYPE ('cs2)"
  and "\<And>c. f1 (Abs (Rep c)) = f2 c"
  shows"sbeConvert (sbeGen_surjrename.rename f1 (sb)) = sbeGen_surjrename.rename f2 (sb)"
  apply (rule sbe_eqI)
  apply(simp add: sbeConvert.rep_eq)
  apply (intro impI conjI)
  apply (metis sbe_emptyiff)
  apply(subst sbeGen_surjrename.rename_def[of f1 lCons1])
  apply (meson assms(1) bij_betw_imp_surj_on sbeGen_rename_def sbeGen_surjrename_def)
  apply (subst sbeGen_surjrename.rename_def[of f2 lCons2])
  apply (meson assms(2) bij_betw_imp_surj_on sbeGen_rename_def sbeGen_surjrename_def)
  apply(subst sbegetch_insert)
  apply (metis assms(3) chdom_in)
  apply (subst sberenamech_rep)
  apply (insert  sbeGen_rename_def [of f1 lCons1])
  apply (metis assms(1))
  apply (metis assms(1) order_refl)
  apply (subst sberenamech_rep)
  apply (insert  sbeGen_rename_def [of f2 lCons2])
  apply (metis assms(2))
  apply (metis assms(2) order_refl)
  apply simp
  apply (rule fun_eqI)
  by (simp add: assms(4))

end
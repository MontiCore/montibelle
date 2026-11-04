theory Codegen

imports HOLCF
keywords "setup_domain" :: thy_decl
begin
default_sort type

ML_file\<open>HOLCFcodegen.ml\<close>

attribute_setup ccode =
 \<open>Scan.succeed (Thm.declaration_attribute (cnc)) \<close> "make non cont codelemma from cfun codelemma"

attribute_setup ccodeAbs =
 \<open>Scan.succeed (Thm.declaration_attribute (sbcnc)) \<close> "make non cont codelemma from abstract cfun codelemma"




definition iterate_nc :: "nat \<Rightarrow> ('a::cpo \<rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
"iterate_nc a b c = iterate a\<cdot>b\<cdot>c"

lemma[code]:"iterate_nc 0 a b = b" and
     [code]:"iterate_nc (Suc x) a b = (iterate_nc x a (a\<cdot>b))"
  apply (simp add: iterate_nc_def)+
  using iterate_Suc2 by auto

lemma iterate_fix_eq:
  assumes fixed: "f\<cdot>(iterate x\<cdot>f\<cdot>\<bottom>) = iterate x\<cdot>f\<cdot>\<bottom>"
  shows "(\<Squnion>x::nat. iterate x\<cdot>f\<cdot>\<bottom>) = iterate x\<cdot>f\<cdot>\<bottom>"
proof-
  have"\<And>z. f\<cdot>z = z \<Longrightarrow> iterate x\<cdot>f\<cdot>\<bottom> \<sqsubseteq> z"
    using fix_least iterate_below_fix rev_below_trans by blast
  then show ?thesis
    by (metis (no_types, lifting) fix_least_below fixed iterate_below_fix lub_chain_maxelem po_eq_conv)
qed


end
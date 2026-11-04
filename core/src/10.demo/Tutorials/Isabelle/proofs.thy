
theory proofs

imports definitions
begin


lemma [simp]:"doublef = double"
  apply(subst fun_eq_iff,rule)
  by(induct_tac x,simp_all)

lemma [simp]:"doublep = double"
  apply(subst fun_eq_iff,rule)
  by(induct_tac x,simp_all)

lemma "doublef = doublep"
  by simp


lemma "0<m \<Longrightarrow> \<exists>n. (Suc n) = m"
  by(rule_tac exI [where x= "m-1"],simp) 


lemma "\<And>m. 0<m \<Longrightarrow> \<exists>n. (Suc n) = m"
  by(rule_tac x="m-1" in exI,simp) 



lemma assumes S_def:"S = S\<union>{x+1 | x.  x\<in>S}"
      and "(0::nat) \<in> S"
    shows "S= UNIV"
  apply(auto)
  apply(induct_tac x,simp add: assms(2))
  text\<open>Here, \<open>apply(simp add: S_def)\<close> would not work, because it would run infinetely long to
"compute" S. Instead \<open>subst\<close> can be used to unfold S once\<close>
  apply(subst S_def)
  by simp

lemma assumes" n = m"
      and "m = n"
    shows "P n \<Longrightarrow> P m"
  text\<open>similarly, the addition of both assumptions to \<open>simp\<close> using \<open>apply(simp add: assms)\<close>will 
always exchange n with m and vice versa, thus never finish the proof.\<close>
  by(subst assms,simp)



  

lemma 
  fixes n::nat
  assumes "n > 0" and n_bot: "n < 0"
  shows "P ln"
proof -
  have "easyFormular" 
    using n_bot by auto
  from this have name: "complexFormular" 
    using n_bot by auto
  hence "evenMoreComplex" 
    using n_bot by auto
  show ?thesis
    using name n_bot by auto 
qed
  
  
  

lemma 
  fixes n::nat
  assumes "n > 0" and n_bot: "n < 0" 
  shows "P n"
proof (cases "n = 0")
  case True
  then show ?thesis 
    using n_bot by auto
next
  case False
  have "0 < n" 
    using False leI by blast
  obtain m where n_def: "Suc n = m"
    using \<open>n < 0\<close> by simp 
  then show ?thesis 
    using n_bot by auto
qed

lemma 
  fixes n::nat
  assumes "n > 0" and n_bot: "n < 0"
  shows "P n"
proof (induction n)
  case 0
  then show ?case 
    using n_bot by auto
next
  case (Suc n)
  then show ?case 
    using n_bot by auto
qed
  
 
  
lemma assumes "monofun f" 
   shows"monofun (\<lambda>n. f n)" (is "monofun ?F")
proof (rule monofunI)
  fix x::"'a"
  fix y::"'a"

  assume "x\<sqsubseteq> y"
  
  thus "?F x \<sqsubseteq> ?F y"
    using assms monofun_def by auto 
qed      
  
end
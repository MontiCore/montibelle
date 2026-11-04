theory hwl_tsynSBRemDups
  imports
    hwl_core_ext
    TsynSBFunctionExtension
    bundle.TsynSBFunction
begin

lemma tsynRemDups_sValues_se_h:
  "sValues\<cdot>(sscanlAOne tsynRemDups_h state\<cdot>s) \<subseteq> sValues\<cdot>(tsynRemDups\<cdot>s) \<union> {\<sim>}"
proof -
  have tsyn_def: "tsynRemDups\<cdot>s = sscanlAOne tsynRemDups_h \<sim>\<cdot>s"
    by (simp add: tsynRemDups_def)
  
  show ?thesis
  proof (induction s arbitrary: state)
    case adm
    then show ?case
      unfolding subset_iff
      apply (intro adm_all adm_imp SetPcpo.adm_in2 Cpo.adm_const)
      using adm_cmp apply force 
      apply (simp add: SetPcpo.adm_in2)
      proof-
          fix t :: "'a tsyn"
          show "adm (\<lambda>x::'a tsyn stream. t = \<sim> \<or> t \<in> sValues\<cdot>(tsynRemDups\<cdot>x))"
          proof (cases "t = \<sim>")
            case True
            then show ?thesis
              by simp
          next
            case False
            then show ?thesis
              apply (simp add: SetPcpo.adm_in2)
              using adm_cmp adm_in2 by fastforce
          qed
      qed
  next
    case bottom
      have sscanl_eps: "sscanlAOne tsynRemDups_h state\<cdot>\<epsilon> = \<epsilon>" unfolding sscanlAOne_def
        by simp
      
      have tsyn_eps: "tsynRemDups\<cdot>\<epsilon> = \<epsilon>"  unfolding tsynRemDups_def sscanlAOne_def
        by (simp add: tsynRemDups_def)
      
      have svalues_eps: "sValues\<cdot>\<epsilon> = {}"
        by (simp add:)

    then show ?case
      by (simp add: sscanl_eps) 
  next
    case (step a s)
      have step_eq1: "sscanlAOne tsynRemDups_h state\<cdot>(\<up>a \<Zcat> s) = 
            sup' (snd (tsynRemDups_h state a)) \<Zcat>\<Zcat> 
            sscanlAOne tsynRemDups_h (fst (tsynRemDups_h state a))\<cdot>s"
        by (simp add: sscanlaone_step)
      
      have step_eq2: "tsynRemDups\<cdot>(\<up>a \<Zcat> s) = 
            sup' (snd (tsynRemDups_h \<sim> a)) \<Zcat>\<Zcat> 
            sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s"
        by (simp add: tsynRemDups_def sscanlaone_step)
      
      have svalues_conc1: "sValues\<cdot>(sscanlAOne tsynRemDups_h state\<cdot>(\<up>a \<Zcat> s)) = 
            sValues\<cdot>(sup' (snd (tsynRemDups_h state a))) \<union> 
            sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h state a))\<cdot>s)"
        by (simp add: sscanlaone_step)


      then show ?case 
        apply (cases a; auto)
        apply (metis (no_types, lifting) Un_commute
            conc_stream_def fst_eqD
            tsynRemDups_h.simps(1)
            insert_is_Un insert_subset
            mk_disjoint_insert snd_eqD srcdups_dom
            srcdups_dom_h step step_eq2
            tsynRemDups_def)
        using step_eq2 apply fastforce
        using step_eq2 apply auto[1]
        using step_eq2 by force  
    qed
  qed

lemma tsynRemDups_sValues_se:
  "sValues\<cdot>(tsynRemDups\<cdot>s) \<subseteq>  sValues\<cdot>s \<union> {\<sim>} " 
proof (induction s )
  case adm
  then show ?case 
    apply auto 
    unfolding subset_iff
      apply (intro adm_all adm_imp SetPcpo.adm_in2 Cpo.adm_const)
    using adm_cmp apply force
    apply (simp add: SetPcpo.adm_in2)
    done
next
  case bottom
  then show ?case unfolding tsynRemDups_def sscanlAOne_def by simp
next
  case (step a s)
    have step_eq: "tsynRemDups\<cdot>(\<up>a \<Zcat> s) = 
          sup' (snd (tsynRemDups_h \<sim> a)) \<Zcat>\<Zcat> 
          sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s"
      by (simp add: tsynRemDups_def sscanlaone_step) 
    
    have svalues_conc: "sValues\<cdot>(tsynRemDups\<cdot>(\<up>a \<Zcat> s)) = 
          sValues\<cdot>(sup' (snd (tsynRemDups_h \<sim> a))) \<union> 
          sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s)"
      by (simp add: step_eq)
    
    
    have part2: "sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s) \<subseteq> {\<sim>} \<union> sValues\<cdot>s" using step tsynRemDups_sValues_se_h
      by blast 
    
    have "sValues\<cdot>s \<subseteq> sValues\<cdot>(\<up>a \<Zcat> s)"
      by (auto)
    then have part2': "sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s) \<subseteq> {\<sim>} \<union> sValues\<cdot>(\<up>a \<Zcat> s)"
      using part2 by blast
    

      have step_eq: "tsynRemDups\<cdot>(\<up>a \<Zcat> s) = 
          sup' (snd (tsynRemDups_h \<sim> a)) \<Zcat> 
          sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s"
        by (simp add: tsynRemDups_def sscanlaone_step)  

      have step_eq2: "sscanlAOne tsynRemDups_h state\<cdot>(\<up>a \<Zcat> s) = 
          sup' (snd (tsynRemDups_h state a)) \<Zcat>\<Zcat> 
          sscanlAOne tsynRemDups_h (fst (tsynRemDups_h state a))\<cdot>s"
      by (simp add: sscanlaone_step)

    have part1: "sValues\<cdot>(sup' (snd (tsynRemDups_h \<sim> a))) \<subseteq> {\<sim>} \<union> sValues\<cdot>(\<up>a \<Zcat> s)"
    proof -
      have "snd (tsynRemDups_h \<sim> a) \<in> {a, \<sim>}"
        by (cases a) (auto)
      then have "sValues\<cdot>(sup' (snd (tsynRemDups_h \<sim> a))) \<subseteq> {a, \<sim>}"
        by simp
      also have "{a, \<sim>} \<subseteq> {\<sim>} \<union> sValues\<cdot>(\<up>a \<Zcat> s)"
        by simp
      finally show ?thesis .
    qed
    
    have part2: "sValues\<cdot>(tsynRemDups\<cdot>s) \<subseteq> {\<sim>} \<union> sValues\<cdot>s"
      using step by auto
    
    have "sValues\<cdot>s \<subseteq> sValues\<cdot>(\<up>a \<Zcat> s)"
      by auto
    then have part2': "sValues\<cdot>(tsynRemDups\<cdot>s) \<subseteq> {\<sim>} \<union> sValues\<cdot>(\<up>a \<Zcat> s)"
      using part2 by blast

    have "sValues\<cdot>(\<up>(snd (tsynRemDups_h \<sim> a)))\<union> sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s) =
           sValues\<cdot>(\<up>(snd (tsynRemDups_h \<sim> a)) \<Zcat> sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s)"
      by auto

    have "sValues\<cdot>(\<up>(snd (tsynRemDups_h \<sim> a))) \<subseteq> sValues\<cdot>(\<up>a \<Zcat> s) \<union> {\<sim>}"
      using part1 by blast

    have " sValues\<cdot>(tsynRemDups\<cdot>(s::'a tsyn stream)) \<subseteq> sValues\<cdot>s \<union> {\<sim>}"
      using step by blast 

    show ?case 
      apply (subst step_eq)
      using
        \<open>sValues\<cdot>(\<up>(snd (tsynRemDups_h \<sim> (a::'a tsyn)))) \<subseteq> sValues\<cdot>(\<up>a \<Zcat> (s::'a tsyn stream)) \<union> {\<sim>}\<close>
        part2 tsynRemDups_sValues_se_h
      by fastforce
      
  qed

definition "tsynSBRemDups_raw" :: "'cs::{tsynchan}\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<Omega>" where
  "tsynSBRemDups_raw \<equiv> \<lambda>sb. Abs_lsb (\<lambda>c. (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb\<^enum>c))"

lemma cType_not_TNone_tsynchan:
  assumes "chDom TYPE ('cs) \<noteq> {}"
  shows "cType (Rep (c::'cs::{tsynchan})) \<noteq> TNone"
proof
  assume "cType (Rep c) = TNone"
  then have "ctype (Rep c) = {}"
    by (metis cMsg.simps cMsgt.simps(4) cType.elims ctype_empty_iff)
  moreover from assms have "ctype (Rep c) \<noteq> {}"
    using dom2ctypenempty by blast
  ultimately show False by contradiction
qed

lift_definition tsynSBRemDups :: "'cs::{tsynchan}\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" is
"tsynSBRemDups_raw"
  apply (simp add: tsynSBRemDups_raw_def)
  apply (intro cont2cont)
  apply (simp add: lsb_well_def)
proof -
  fix sb :: "'cs::{tsynchan}\<^sup>\<Omega>"
  have sub1: "chDom TYPE('cs::{tsynchan}) = {} \<Longrightarrow> \<forall>c::'cs::{tsynchan}. sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) \<subseteq> ctype (Rep c)" 
    using Channel.dom2ctypeempty tsynSBRemDups_raw_sValues_subset_ctype_chDom_empty 
    by blast
  have sub2: "chDom TYPE('cs::{tsynchan}) \<noteq> {} \<Longrightarrow> \<forall>c::'cs::{tsynchan}. sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) \<subseteq> ctype (Rep c)" 
    using tsynSBRemDups_raw_sValues_subset_ctype_chDom_not_empty by blast
  show "\<forall>c::'cs.
          sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))))
            \<subseteq> ctype (Rep c)"
    using sub1 sub2 by blast
qed

lemma tsynSBRemDups_rule:
  assumes "\<And>c. (sbo \<^enum> c) = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sbi \<^enum> c)"
  shows "tsynSBRemDups\<cdot>sbi = sbo"
proof (rule sb_eqI) 
  fix c
  show "(tsynSBRemDups\<cdot>sbi) \<^enum> c = sbo \<^enum> c"
  proof -
    have "(tsynSBRemDups\<cdot>sbi) \<^enum> c = sbGetCh c\<cdot>(tsynSBRemDups\<cdot>sbi)"
      by simp
    
    moreover have "... = sbGetCh c\<cdot>(tsynSBRemDups_raw sbi)"
      by (simp add: tsynSBRemDups.rep_eq)
    
    moreover have "... = Rep_lsb (tsynSBRemDups_raw sbi) c"
      using sbgetch_insert2 by blast
    
    moreover have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sbi \<^enum> c)"
      by (metis (no_types, lifting) ext
          abs_rep_sb_sb assms sbgetch_insert2
          tsynSBRemDups_raw_def)
    
    moreover have "... = sbo \<^enum> c"
      using assms by presburger
    
    ultimately show ?thesis
      by (metis)
  qed
qed


lemma tsynSBRemDups_raw_lsb_well:
  shows "lsb_well (\<lambda>(c::'cs::tsynchan). (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c))"
  unfolding lsb_well_def
proof (intro allI)
  fix c :: 'cs
  show "sValues\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c))
        \<subseteq> ctype (Rep c)"
  proof-
    have "chDom TYPE('cs::{tsynchan}) = {} \<Longrightarrow> \<forall>c::'cs::{tsynchan}. sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) \<subseteq> ctype (Rep c)" 
      using Channel.dom2ctypeempty tsynSBRemDups_raw_sValues_subset_ctype_chDom_empty  by blast
    have "chDom TYPE('cs::{tsynchan}) \<noteq> {} \<Longrightarrow> \<forall>c::'cs::{tsynchan}. sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) \<subseteq> ctype (Rep c)" 
      using tsynSBRemDups_raw_sValues_subset_ctype_chDom_not_empty by blast
    then show ?thesis by (metis cfcomp2 empty_subsetI tsynSBRemDups_raw_sValues_subset_ctype_chDom_empty)
  qed
qed

lemma tsynSBRemDups_insert:
  shows "Rep_lsb (tsynSBRemDups\<cdot>(sb::'cs\<^sup>\<Omega>)) = (\<lambda>(c::'cs::tsynchan). (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>((Rep_lsb sb) c))"
proof (rule ext)
  fix c :: "'cs::tsynchan"
  have "lsb_well (\<lambda>c. tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c))))"
    using tsynSBRemDups_raw_lsb_well by auto

  then have
      "Rep_lsb (Abs_lsb (\<lambda>c.
         tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c))))) c
       = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))"
    by (simp)


  then have "Rep_lsb (tsynSBRemDups_raw sb) c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
    by (metis sb_rep_abs tsynSBRemDups_raw_def tsynSBRemDups_raw_lsb_well)

  moreover have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sbGetCh c\<cdot>sb)"
    by simp
  
  moreover have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(Rep_lsb sb c)"
    by (metis (no_types) sbgetch_insert2)

  ultimately show "Rep_lsb (tsynSBRemDups\<cdot>(sb::'cs\<^sup>\<Omega>)) c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(Rep_lsb sb c)"
    by (metis (mono_tags, lifting) hwl_tsynSBRemDups.tsynSBRemDups.rep_eq tsynSBRemDups_raw_def)
qed

lemma tsynRemDups_sconc_Eps: "tsynRemDups\<cdot>(\<up>Eps \<Zcat> s) = \<up>Eps \<Zcat> tsynRemDups\<cdot>s" 
  apply (auto simp: tsynRemDups_def)
  using tsynRemDups_h.cases
  by (simp add: sscanlaone_step)

lemma tsynLen_tsynRemDups_cons_Eps:
  "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>Eps \<Zcat> s)) = tsynLen\<cdot>(tsynRemDups\<cdot>s)"
  apply (simp add: tsynRemDups_def tsynLen_def)
  proof -
    have "tsynRemDups\<cdot>(\<up>Eps \<Zcat> s) = \<up>Eps \<Zcat> tsynRemDups\<cdot>s"
      using tsynRemDups_sconc_Eps
      by auto
    hence "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>Eps \<Zcat> s))
         = tsynLen\<cdot>(\<up>Eps \<Zcat> tsynRemDups\<cdot>s)"
      by simp
    also have "... = tsynLen\<cdot>(tsynRemDups\<cdot>s)"
      by (simp add: tsynlen_sconc_Eps)
    then show " (\<Lambda> (s::'a tsyn stream). #(tsyn2ustream\<cdot>s))\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>\<sim> \<Zcat> s)) 
                = (\<Lambda> (s::'a tsyn stream). #(tsyn2ustream\<cdot>s))\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s)" 
      by (metis \<open>tsynRemDups\<cdot>(\<up>\<sim> \<Zcat> (s::'a tsyn stream)) = \<up>\<sim> \<Zcat> tsynRemDups\<cdot>s\<close> tsynLen_def tsynRemDups_def)
  qed

lemma tsynLen_sconc_TSynMsg:
  "tsynLen\<cdot>(\<up>(TSynMsg v) \<Zcat> s) = tsynLen\<cdot>s + 1"
proof -
  have "tsynLen\<cdot>(\<up>(TSynMsg v) \<Zcat> s)
        = # (tsyn2ustream\<cdot>(\<up>(TSynMsg v) \<Zcat> s))"
    apply (simp add: tsynLen_def) 
    by (metis tsynLen_def tsynlen_insert tsynlen_sconc_msg)
  also have "\<dots> = # (tsyn2ustream\<cdot>s) + 1"
    by (simp add: lnat_plus_commu one_lnat_def sconc_slen2)
  also have "\<dots> = tsynLen\<cdot>s + 1"
    apply (simp add: tsynLen_def) 
    by (metis tsynLen_def tsynlen_insert)
  finally show ?thesis .
qed

lemma tsynLen_tail_TSynMsg:
  "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s) \<le> tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s)"
proof (induction s arbitrary: v)
  case adm
  show ?case
  proof (rule admI)
    fix Y :: "nat \<Rightarrow> 'a tsyn stream"
    assume chainY: "chain Y"
    assume IH: "\<And>i. tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>(Y i)) \<le> tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>(Y i))"

    let ?F = "\<lambda>s. tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s)"
    let ?G = "\<lambda>s. tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s)"

    have cont_F: "cont ?F"
      by (intro cont2cont)
    have cont_G: "cont ?G"
      by (intro cont2cont)
    have F_lub:
      "?F (\<Squnion>i. Y i) = (\<Squnion>i. ?F (Y i))"
      using cont_F chainY
      by (rule cont2contlubE)

    have G_lub:
      "?G (\<Squnion>i. Y i) = (\<Squnion>i. ?G (Y i))"
      using cont_G chainY
      by (rule cont2contlubE)

    have lub_ineq:
      "(\<Squnion>i. ?F (Y i)) \<le> (\<Squnion>i. ?G (Y i))"
      using IH UNIV_def ch2ch_cont chainY lub_mono2 tsynRemDups_def by auto

    then have endResult: "\<And>Y::nat \<Rightarrow> 'a tsyn stream.
       chain Y \<Longrightarrow>
       \<forall>(i::nat) x::'a. #\<^sub>-(sscanlAOne tsynRemDups_h (TSynMsg x)\<cdot>(Y i)) \<le> #\<^sub>-(sscanlAOne tsynRemDups_h \<sim>\<cdot>(Y i)) \<Longrightarrow>
       \<forall>x::'a. #\<^sub>-(sscanlAOne tsynRemDups_h (TSynMsg x)\<cdot>(\<Squnion>i::nat. Y i)) \<le> #\<^sub>-(sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<Squnion>i::nat. Y i))"
      unfolding F_lub G_lub
      using lub_ineq by (simp add: contlub_cfun_arg lub_mono2)
  next
    show " \<And>Y::nat \<Rightarrow> 'a tsyn stream.
       chain Y \<Longrightarrow>
       \<forall>(i::nat) x::'a. #\<^sub>-(sscanlAOne tsynRemDups_h (TSynMsg x)\<cdot>(Y i)) \<le> #\<^sub>-(sscanlAOne tsynRemDups_h \<sim>\<cdot>(Y i)) \<Longrightarrow>
       \<forall>x::'a. #\<^sub>-(sscanlAOne tsynRemDups_h (TSynMsg x)\<cdot>(\<Squnion>i::nat. Y i)) \<le> #\<^sub>-(sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<Squnion>i::nat. Y i))"
      by (simp add: contlub_cfun_arg lub_mono2)
  qed
next
  case bottom
  then show ?case
    by (simp add: tsynLen_def sscanlAOne_def)
next
  case (step a s)
  obtain st1 out1 where h1: "tsynRemDups_h (TSynMsg v) a = (st1, out1)"
    by (cases "tsynRemDups_h (TSynMsg v) a") auto
  obtain st0 out0 where h0: "tsynRemDups_h \<sim> a = (st0, out0)"
    by (cases "tsynRemDups_h \<sim> a") auto

  have lhs_step:
    "sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>(\<up>a \<Zcat> s) = sup' out1 \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h st1\<cdot>s"
    by (simp add: sscanlaone_step h1)

  have rhs_step:
    "sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>a \<Zcat> s) = sup' out0 \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h st0\<cdot>s"
    by (simp add: sscanlaone_step h0)

  have LHS_len:
    "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>(\<up>a \<Zcat> s)) = tsynLen\<cdot>(sup' out1 \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h st1\<cdot>s)"
    by (simp add: lhs_step)

  have RHS_len:
    "tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>a \<Zcat> s)) = tsynLen\<cdot>(sup' out0 \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h st0\<cdot>s)"
    by (simp add: rhs_step)

  show ?case
  proof (cases a)
    case Eps
    have h1': "tsynRemDups_h (TSynMsg v) Eps = (TSynMsg v, \<sim>)"
      by simp
    have h0': "tsynRemDups_h \<sim> Eps = (\<sim>, \<sim>)"
      by simp

    from h1 h1' have [simp]: "st1 = TSynMsg v" "out1 = \<sim>"
      apply (simp add: Eps) using Eps h1 by auto
    from h0 h0' have [simp]: "st0 = \<sim>" "out0 = \<sim>"
      using Eps apply fastforce using Eps h0 by auto

    from LHS_len have
      "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>(\<up>a \<Zcat> s)) = tsynLen\<cdot>(sup' \<sim> \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s)"
      by simp
    also have "\<dots> = tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s)"
      apply (simp add: tsynLen_def) by (metis tsynLen_def tsynlen_sconc_Eps)
    also have "\<dots> \<le> tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s)"
      using step.IH by simp
    also from RHS_len Eps have
      "tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s) = tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>a \<Zcat> s))"
      apply (simp add: tsynLen_def) by (metis tsynLen_def tsynlen_sconc_Eps)
    finally show ?thesis
      using Eps by simp
  next
    case (Msg w)
    show ?thesis
    proof (cases "TSynMsg v = TSynMsg w")
      case True
      have h1':
        "tsynRemDups_h (TSynMsg v) (TSynMsg w) = (TSynMsg v, \<sim>)"
        using True by simp
      from h1 h1' have [simp]: "st1 = TSynMsg v" "out1 = \<sim>"
        using Msg apply auto[1] 
        using Msg h1 h1' by force

      have h0':
        "tsynRemDups_h \<sim> (TSynMsg w) = (TSynMsg w, TSynMsg w)"
        by simp
      from h0 h0' have [simp]: "st0 = TSynMsg w" "out0 = TSynMsg w"
        apply (simp add: Msg) 
        using Msg Product_Type.prod.inject h0 h0' by force

      from LHS_len Msg have
        "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>(\<up>a \<Zcat> s)) = tsynLen\<cdot>(sup' \<sim> \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s)"
        using True \<open>(out1::'a tsyn) = \<sim>\<close> \<open>(st1::'a tsyn) = TSynMsg (v::'a)\<close> by blast
      also have "\<dots> = tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s)"
        by (simp add: tsynlen_sconc_Eps)
      
      from RHS_len Msg have
        "tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>a \<Zcat> s)) = tsynLen\<cdot>(sup' (TSynMsg w) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s)"
        by simp
      have "\<dots> = tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s) + 1"
        by (simp add: tsynLen_sconc_TSynMsg)

      ultimately show ?thesis
        using Msg True rhs_step
        by (metis (full_types) \<open>#\<^sub>-(\<up>\<sim>\<Zcat>\<Zcat>sscanlAOne tsynRemDups_h (TSynMsg (w::'a))\<cdot> (s::'a tsyn stream)) = #\<^sub>-(sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s)\<close> 
          \<open>(out0::'a tsyn) = TSynMsg (w::'a)\<close>
          \<open>(st0::'a tsyn) = TSynMsg (w::'a)\<close> conc_stream_def less_lnsuc tsynlen_sconc_msg)
    next
      case False
      have h1':
        "tsynRemDups_h (TSynMsg v) (TSynMsg w) = (TSynMsg w, TSynMsg w)"
        using False by simp
      from h1 h1' have [simp]: "st1 = TSynMsg w" "out1 = TSynMsg w"
        apply (simp add: Msg) 
        using Msg Product_Type.prod.inject h1 h1' by force

      have h0':
        "tsynRemDups_h \<sim> (TSynMsg w) = (TSynMsg w, TSynMsg w)"
        by simp
      from h0 h0' have [simp]: "st0 = TSynMsg w" "out0 = TSynMsg w"
        apply (simp add: Msg) 
        using Msg Product_Type.prod.inject h0 h0' by force

      from LHS_len Msg have
        "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>(\<up>a \<Zcat> s)) = tsynLen\<cdot>(sup' (TSynMsg w) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s)"
        by simp
      also have "\<dots> = tsynLen\<cdot>(\<up>(TSynMsg w) \<Zcat> sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s)"
        by simp
      also have "\<dots> = tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s) + 1"
        by (rule tsynLen_sconc_TSynMsg)

      from RHS_len Msg have
        "tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>a \<Zcat> s))
         = tsynLen\<cdot>(sup' (TSynMsg w) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s)"
        by simp
      have "\<dots> = tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg w)\<cdot>s) + 1"
        by (simp add: tsynLen_sconc_TSynMsg)

      ultimately show ?thesis
        using Msg False rhs_step by auto
    qed
  qed
qed


lemma tsynLen_tsynRemDups_cons_TSynMsg_le1:
  "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s)) \<le> tsynLen\<cdot>(tsynRemDups\<cdot>s) + 1"
proof -
  have decomp:
    "tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s)
     = sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>(TSynMsg v) \<Zcat> s)"
    by (simp add: tsynRemDups_def)

  also have
    "\<dots> = sup' (snd (tsynRemDups_h \<sim> (TSynMsg v))) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> (TSynMsg v)))\<cdot>s"
    by (simp add: sscanlaone_step)

  moreover have "tsynRemDups_h \<sim> (TSynMsg v) = (TSynMsg v, TSynMsg v)"
    by simp

  ultimately have
    "tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s) = sup' (TSynMsg v) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s"
    by simp

  hence LHS:
    "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s)) = tsynLen\<cdot>(sup' (TSynMsg v) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s)"
    by simp

  also have
    "tsynLen\<cdot>(sup' (TSynMsg v) \<Zcat>\<Zcat> t) = tsynLen\<cdot>t + 1" for t
    by (simp add: tsynLen_sconc_TSynMsg)

  from this have
    "tsynLen\<cdot>(sup' (TSynMsg v) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s) = tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s) + 1"
    by simp

  also have
    "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s) \<le> tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s)"
    by (rule tsynLen_tail_TSynMsg)

  hence
    "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s) + 1 \<le> tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s) + 1"
    by (simp add: lessequal_addition)

  also have "sscanlAOne tsynRemDups_h \<sim>\<cdot>s = tsynRemDups\<cdot>s"
    by (simp add: tsynRemDups_def)

  finally show ?thesis
    by simp
qed

lemma tsynLen_tsynRemDups_le:
  "tsynLen\<cdot>(tsynRemDups\<cdot>s) \<le> tsynLen\<cdot>s"
proof (induction s)
  case adm
  show ?case
  unfolding adm_def
proof (intro allI impI)
  fix Y :: "nat \<Rightarrow> 'a tsyn stream"
    assume chainY: "chain Y"
    assume IH_all: "\<forall>i. #\<^sub>-(tsynRemDups\<cdot>(Y i)) \<le> #\<^sub>-(Y i)"
    from IH_all have IH: "\<And>i. #\<^sub>-(tsynRemDups\<cdot>(Y i)) \<le> #\<^sub>-(Y i)"
      by blast
    have len_lub_tsrd:
      "#\<^sub>-(tsynRemDups\<cdot>(\<Squnion>i. Y i)) = (\<Squnion>i. #\<^sub>-(tsynRemDups\<cdot>(Y i)))"
      using chainY
      by (simp add: cont2contlubE) 
    have len_lub:
      "#\<^sub>-(\<Squnion>i. Y i) = (\<Squnion>i. #\<^sub>-(Y i))"
      using chainY
      by (simp add: cont2contlubE)
    from IH have lub_ineq:
      "(\<Squnion>i. #\<^sub>-(tsynRemDups\<cdot>(Y i))) \<le> (\<Squnion>i. #\<^sub>-(Y i))"
      using lub_mono monotoneI chain_mono chainY lub_mono2 by auto
    show "#\<^sub>-(tsynRemDups\<cdot>(\<Squnion>i. Y i)) \<le> #\<^sub>-(\<Squnion>i. Y i)"
      unfolding len_lub_tsrd len_lub
      using lub_ineq by simp
  qed
next
  case bottom
  then show ?case
    by (simp add: tsynRemDups_def tsynLen_def sscanlAOne_def)
next
  case (step a s)
  have sscan_step:
    "tsynRemDups\<cdot>(\<up>a \<Zcat> s) =
       sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>a \<Zcat> s)"
    by (simp add: tsynRemDups_def)

  show ?case
  proof (cases a)
    case Eps
    have "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>Eps \<Zcat> s)) \<le> tsynLen\<cdot>(tsynRemDups\<cdot>s)"
      by (simp add: tsynLen_tsynRemDups_cons_Eps)
    also have "\<dots> \<le> tsynLen\<cdot>s"
      using step.IH .
    also have "\<dots> \<le> tsynLen\<cdot>(\<up>Eps \<Zcat> s)"
      by (simp add: tsynlen_sconc_Eps)
    finally show ?thesis using Eps by blast
    next
    case (Msg v)
    have "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s))
          \<le> tsynLen\<cdot>(tsynRemDups\<cdot>s) + 1"
      by (rule tsynLen_tsynRemDups_cons_TSynMsg_le1)
    also have "\<dots> \<le> tsynLen\<cdot>s + 1"
      using step.IH lnat_plus_suc by fastforce
    also have "\<dots> = tsynLen\<cdot>(\<up>(TSynMsg v) \<Zcat> s)"
      by (simp add: tsynLen_sconc_TSynMsg)
    finally show ?thesis
      using Msg by simp
  qed
qed

lemma tsynSBRemDups_tsynSBlen_le_h:
  "tsynLenM\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>s) \<le> tsynLenM\<cdot>s"
proof -
  have lhs: "tsynLenM\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>s) = 
            tsynLen\<cdot>(toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))))"
    by (simp add: tsynLenM_def oo_def)
     
  have conversion_eq: "\<And>x. toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>x) = x"
  proof -
    fix x
    have "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>x) = smap ((inv Tsyn) o (inv Timed))\<cdot>(smap (Timed o Tsyn)\<cdot>x)"
      by (simp add: toTsynMsgStream_def tsynMsgToMStream_def)
    also have "... = smap (((inv Tsyn) o (inv Timed)) o (Timed o Tsyn))\<cdot>x"
      by (simp add: smapsmap2smap)
    also have "... = x"
  proof -
    have "\<forall>s. toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>s) = s \<or> inv Tsyn \<circ> inv Timed \<circ> (Timed \<circ> Tsyn) \<noteq> id"
      by (metis (no_types) smap_id smapsmap2smap toTsynMsgStream_def tsynMsgToMStream_def)
    then show ?thesis
      using toTsynMsgStream_def tsynMsgToMStream_def
      using calculation by auto 
  qed
    finally show "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>x) = x" .
  qed

  then have "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))) = tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s)"
    by simp 
  
  with lhs have lhs_simplified: "tsynLenM\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>s) = 
                               tsynLen\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))"
    by simp
  
  have "tsynLen\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s)) \<le> tsynLen\<cdot>(toTsynMsgStream\<cdot>s)"
    using tsynLen_tsynRemDups_le by auto
  
  also have "tsynLen\<cdot>(toTsynMsgStream\<cdot>s) = tsynLenM\<cdot>s"
    by (simp add: tsynLenM_def)
  
  finally show ?thesis
    by (metis lhs_simplified)
qed

lemma tsynSBRemDups_tsynSBlen_le: "tsynSBlen (tsynSBRemDups\<cdot>sb) \<le> tsynSBlen sb"
proof (cases "chDomEmpty TYPE('a)")
  case True
  then have "tsynSBlen sb = \<infinity>" unfolding tsynSBlen_def by simp
  then show ?thesis using  tsynSBlen_def
    by simp
next
  case False
  have h1: "\<forall>c. tsynLenM\<cdot>((tsynSBRemDups\<cdot>sb) \<^enum> c) \<le> tsynLenM\<cdot>(sb \<^enum> c)"
    proof
      fix c::'a
      have stream_eq: "(tsynSBRemDups\<cdot>sb) \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
        by (metis (no_types, lifting) cfcomp2 hwl_tsynSBRemDups.tsynSBRemDups.rep_eq sb_rep_abs sbgetch_insert2 tsynSBRemDups_raw_def
          tsynSBRemDups_raw_lsb_well)
      
      have "tsynLenM\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)) \<le> tsynLenM\<cdot>(sb \<^enum> c)"
        using tsynSBRemDups_tsynSBlen_le_h by auto
      
      then show "tsynLenM\<cdot>((tsynSBRemDups\<cdot>sb) \<^enum> c) \<le> tsynLenM\<cdot>(sb \<^enum> c)"
        by (simp add: stream_eq)
    qed
  show ?thesis
    using h1 by (metis (mono_tags, opaque_lifting) False trans_lnle tsynSBlen_ruleD(1,2))
qed

lemma tsynSBRemDups_getCh: "tsynSBRemDups\<cdot>sb \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
  by (metis (no_types, lifting) cfcomp2 hwl_tsynSBRemDups.tsynSBRemDups.rep_eq sb_rep_abs sbgetch_insert2 tsynSBRemDups_raw_def
          tsynSBRemDups_raw_lsb_well)


lemma tsynMsgToMStream_tsynRemDup_toTsynMsgStream:
  assumes "inj f"
  shows "tsynMsgToMStream\<cdot>(\<alpha>\<^sub>-(toTsynMsgStream\<cdot>(smap (Timed \<circ> Tsyn \<circ> map_tsyn f)\<cdot>s))) 
      = smap (Timed \<circ> Tsyn \<circ> map_tsyn f)\<cdot>(\<alpha>\<^sub>-s)"
  apply(simp add: toTsynMsgStream_smap_Timed_Tsyn_f)
  apply(simp add: assms tsynRemDups_smap[symmetric] tsyn.inj_map)
  by (simp add: smapsmap2smap tsynMsgToMStream_def)


lemma
  tsynsbremdups_tsynsblen_ex:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows "\<exists>c. tsynLenM\<cdot>(tsynMsgToMStream\<cdot>(\<alpha>\<^sub>-(toTsynMsgStream\<cdot>(sb \<^enum> c)))) = tsynSBlen (tsynSBRemDups\<cdot>(sb))"
proof-

  obtain c where c_def: "tsynLenM\<cdot>(tsynSBRemDups\<cdot>(sb)  \<^enum>  c) = tsynSBlen (tsynSBRemDups\<cdot>(sb))"
    using assms tsynSBlen_ruleD(2) by blast

  have eq: "(tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c) = (tsynSBRemDups\<cdot>(sb) \<^enum> c)"
    using tsynSBRemDups_getCh[symmetric] by blast

  show ?thesis
    apply(rule_tac x=c in exI)
    by(simp add: eq[simplified] c_def)
qed



lemma tsynSBRemDups_is_lifted: "is_lifted_tsyn_stream_fn tsynSBRemDups tsynRemDups"
  apply(simp add: is_lifted_tsyn_stream_fn_def is_lifted_stream_fn_def)
  by (metis cfcomp2 tsynSBRemDups_getCh)


end
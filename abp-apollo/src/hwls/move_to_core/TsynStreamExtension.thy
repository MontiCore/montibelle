theory TsynStreamExtension
  imports stream.TsynStream StreamExtension

begin


lemma tsynboolfilter_tsynmap:
  assumes "#s \<le> #ora"
  shows "tsynBoolFilter\<cdot>((tsynMap f)\<cdot>s)\<cdot>ora = (tsynMap f)\<cdot>(tsynBoolFilter\<cdot>s\<cdot>ora)"
  apply(simp add: tsynBoolFilter_def)
  apply(induction s arbitrary: ora, auto)
  apply(case_tac ora, auto)
  apply(case_tac a, auto)
   apply(simp add: tsynmap_sconc_Eps tsynzip_sconc_Eps tsynfilter_sconc_Eps tsynprojfst_sconc_Eps)
  apply(simp add: tsynmap_sconc_msg tsynzip_sconc_msg)
  apply(case_tac aa, auto)
   apply(simp add: tsynfilter_sconc_msg_in tsynprojfst_sconc_msg tsynmap_sconc_msg)
  by(simp add: tsynfilter_sconc_msg_nin tsynprojfst_sconc_Eps tsynmap_sconc_Eps)




lemma "#\<^sub>-(tsynFilter X\<cdot>(sdrop 1\<cdot>(<[Eps, Eps]>))) =  #\<^sub>-(tsynFilter X\<cdot>(<[Eps, Eps]>))"
  by (metis l2s_single list2s_conc tsynfilter_tsynlen tsynlen_sconc_Eps tsynlen_singleton_Eps tsynlen_tsynfilter_sdrop_ile
      zero_eq)

lemma "#\<^sub>-(tsynFilter {1}\<cdot>(sdrop 1\<cdot>(<[TSynMsg 1, Eps]>))) <  #\<^sub>-(tsynFilter {1}\<cdot>(<[TSynMsg 1, Eps]>))"
  by (simp add: tsynfilter_sconc_msg_in tsynfilter_singleton_Eps tsynlen_insert)

lemma "tsyn2ustream\<cdot>({False} \<ominus>\<^sub>-(<[TSynMsg True]>)) = \<bottom> \<Longrightarrow> tsynValues\<cdot> (<[TSynMsg True]>) = UNIV - {False}"
  apply (simp add: tsyndom_singleton_msg)
  by auto

lemma  "tsyn2ustream\<cdot>({} \<ominus>\<^sub>-(<[Eps]>)) = \<bottom> \<Longrightarrow> tsynValues\<cdot> (<[Eps]>) \<subset> UNIV - {}"
  apply (simp add: tsynfilter_singleton_Eps tsyndom_insert) 
  by auto

lemma "tsynValues\<cdot>({1::nat} \<ominus>\<^sub>-(<[TSynMsg 2]>)) \<subset> tsynValues\<cdot>({1} \<ominus>\<^sub>-((updis(TSynMsg 1)) && (<[TSynMsg 2]>)))" 
  apply (simp add: tsyndom_singleton_msg lscons_conv)
  by auto 
lemma "tsynValues\<cdot>({1::nat} \<ominus>\<^sub>-(<[TSynMsg 2]>)) = tsynValues\<cdot>({1} \<ominus>\<^sub>-((updis(TSynMsg 2)) && (<[TSynMsg 2]>)))" 
  by (simp add: tsyndom_singleton_msg lscons_conv)

lemma assumes "{1} \<subseteq> {1::nat,2}"
  shows " #\<^sub>-(tsynFilter {1}\<cdot>(<[TSynMsg 1]>)) =  #\<^sub>-(tsynFilter {1::nat,2}\<cdot>(<[TSynMsg 1]>))"
  by (simp add: tsynfilter_singleton_msg_in  tsynlen_insert)
lemma assumes "{} \<subseteq> {1::nat}"
  shows " #\<^sub>-(tsynFilter {}\<cdot>(<[TSynMsg 1]>)) <  #\<^sub>-(tsynFilter {1::nat}\<cdot>(<[TSynMsg 1]>))"
  by (simp add: tsynfilter_singleton_msg_in tsynfilter_singleton_msg_nin tsynlen_insert)

lemma "#\<^sub>-(\<alpha>\<^sub>-(<[Eps]>)) = #\<^sub>-(<[Eps]>)"
  by (simp add: tsynlen_insert)

lemma  "#\<^sub>-(\<alpha>\<^sub>-(<[TSynMsg (1::nat), TSynMsg 1]>)) < #\<^sub>-(<[TSynMsg 1, TSynMsg 1]>)"
  apply (simp add: tsynlen_insert)
  using  sconc_snd_empty 
  by (metis Fin_Suc eq_Suc_0_numeral1 ln_less lnat_1_inf one_lnat_def tsynlen_insert tsynlen_singleton_msg tsynremdups_sup
      tsynremdups_tsynlen_msg_eq)

lemma
  fixes y :: "(nat \<times> bool) tsyn stream"
  defines "y \<equiv> <[ TSynMsg (1, True), TSynMsg (2, True), TSynMsg (3, False) ]>"
  shows   "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) > #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))"
proof -
  have "\<alpha>\<^sub>- y = y" by (simp add: y_def tsynremdups_unfold)  
  moreover have "\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>- y) = <[ TSynMsg True,  \<sim>, TSynMsg False ]>"
    apply (simp add: y_def tsynremdups_unfold tsynprojsnd_sconc_msg) 
    by (simp add: tsynprojsnd_singleton_msg)
  ultimately show ?thesis
    by (simp add: y_def tsynlen_sconc_msg tsynlen_singleton_msg tsynprojfst_singleton_msg 
        tsynprojfst_sconc_msg tsynlen_sconc_Eps) 
qed

lemma
  fixes y :: "(nat \<times> bool) tsyn stream"
  defines "y \<equiv> <[ TSynMsg (1, True), TSynMsg (2, False), TSynMsg (3, True) ]>"
  shows   "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))"
  apply (simp add: y_def tsynremdups_unfold tsynprojsnd_sconc_msg 
        tsynprojfst_singleton_msg tsynprojsnd_singleton_msg tsynprojfst_sconc_msg)
  by (simp add: tsynlen_sconc_msg tsynlen_singleton_msg)

lemma  " #\<^sub>-(\<up>(TSynMsg (1::nat))) > #\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>(\<up>(TSynMsg (1::nat)))\<cdot>(\<up>False)))"
  by (simp add: tsynboolfilter_single_false tsynlen_insert)
lemma  " #\<^sub>-(\<up>(TSynMsg (1::nat))) = #\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>(\<up>(TSynMsg (1::nat)))\<cdot>(\<up>True)))"
  by (simp add: tsynboolfilter_single_true tsynlen_insert)

lemma assumes "y=<[TSynMsg (1,True), TSynMsg (1,True)]>" and "ora = <[False, True]> \<Zcat> (sinftimes (\<up>True))" 
  shows "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora))) = #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) \<Longrightarrow> \<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora)) \<noteq> \<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)"  
  using assms
  apply (simp add: tsynboolfilter_lemmas tsynprojfst_sconc_Eps tsynprojfst_sconc_msg
   tsynremdups_step sscanlAOne_def tsynlen_sconc_Eps tsynlen_sconc_msg tsynprojfst_singleton_msg tsynprojfst_singleton_Eps)
  using tsynlen_singleton_msg tsynlen_singleton_Eps inject_scons by blast

lemma "y=<[TSynMsg (1::nat), TSynMsg 2]> \<Longrightarrow> ora = <[False, True]> \<Zcat> (sinftimes (\<up>True))
        \<Longrightarrow> \<not>(tsyn2ustream\<cdot>((\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora))) \<sqsubseteq> tsyn2ustream\<cdot>((\<alpha>\<^sub>-y)))"
  by (simp add: tsynboolfilter_lemmas tsynRemDups_def sscanlAOne_def tsynprojfst_sconc_Eps tsynprojfst_sconc_msg)


lemma tsyn_stream_infs: "(\<And>s::'a tsyn stream. #\<^sub>-s<\<infinity> \<Longrightarrow> P s) \<Longrightarrow> adm P \<Longrightarrow> P s"
  using stream_infs 
  by (metis tsynEps_tsynEps2slen_infinite_msg tsynlen_not_inf_eq_inf)


lemma smap_tsynBoolFilter:
  assumes "f Eps = Eps"
    and "\<And> m. m\<noteq>Eps \<Longrightarrow> f m \<noteq> Eps "
  shows "(smap f)\<cdot>(tsynBoolFilter\<cdot>y\<cdot>ora) = tsynBoolFilter\<cdot>((smap f)\<cdot>y)\<cdot>ora"
proof (induction y arbitrary: ora rule: tsyn_ind)
  case adm
  then show ?case by simp
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  show ?case
  proof (cases ora)
    case bottom
    then show ?thesis by simp
  next
    case (step a s')
    
    obtain m' where f_m: "f (TSynMsg m) = TSynMsg m'"
      using assms(2)[of "TSynMsg m"] by (cases "f (TSynMsg m)"; simp)
    
    show ?thesis
    proof (cases a)
      case True
      have left: "tsynBoolFilter\<cdot>(\<up>(TSynMsg m) \<Zcat> s)\<cdot>(\<up>True \<Zcat> s') = 
                      \<up>(TSynMsg m) \<Zcat> tsynBoolFilter\<cdot>s\<cdot>s'"
        using tsynboolfilter_msg_true_rec
        by blast
      
      have right: "tsynBoolFilter\<cdot>(smap f\<cdot>(\<up>(TSynMsg m) \<Zcat> s))\<cdot>(\<up>True \<Zcat> s') = 
                       \<up>(TSynMsg m') \<Zcat> tsynBoolFilter\<cdot>(smap f\<cdot>s)\<cdot>s'"
        by (simp add: f_m tsynboolfilter_msg_true_rec)
      
      show ?thesis
        using True f_m left
          local.step msg right
        by force      
    next
      case False
      have left: "tsynBoolFilter\<cdot>(\<up>(TSynMsg m) \<Zcat> s)\<cdot>(\<up>False \<Zcat> s') = 
                       \<up>Eps \<Zcat> tsynBoolFilter\<cdot>s\<cdot>s'"
        using tsynboolfilter_msg_false_rec by blast
      
      have right: "tsynBoolFilter\<cdot>(smap f\<cdot>(\<up>(TSynMsg m) \<Zcat> s))\<cdot>(\<up>False \<Zcat> s') = 
                        \<up>Eps \<Zcat> tsynBoolFilter\<cdot>(smap f\<cdot>s)\<cdot>s'"
        by (simp add: f_m tsynboolfilter_msg_false_rec)
      
      show ?thesis
        using False f_m left
          local.step msg right
        by (simp add:
            assms(1))
    qed
  qed
next
  case (Eps s)
  show ?case
  proof (cases ora)
    case bottom
    then show ?thesis by simp
  next
    case (step a s')
    have left: "tsynBoolFilter\<cdot>(\<up>Eps \<Zcat> s)\<cdot>(\<up>a \<Zcat> s') = 
                \<up>Eps \<Zcat> tsynBoolFilter\<cdot>s\<cdot>(\<up>a \<Zcat> s')"
      using tsynboolfilter_Eps_bool_rec by blast
    
    have right: "tsynBoolFilter\<cdot>(smap f\<cdot>(\<up>Eps \<Zcat> s))\<cdot>(\<up>a \<Zcat> s') = 
                 tsynBoolFilter\<cdot>(\<up>(f Eps) \<Zcat> (smap f\<cdot>s))\<cdot>(\<up>a \<Zcat> s')"      
      by simp
    
    also have "... = tsynBoolFilter\<cdot>(\<up>Eps \<Zcat> smap f\<cdot>s)\<cdot>(\<up>a \<Zcat> s')"
      using assms by simp

    also have "... = \<up>Eps \<Zcat> tsynBoolFilter\<cdot>(smap f\<cdot>s)\<cdot>(\<up>a \<Zcat> s')"
      using tsynboolfilter_Eps_bool_rec by blast
    
    finally have right_simplified: "tsynBoolFilter\<cdot>(smap f\<cdot>(\<up>Eps \<Zcat> s))\<cdot>(\<up>a \<Zcat> s') = 
                                    \<up>Eps \<Zcat> tsynBoolFilter\<cdot>(smap f\<cdot>s)\<cdot>(\<up>a \<Zcat> s')" .
    
    from this step show ?thesis
      by (simp add: Eps assms(1)
          left)
    qed
  qed




lemma infeps_ustream[simp]:"\<up>\<sim>\<^sup>\<infinity>\<^sup>- = \<epsilon>"
  by(simp add: tsyn2ustream_def)

lemma infeps_tsynlen[simp]:" #\<^sub>-\<up>\<sim>\<^sup>\<infinity> = 0"
  by(simp add: tsynlen_insert)
 
lemma helper:"\<exists>y::'a tsyn stream. stake i\<cdot>s \<sqsubseteq> y \<and> #y = \<infinity> \<and> #\<^sub>-y < \<infinity>"
  apply(rule_tac x="(stake i\<cdot>s)\<Zcat>((\<up>Eps)\<^sup>\<infinity>)" in exI)
  apply auto  
   apply (simp add: slen_sconc_snd_inf)
  apply(induction i arbitrary: s,simp_all)
  apply(case_tac s;simp)
  apply(case_tac a;simp)
  apply(simp add: tsynlen_sconc_Eps)
  by(simp add: tsynlen_sconc_msg)

lemma tsyn_abp_adm:
  assumes "P \<equiv> \<lambda>x. (f\<cdot>x)\<^sup>- = x\<^sup>-"
  and "\<And>s. (#s = \<infinity> \<and> #\<^sub>-s < \<infinity>) \<Longrightarrow> P s"
  and "\<And>s.  #\<^sub>-s = \<infinity> \<Longrightarrow> #\<^sub>-(f\<cdot>s) = \<infinity>"
shows "#s = \<infinity> \<Longrightarrow> P s "
  using assms(2)
  apply(simp add: assms(1))
  apply(cases "tsynLen\<cdot>s = \<infinity>") defer
  using tsynlen_not_inf_eq_inf apply blast
   apply(subgoal_tac "chain(\<lambda>i. stake i\<cdot>s)")
    apply(subgoal_tac "(f\<cdot>(\<Squnion>x. stake x\<cdot>s))\<^sup>- \<sqsubseteq> (\<Squnion>x. stake x\<cdot>s)\<^sup>-")
      apply auto
     apply(subgoal_tac "(\<Squnion>x. stake x\<cdot>s) = s")
      apply simp
  using assms(3) 
  using eq_tsynlen_eq_and_less apply metis
  using stream.reach apply blast
  apply(rule admD,simp_all)
proof(rule ccontr)
  fix i
  assume a2:"(\<And>s. #s = \<infinity> \<and> #\<^sub>-s < \<infinity> \<Longrightarrow> (f\<cdot>s)\<^sup>- = s\<^sup>-)"
  assume a4:"(f\<cdot>(stake i\<cdot>s))\<^sup>- \<notsqsubseteq> (stake i\<cdot>s)\<^sup>-"
  then obtain y where y_def:" y = stake i\<cdot>s\<Zcat>((\<up>Eps)\<^sup>\<infinity>)"
    by blast
  have y_len:"#y = \<infinity> \<and> #\<^sub>-y < \<infinity>"
    apply(simp add: y_def)
   apply auto  
   apply (simp add: slen_sconc_snd_inf)
    apply(induction i arbitrary: s,simp_all)
  apply(case_tac s;simp)
  apply(case_tac a;simp)
  apply(simp add: tsynlen_sconc_Eps)
  by(simp add: tsynlen_sconc_msg)
  then have "(f\<cdot>(stake i\<cdot>s))\<^sup>- \<sqsubseteq> (y)\<^sup>-"
    using a2 y_def 
    by (metis monofun_cfun_arg sconc_prefix)
  then have "(stake i\<cdot>s)\<^sup>-  \<sqsubseteq> (f\<cdot>(stake i\<cdot>s))\<^sup>-" 
    using a4 monofun_cfun_arg stream_order_pre_total y_def y_len sconc_prefix by blast
  then obtain rt where rt_def:"(stake i\<cdot>s)\<^sup>- \<Zcat> rt = (f\<cdot>(stake i\<cdot>s))\<^sup>- \<and> rt\<noteq> \<epsilon>" 
    using approxl3 a4 by (metis sconc_snd_empty) 
  then have "(stake i\<cdot>s)\<^sup>- \<Zcat> rt \<sqsubseteq> (y)\<^sup>-" 
    using \<open>(f\<cdot>(stake i\<cdot>s))\<^sup>- \<sqsubseteq> y\<^sup>-\<close> by presburger
  then show "False"
    apply(simp add: y_def)
    apply(subgoal_tac "((stake i\<cdot>s \<Zcat> (\<up>\<sim>\<^sup>\<infinity>))\<^sup>-) = ((stake i\<cdot>s)\<^sup>-) ")
     apply (simp add: a4 rt_def)
    apply(subst tsynabs_sconc) 
     apply (simp add: lnless_def)
    by simp
qed

end

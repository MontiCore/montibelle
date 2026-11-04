theory SPFComp

imports SPF 
begin




fixrec spfComp::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)
 \<rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>)" where 
"spfComp\<cdot>spf1\<cdot>spf2\<cdot>sbIn = spf1\<cdot>((sbIn \<uplus>\<^sub>- spfComp\<cdot>spf1\<cdot>spf2\<cdot>sbIn)\<star>\<^sub>1) 
                      \<uplus> spf2\<cdot>((sbIn \<uplus>\<^sub>- spfComp\<cdot>spf1\<cdot>spf2\<cdot>sbIn)\<star>\<^sub>2)"

declare %invisible spfComp.simps[simp del]

lemma spfComp_def2: "spfComp =(\<Lambda> spf1 spf2 sbIn.
  fix\<cdot>(\<Lambda> sbOut. spf1\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> spf2\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>2)))"
  unfolding spfComp_def
  apply(subst fix_const';
          ((intro cont2cont)
            |
          ((rule cfun_belowI | rule cfun_eqI)+)?, simp)?)+
  done


abbreviation spfComp_abbr::
"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)
 \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>)" 
(infixr "\<otimes>" 70) where "spf1 \<otimes> spf2 \<equiv> spfComp\<cdot>spf1\<cdot>spf2"

text\<open>The compositions output domain is equal to output domain union 
of both input functions. Thus, the composition operator does not 
hide any internal channels in the output. This can still be achieved
by using the @{const sbTypeCast} operator to restrict the output 
domain. A abbreviation for applying @{const sbTypeCast} to the 
composition operator is provided. It can be used for hiding 
channels.\<close>

abbreviation spfCompm_abbr (infixr "\<otimes>\<^sub>\<star>" 70) where 
"spf1 \<otimes>\<^sub>\<star> spf2 \<equiv> sbTypeCast oo (spfComp\<cdot>spf1\<cdot>spf2) oo sbTypeCast"


lemma spfcomp_unfold: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  shows "((f \<otimes> g)\<cdot>sbIn) = 
          f\<cdot>((sbIn \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sbIn)\<star>\<^sub>1) \<uplus> g\<cdot>((sbIn \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sbIn)\<star>\<^sub>2)"
  apply(simp add: spfComp_def)
  by(subst fix_eq, simp)

lemma spfcomp_extract_l: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  shows "((sb \<uplus> (f \<otimes> g)\<cdot>sb)\<star>) = f\<cdot>((sb \<uplus> (f \<otimes> g)\<cdot>sb)\<star>)"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_conv_snd)
  apply(simp, blast)
  apply(subst sbunion_conv_fst)
  apply simp
  by(simp add: union_minus_nomagfst)


lemma spfcomp_extract_r: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
  shows "((sb \<uplus> (f \<otimes> g)\<cdot>sb)\<star>) = g\<cdot>((sb \<uplus> (f \<otimes> g)\<cdot>sb)\<star>)"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_conv_snd)
  apply(simp, blast)
  apply(subst sbunion_conv_snd)
  apply(simp add: assms)
  by (simp add: union_minus_nomagsnd)


lemma spfcomp_getch_l:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "Rep c \<in> chDom TYPE('fOut)"
    and "chDom TYPE('fIn) \<inter> chDom TYPE('fOut \<union> 'gOut) = {}"
  shows "(f \<otimes> g)\<cdot>sb  \<^enum>\<^sub>\<star> c = f\<cdot>(sb\<star>)  \<^enum>\<^sub>\<star> c"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_getchl[OF assms(1)])
  apply(rule spf_arg_cong, simp)
  apply(rule sbunion_getchl)
  using assms(2) by auto[1]

lemma spfcomp_getch_r:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "Rep c \<notin> chDom TYPE('fOut)"
    and "chDom TYPE('gIn) \<inter> chDom TYPE('fOut \<union> 'gOut) = {}"
  shows "(f \<otimes> g)\<cdot>sb  \<^enum>\<^sub>\<star> c = g\<cdot>(sb\<star>)  \<^enum>\<^sub>\<star> c"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_getchr[OF assms(1)])
  apply(rule spf_arg_cong, simp)
  apply(rule sbunion_getchl)
  using assms(2) by auto[1]

lemma spfcomp_sbrename_getch_l:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and m::"'mOut \<Rightarrow> 'mIn"
assumes "\<And>c. ctype (Rep (m c)) \<subseteq> ctype (Rep c)"
    and "Rep c \<in> chDom TYPE('mOut)"
    and "Rep (m (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'fIn) - 'mOut \<union> 'fOut)"
  shows "(sbRenameCh m \<otimes> f)\<cdot>sb  \<^enum>\<^sub>\<star> c = sb  \<^enum>\<^sub>\<star> m (Abs (Rep c))"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_getchl[OF assms(2)])
  apply(subst sbrenamech_getch2[OF assms(2) assms(1)], simp)
  by(rule sbunion_minus_getchl[OF assms(3)])

lemma spfcomp_sbrename_getch_lr:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and m::"'mOut \<Rightarrow> 'mIn"
assumes "\<And>c. ctype (Rep (m c)) \<subseteq> ctype (Rep c)"
    and "Rep c \<in> chDom TYPE('mOut)"
    and "Rep (m (Abs (Rep c))) \<notin> chDom TYPE(('mIn \<union> 'fIn) - 'mOut \<union> 'fOut)"
    and "Rep (m (Abs (Rep c))) \<in> chDom TYPE('mIn \<union> 'fIn)"
    and "Rep (m (Abs (Rep c))) \<notin> chDom TYPE('mOut)"
    and "chDom TYPE('fIn) \<inter> chDom TYPE('mOut \<union> 'fOut) = {}"
  shows "(sbRenameCh m \<otimes> f)\<cdot>sb  \<^enum>\<^sub>\<star> c = f\<cdot>(sb\<star>)  \<^enum>\<^sub>\<star> m (Abs (Rep c))"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_getchl[OF assms(2)])
  apply(subst sbrenamech_getch2[OF assms(2) assms(1)], simp)
  apply(subst sbunion_minus_getchr)
  using assms(4) apply auto[1]
  using assms(3) apply auto[1]
  by(rule spfcomp_getch_r[OF assms(5, 6)])

lemma spfcomp_sbrename_getch_rl:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and m::"'mOut \<Rightarrow> 'mIn"
assumes "\<And>c. ctype (Rep (m c)) \<subseteq> ctype (Rep c)"
    and "Rep c \<notin> chDom TYPE('mOut)"
    and "chDom TYPE('fIn) \<subseteq> chDom TYPE('mOut)"
    and "\<And>c::'fIn. Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (m (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'fIn) - 'mOut \<union> 'fOut)"
  shows "(sbRenameCh m \<otimes> f)\<cdot>sb  \<^enum>\<^sub>\<star> c = f\<cdot>(sbRenameCh m\<cdot>(sb\<star>)\<star>)  \<^enum>\<^sub>\<star> c"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_getchr[OF assms(2)])
  apply(rule spf_arg_cong, simp)
  apply(subst sbunion_getchr)
  using assms(3) apply auto[1]
  apply(subst spfcomp_sbrename_getch_l[OF assms(1)])
  using assms(3) apply auto[1]
  using assms(4) apply auto[1]
  apply(subst sbrenamech_getch2[OF _ assms(1)])
  using assms(3) apply auto[1]
  by simp

lemma spfcomp_sbrename_getch_lrl:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and m::"'mOut \<Rightarrow> 'mIn"
assumes "\<And>c. ctype (Rep (m c)) \<subseteq> ctype (Rep c)"
    and "Rep c \<in> chDom TYPE('mOut)"
    and "Rep (m (Abs (Rep c))) \<notin> chDom TYPE(('mIn \<union> 'fIn) - 'mOut \<union> 'fOut)"
    and "Rep (m (Abs (Rep c))) \<in> chDom TYPE('mIn \<union> 'fIn)"
    and "Rep (m (Abs (Rep c))) \<notin> chDom TYPE('mOut)"
    and "chDom TYPE('fIn) \<subseteq> chDom TYPE('mOut)"
    and "\<And>c::'fIn. Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (m (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'fIn) - 'mOut \<union> 'fOut)"
  shows "(sbRenameCh m \<otimes> f)\<cdot>sb  \<^enum>\<^sub>\<star> c = f\<cdot>(sbRenameCh m\<cdot>(sb\<star>)\<star>)  \<^enum>\<^sub>\<star> m (Abs (Rep c))"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_getchl[OF assms(2)])
  apply(subst sbrenamech_getch2[OF assms(2) assms(1)], simp)
  apply(subst sbunion_minus_getchr)
  using assms(4) apply auto[1]
  using assms(3) apply auto[1]
  apply(rule spfcomp_sbrename_getch_rl[OF assms(1)])
  using assms(5) apply auto[1]
  using assms(6) apply auto[1]
  using assms(7) by fastforce


theorem spfcomp_belowI: 
  fixes    f  ::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and    g  ::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "f\<cdot>(sb \<uplus>\<^sub>- out\<star>\<^sub>1) \<sqsubseteq> (out\<star>\<^sub>1)"
      and "g\<cdot>(sb \<uplus>\<^sub>- out\<star>\<^sub>2) \<sqsubseteq> (out\<star>\<^sub>2)"
  shows   "(f\<otimes>g)\<cdot>sb \<sqsubseteq> out"
  apply(simp add: spfComp_def2)
  apply(rule fix_least_below)
  apply simp
  apply(subst sbunion_belowI2; simp add: assms)
  done

theorem spfcomp_eqI:  
  fixes    f  ::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and     g  ::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  and     out::"('fOut \<union> 'gOut)\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
  and     "f\<cdot>(sb \<uplus>\<^sub>- out\<star>\<^sub>1) =(out\<star>\<^sub>1)"
  and     "g\<cdot>(sb \<uplus>\<^sub>- out\<star>\<^sub>2) = (out\<star>\<^sub>2)"
  and     "\<And>z. f\<cdot>(sb \<uplus>\<^sub>\<star> z) = (z\<star>\<^sub>1) \<and> g\<cdot>(sb \<uplus>\<^sub>\<star> z) = (z\<star>\<^sub>2) \<Longrightarrow> out \<sqsubseteq> z"
  shows   "((f\<otimes>g)\<cdot>sb) = out"
  apply(subst spfComp_def2)
  apply(simp add: spfConvert_def)
  apply(rule fix_eqI)
  apply (insert assms,simp_all)
  by (metis assms(1) union_minus_nomagfst union_minus_nomagsnd sbunion_fst sbunion_snd)



lemma arg_congsbeq: "x \<triangleq> y \<Longrightarrow> (f\<cdot>x) \<triangleq> (f\<cdot>y)"
  apply(simp add: sbEQ_def,auto)
  by (metis sb_rep_eqI sbgetch_insert2)

lemma ubunion_minus_project1:
  fixes x::"(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)\<^sup>\<Omega>"
  and xa::"('fOut \<union> 'gOut)\<^sup>\<Omega>"
  shows "x \<uplus>\<^sub>- xa\<star>\<^sub>1 = ((x\<star>) \<uplus>\<^sub>- (xa\<star>\<^sub>\<rightleftharpoons>)\<star>\<^sub>2)"
  apply(rule sb_eqI)
  apply(subst union_minus_nomagfst[symmetric])
  apply(subst union_minus_nomagsnd[symmetric])
  apply(rename_tac c)
  apply(case_tac "Rep c \<in> chDom (TYPE(('fIn \<union> 'gIn) - ('fOut \<union> 'gOut)))")
  by (auto)

lemma ubunion_minus_project2:
  fixes x::"(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)\<^sup>\<Omega>"
  and xa::"('fOut \<union> 'gOut)\<^sup>\<Omega>"
  shows "x \<uplus>\<^sub>- xa\<star>\<^sub>2 = ((x\<star>) \<uplus>\<^sub>- (xa\<star>\<^sub>\<rightleftharpoons>)\<star>\<^sub>1)"
  apply(rule sb_eqI)
  apply(subst union_minus_nomagfst[symmetric])
  apply(subst union_minus_nomagsnd[symmetric])
  apply(rename_tac c)
  apply(case_tac "Rep c \<in> chDom (TYPE(('fIn \<union> 'gIn) - ('fOut \<union> 'gOut)))")
  by (auto)

lemma spfcomp_commut_convert_general:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "chDom TYPE('Out) \<inter> chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and "\<not>chDomEmpty TYPE('Out \<union> 'fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut \<union> 'gOut) \<subseteq> chDom TYPE('Out)"
    and "\<not>chDomEmpty TYPE('Out \<union> 'gOut) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('fOut \<union> 'gOut) \<subseteq> chDom TYPE('Out)"
  shows "spfConvert\<cdot>(f \<otimes> g) = (spfConvert\<cdot>(g \<otimes> f)::'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)"
  apply(rule cfun_eqI)
  apply(simp add: spfComp_def2 spfConvert_def)
  apply(rule parallel_fix_ind)
  apply(auto)[3]
  apply(rule sb_eqI)
  apply(rename_tac in1 out1 out2 c)
  apply(case_tac "Rep c \<in> chDom TYPE('fOut)"; case_tac "Rep c \<in> chDom TYPE('gOut)"; simp)
  using assms(1) apply fastforce
  apply(rule spf_arg_cong; simp)
  apply(case_tac "Rep ca \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)"; simp)
  apply(case_tac "Rep ca \<in> chDom TYPE(('gIn \<union> 'fIn) - 'gOut \<union> 'fOut)"; simp)
  apply(case_tac "Rep ca \<in> chDom TYPE('Out)")
  apply (metis sbtypecast_getch2)
  using assms(2) apply fastforce
  apply(rule spf_arg_cong; simp)
  apply(case_tac "Rep ca \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)"; simp)
  apply(case_tac "Rep ca \<in> chDom TYPE(('gIn \<union> 'fIn) - 'gOut \<union> 'fOut)"; simp)
  apply(case_tac "Rep ca \<in> chDom TYPE('Out)")
  apply (metis sbtypecast_getch2)
  using assms(3) by fastforce

lemma spfcomp_commut_convert:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
  shows "f \<otimes> g = spfConvert\<cdot>(g \<otimes> f)"
  apply(subst spfcomp_commut_convert_general)
  using assms by fastforce+

theorem spfcompcommu: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
  shows "(f \<otimes> g) \<triangleq>\<^sub>f (g \<otimes> f)"
  apply(rule spfconvert2spfeq, auto)
  apply(rule spfcomp_commut_convert)
  by (simp add: assms)

text\<open>The commutativity theorem needs a disjoint output domain
assumption, because the @{const sbUnion} operator is only
commutative for disjoint domains (see \cref{thm:unioncommu}).
Furthermore, the commutativity is proven using the special equality for
\glspl{spf} \<open>(\<triangleq>\<^sub>f)\<close>. Otherwise a type error would occur, because the output
type \<open>('fOut \<union> 'gOut)\<^sup>\<Omega>\<close> is different to \<open>('gOut \<union> 'fOut)\<^sup>\<Omega>\<close>\<close>



lemma spf321_1:  
  fixes spf1::"'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and spf2::"'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and spf3::"'in3\<^sup>\<Omega> \<rightarrow> 'out3\<^sup>\<Omega>"
assumes "chDom TYPE ('out1) \<inter> chDom TYPE ('out2) = {}"
    and "chDom TYPE ('out1) \<inter> chDom TYPE ('out3) = {}"
  shows "(spf1 \<otimes> (spf2 \<otimes> spf3))\<cdot>sbIn =
         fix\<cdot>(\<Lambda> sbOut. spf1\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut) 
                     \<uplus> spf2\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut)
                     \<uplus> spf3\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))"
proof - 
  let ?f = "(\<Lambda> (b::('out2 \<union> 'out3)\<^sup>\<Omega>) a. spf1\<cdot>(sbIn \<uplus>\<^sub>- a\<star>\<^sub>1) \<uplus> b)"
  let ?g = "(\<Lambda> a b. spf2\<cdot>((sbIn \<uplus>\<^sub>- a\<star>\<^sub>2) \<uplus>\<^sub>- b\<star>\<^sub>1) \<uplus> spf3\<cdot>((sbIn \<uplus>\<^sub>- a\<star>\<^sub>2) \<uplus>\<^sub>- b\<star>\<^sub>2))"
  let ?a2b = "sbTypeCast :: ('out1 \<union>'out2 \<union> 'out3)\<^sup>\<Omega> \<rightarrow> ('out2 \<union> 'out3)\<^sup>\<Omega>"
  have "fix\<cdot>(\<Lambda> a. ?f\<cdot>(fix\<cdot>(?g\<cdot>a))\<cdot>a) = fix\<cdot>(\<Lambda> a . (?f\<cdot>(?g\<cdot>a\<cdot>(?a2b\<cdot>a))\<cdot>a))"
    apply(rule fix_reduce, simp)
    apply(rule sbunion_snd)
    by (simp add: assms(1) assms(2) inf_sup_distrib1)
  moreover have "fix\<cdot>(\<Lambda> a . (?f\<cdot>(?g\<cdot>a\<cdot>(?a2b\<cdot>a))\<cdot>a)) =
      fix\<cdot>(\<Lambda> sbOut. spf1\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut) 
                 \<uplus> spf2\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut)
                 \<uplus> spf3\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))"
    apply(rule cfun_arg_cong, rule cfun_eqI)
    apply(rule sb_eqI, auto)
    apply (simp add: sbtypecast_reduce1; fail)
    apply(auto simp add: sbGetCh.rep_eq sbunion_rep_eq)[1]
    by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)+
  ultimately show ?thesis by (simp add: spfComp_def2)
qed

lemma spf321_2:  
fixes spf1::"'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
  and spf2::"'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
  and spf3::"'in3\<^sup>\<Omega> \<rightarrow> 'out3\<^sup>\<Omega>"
shows "((spf1 \<otimes> spf2) \<otimes> spf3)\<cdot>sbIn =
       fix\<cdot>(\<Lambda> sbOut. ( spf1\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut) 
                     \<uplus> spf2\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))
                     \<uplus> spf3\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))"
proof - 
  let ?f = "(\<Lambda> (b::('out1 \<union> 'out2)\<^sup>\<Omega>) a. b \<uplus> spf3\<cdot>(sbIn \<uplus>\<^sub>- a\<star>\<^sub>2))"
  let ?g = "(\<Lambda> a b. spf1\<cdot>((sbIn \<uplus>\<^sub>- a\<star>\<^sub>1) \<uplus>\<^sub>- b\<star>\<^sub>1) \<uplus> spf2\<cdot>((sbIn \<uplus>\<^sub>- a\<star>\<^sub>1) \<uplus>\<^sub>- b\<star>\<^sub>2))"
  let ?a2b = "sbTypeCast :: (('out1 \<union>'out2) \<union> 'out3)\<^sup>\<Omega> \<rightarrow> ('out1 \<union> 'out2)\<^sup>\<Omega>"
  have "fix\<cdot>(\<Lambda> a. ?f\<cdot>(fix\<cdot>(?g\<cdot>a))\<cdot>a) = fix\<cdot>(\<Lambda> a . (?f\<cdot>(?g\<cdot>a\<cdot>(?a2b\<cdot>a))\<cdot>a))"
    by(rule fix_reduce, simp)
  moreover have "fix\<cdot>(\<Lambda> a . (?f\<cdot>(?g\<cdot>a\<cdot>(?a2b\<cdot>a))\<cdot>a)) =
      fix\<cdot>(\<Lambda> sbOut. (spf1\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut) 
                  \<uplus> spf2\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))
                  \<uplus> spf3\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))"
    apply(rule cfun_arg_cong, rule cfun_eqI)
    apply(rule sb_eqI, auto)
    apply(auto simp add: sbGetCh.rep_eq sbunion_rep_eq)[1]
    by(simp add: sbtypecast_reduce1 sbtypecast_reduce2; fail)+
  ultimately show ?thesis by(auto simp add: spfComp_def2)
qed

lemma spfcomp_assoc_sbtypecast:       
  fixes spf1::"'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and spf2::"'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and spf3::"'in3\<^sup>\<Omega> \<rightarrow> 'out3\<^sup>\<Omega>"
  assumes "chDom TYPE ('out1) \<inter> chDom TYPE ('out2) = {}"
      and "chDom TYPE ('out1) \<inter> chDom TYPE ('out3) = {}"
    shows "((spf1 \<otimes> spf2) \<otimes> spf3)\<cdot>sbIn 
        =  ((spf1 \<otimes> (spf2 \<otimes> spf3))\<cdot>(sbIn\<star>)\<star>)"
  unfolding spf321_2
  apply(subst spf321_1, simp_all add: assms)
  apply(subst fix_convert  [where b2a="sbTypeCast"])
  apply(rule cfun_eqI, simp)
  apply(rule sbtypecast_id, auto)
  apply(auto simp add: oo_def)[1]
  apply(rule parallel_fix_ind, auto)
  apply(subst sbunion_assoc_sbtypecast, auto simp add: assms)
  apply(rule arg_cong2[where f="(\<uplus>\<^sub>\<star>)"])
  apply(rule cfun_arg_cong)
  apply(rule sb_eqI, simp)
  apply(case_tac "Rep c\<in>chDom TYPE(('out1 \<union> 'out2) \<union> 'out3)", simp+)
  apply(rule arg_cong2[where f="(\<uplus>)"])
  apply(rule cfun_arg_cong)
  apply(rule sb_eqI, simp)
  apply(case_tac "Rep c\<in>chDom TYPE(('out1 \<union> 'out2) \<union> 'out3)", simp+)
  apply(rule cfun_arg_cong)
  apply(rule sb_eqI, simp)
  by (case_tac "Rep c\<in>chDom TYPE(('out1 \<union> 'out2) \<union> 'out3)", simp+)

lemma spfcomp_assoc_convertr:
  fixes f::"'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and g::"'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and h::"'in3\<^sup>\<Omega> \<rightarrow> 'out3\<^sup>\<Omega>"
assumes "chDom TYPE ('out1) \<inter> chDom TYPE ('out2) = {}"
    and "chDom TYPE ('out1) \<inter> chDom TYPE ('out3) = {}"
  shows "(f \<otimes> g) \<otimes> h = spfConvert\<cdot>(f \<otimes> g \<otimes> h)"
  apply(rule cfun_eqI)
  apply(subst spfconvert_apply)
  apply(subst spfcomp_assoc_sbtypecast)
  using assms by (auto simp add: assms)

lemma spfcomp_assoc_convertl:
  fixes f::"'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and g::"'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and h::"'in3\<^sup>\<Omega> \<rightarrow> 'out3\<^sup>\<Omega>"
assumes "chDom TYPE ('out1) \<inter> chDom TYPE ('out2) = {}"
    and "chDom TYPE ('out1) \<inter> chDom TYPE ('out3) = {}"
  shows "f \<otimes> g \<otimes> h = spfConvert\<cdot>((f \<otimes> g) \<otimes> h)"
  apply(rule spfconvert_symmetric[symmetric])
  using assms apply(simp, blast)
  using assms apply(simp, blast)
  by(rule spfcomp_assoc_convertr[OF assms])

theorem spfcomp_assoc:
  fixes f::"'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and g::"'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and h::"'in3\<^sup>\<Omega> \<rightarrow> 'out3\<^sup>\<Omega>"
  assumes "chDom TYPE ('out1) \<inter> chDom TYPE ('out2) = {}"
      and "chDom TYPE ('out1) \<inter> chDom TYPE ('out3) = {}"
    shows "((f \<otimes> g) \<otimes> h) \<triangleq>\<^sub>f (f \<otimes> (g \<otimes> h))"
  apply(rule spfconvert2spfeq, auto)
  apply(subst spfcomp_assoc_convertr)
  by (auto simp add: assms)


lemma wellformed_spfcomp_iterate:
assumes "weak f"
    and "weak g"
    and "wellformed sb"
  shows "wellformed (iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>)"
proof (induction i)
  case 0
  then show ?case
    using well_ex wellformed_sb_below by auto
next
  case (Suc i)
  have well: "wellformed (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>)"
    using Suc assms(3) wellformed_sbtypecast wellformed_union_minus by blast
  show ?case 
    apply simp
    apply(rule wellformed_union)
    apply(rule wellformed_weakI[OF assms(1) well])
    by(rule wellformed_weakI[OF assms(2) well])
qed


lemma spfcomp_invariant_eq:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "\<And>sb. J sb \<longrightarrow> f'\<cdot>sb = f\<cdot>sb"
    and "\<And>sb. L sb \<longrightarrow> g'\<cdot>sb = g\<cdot>sb"
    and "\<And>i. J (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>1)"
    and "\<And>i. L (sb \<uplus>\<^sub>- iterate i\<cdot>(\<Lambda> sbOut. f\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- sbOut\<star>\<^sub>2))\<cdot>\<bottom>\<star>\<^sub>2)"
  shows "(f' \<otimes> g')\<cdot>sb = (f \<otimes> g)\<cdot>sb"
  apply(simp add: spfComp_def2)
  apply(rule parallel_fix_ind2[where n="0"])
  apply auto[3]
  apply(rule sb_eqI)
  apply(case_tac "Rep c \<in> chDom TYPE('fOut)"; simp)
  apply(subst assms(1))
  apply(rule assms(3))
  apply simp
  apply(subst assms(2))
  apply(rule assms(4))
  by simp


lemma spfcomp_nofeed1:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes
        "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
  shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(sb\<star>) \<uplus> g\<cdot>(sb \<uplus>\<^sub>\<star> f\<cdot>(sb\<star>))"
  apply(subst spfcomp_unfold)
  apply (rule arg_cong2 [where f="(\<uplus>)"])
  subgoal X
  apply(rule arg_cong [where f="Rep_cfun f"])
  apply(rule sb_eqI, auto simp del: sbtypecast_getch2)
  apply(subst sbunion_minus_getchl2)
  using assms apply auto
  done
  apply(rule arg_cong [where f="Rep_cfun g"])
  apply(rule sb_eqI, auto)
  apply(case_tac "Rep c \<in> chDom TYPE((('fIn \<union> 'gIn) - 'fOut \<union> 'gOut))")
  apply auto[2]
  apply (metis X sbunion_getchl spfcomp_unfold)
  using assms(2) by blast


lemma spfcomp_nofeed2:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes
        "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gIn) = {}"
  shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(sb \<uplus>\<^sub>\<star> g\<cdot>(sb\<star>)) \<uplus> g\<cdot>(sb\<star>)"
  apply(subst spfcomp_unfold)
  apply (rule arg_cong2 [where f="(\<uplus>)"])
  defer
  subgoal X
  apply(rule arg_cong [where f="Rep_cfun g"])
  apply(rule sb_eqI, auto simp del: sbtypecast_getch2)
  apply(subst sbunion_minus_getchl2)
  using assms apply auto
  done
  apply(rule arg_cong [where f="Rep_cfun f"])
  apply(rule sb_eqI, auto)
  apply(case_tac "Rep c \<in> chDom TYPE((('fIn \<union> 'gIn) - 'fOut \<union> 'gOut))")
  apply auto[2]
  using assms(1) apply blast
  apply(subst spfcomp_unfold)
  apply(subst X)
  apply(subst sbunion_getchr)
  using assms apply blast
  ..

lemma spfcomp_noselfloops: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes
        "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
  and   "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
  shows "((f \<otimes> g)\<cdot>sb) = (f\<cdot>((sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>\<star> (f \<otimes> g)\<cdot>sb)))) \<uplus> g\<cdot>((sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>\<star> (f \<otimes> g)\<cdot>sb)))))"
  proof -
  have g_simps1:"(g\<cdot>(sb \<uplus>\<^sub>- (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))\<star>\<^sub>2)) = 
        (g\<cdot>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))))"
    apply (rule cfun_arg_cong)
    apply(rule sb_rep_eqI)
    by (simp add: union_minus_nomagsnd [symmetric] sbunion_rep_eq sbgetch_insert)
  have g_simps2: "g\<cdot>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))) = g\<cdot>(sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))"
    apply (subst ubunion_fst)
    apply (simp add: assms)
    by blast
  have f_simps1:"(f\<cdot>(sb \<uplus>\<^sub>- (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))\<star>\<^sub>1)) = 
        (f\<cdot>((f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)) \<uplus>\<^sub>\<star> (sb \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))))"
    apply (rule cfun_arg_cong)
    apply(rule sb_rep_eqI)
    by (simp add: union_minus_nomagfst [symmetric] sbunion_rep_eq sbgetch_insert)
  have f_simps2: "(f\<cdot>((f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)) \<uplus>\<^sub>\<star> (sb \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))))) = f\<cdot>(sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))"
    apply (subst sbunion_conv_snd)
    apply (simp add: assms)
    by blast
  show ?thesis
    apply (subst spfcomp_unfold)
    apply (subst(2) spfcomp_unfold)
    apply (subst spfcomp_unfold)
    by (simp add: g_simps1 g_simps2 f_simps1 f_simps2 union_minus_nomagfst union_minus_nomagsnd)
  qed

lemma spfcomp_noselfloops1: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes
        "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
  shows "((f \<otimes> g)\<cdot>sb) = (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>((sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
  proof -
  have g_simps1:"(g\<cdot>(sb \<uplus>\<^sub>- (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))\<star>\<^sub>2)) = 
        (g\<cdot>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))))"
    apply (rule cfun_arg_cong)
    apply(rule sb_rep_eqI)
    by (simp add: union_minus_nomagsnd [symmetric] sbunion_rep_eq sbgetch_insert)
  have g_simps2: "g\<cdot>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))) = g\<cdot>(sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))"
    apply (subst ubunion_fst)
    apply (simp add: assms; fail)
    by blast
  then show ?thesis
    apply (subst spfcomp_unfold)
    apply (subst(2) spfcomp_unfold)
    by (simp add: g_simps1 g_simps2)
  qed



theorem spfcomp_serial:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('gIn) \<subseteq> chDom TYPE ('fOut)"
    and "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
  shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(sb\<star>) \<uplus> g\<cdot>(f\<cdot>(sb\<star>)\<star>)"
  apply(subst spfcomp_nofeed1)
  apply(simp_all add: assms)
  apply (rule arg_cong2 [where f="(\<uplus>)"])
  apply (rule refl)
  apply(rule arg_cong [where f="Rep_cfun g"])
  apply(rule sb_eqI, auto)
  using assms by auto

theorem spfcomp_serial2:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fIn) \<subseteq> chDom TYPE ('gOut)"
    and "chDom TYPE ('gOut) \<inter> chDom TYPE ('fOut) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gIn) = {}"
  shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(g\<cdot>(sb\<star>)\<star>) \<uplus> g\<cdot>(sb\<star>)"
  apply(subst spfcomp_nofeed2)
  apply(simp_all add: assms)
  apply(rule arg_cong2 [where f="(\<uplus>)"])
  apply(rule arg_cong [where f="Rep_cfun f"])
  apply(rule sb_eqI, auto)
  apply(case_tac " Rep c \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)", auto)
  using assms(1) by blast

text\<open>If the input domains are pairwise disjoint @{const spfComp} is
equivalent to function composition @{const cfcomp}.\<close>
theorem spfcomp_cfcomp:
  fixes f::"'a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>"
    and g::"'b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"
assumes "chDom TYPE('a) \<inter> chDom TYPE('b) = {}"
    and "chDom TYPE('b) \<inter> chDom TYPE('c) = {}"
    and "chDom TYPE('a) \<inter> chDom TYPE('c) = {}"
  shows "spfConvert\<cdot>(f \<otimes> g) = (g oo f)"
  apply(rule cfun_eqI, simp)
  apply(simp add: spfConvert_def)
  apply(subst spfcomp_serial)
  apply(auto simp add: assms)[6]
  using assms(2) apply auto[1]
  using assms(1) apply auto[1]
  using assms(3) apply auto[1]
  apply(subst sbtypecast_id)
  apply(auto simp add: assms)[1]
  using assms(1) apply auto[1]
  using assms(3) by auto

theorem spfcomp_cfcomp_all:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "chDom TYPE('fIn) \<inter> chDom TYPE('fOut) = {}"
    and "chDom TYPE('gIn) \<inter> chDom TYPE('gOut) = {}"
    and "chDom TYPE('fIn) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('fOut) = chDom TYPE ('gIn)"
  shows "spfConvert\<cdot>(f \<otimes> g) = (g oo (spfConvert\<cdot>f ::'fIn\<^sup>\<Omega> \<rightarrow> 'gIn\<^sup>\<Omega>))"
  apply(rule cfun_eqI, simp)
  apply(simp add: spfConvert_def)
  apply(subst spfcomp_serial)
  apply(simp_all add: assms)
  using assms(2) apply auto[1]
  using assms(3) apply auto[1]
  apply(subst sbtypecast_id)
  apply(auto simp add: assms)[1]
  using assms(3) apply auto[1]
  using assms(4) by auto


definition spfCompSeq::"('In\<^sup>\<Omega> \<rightarrow> 'Intern\<^sup>\<Omega>) \<rightarrow> ('Intern\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)
  \<rightarrow> ('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)" where 
"spfCompSeq \<equiv> \<Lambda> spf1 spf2 sb. spf2\<cdot>(spf1\<cdot>sb)"

definition spfCompSeq_weak::"('I::tchan\<^sup>\<Omega> \<rightarrow>\<^sub>w 'L::tchan\<^sup>\<Omega>) \<rightarrow> ('L\<^sup>\<Omega> \<rightarrow>\<^sub>w 'O::tchan\<^sup>\<Omega>)
  \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow>\<^sub>w 'O\<^sup>\<Omega>)" where 
"spfCompSeq_weak \<equiv> \<Lambda> spf1 spf2. Abs_tspfw(spfCompSeq\<cdot>(Rep_tspfw spf1)\<cdot>(Rep_tspfw spf2))"

lemma spfcompseq_cont_fst[simp]:
  shows "cont (\<lambda> spf1 . (\<Lambda> spf2 sb . spf2\<cdot>(spf1\<cdot>sb)))"
  by (intro cont2cont)

lemma spfcompseq_cont_snd[simp]:
  shows "cont (\<lambda> spf1 . (\<lambda> spf2 . (\<Lambda> sb . spf2\<cdot>(spf1\<cdot>sb))))"
  by (intro cont2cont)

lemma spfcompseq_insert: "spfCompSeq\<cdot>spf1\<cdot>spf2 = spf2 oo spf1"
  by(simp add: spfCompSeq_def oo_def)

lemma spfcompseq_assoc_spfconvert:
  shows "spfCompSeq\<cdot>(spfCompSeq\<cdot>f\<cdot>g)\<cdot>h = spfConvert\<cdot>(spfCompSeq\<cdot>f\<cdot>(spfCompSeq\<cdot>g\<cdot>h))"
  by (simp add: spfCompSeq_def)

corollary spfcompseq_assoc:
  shows "spfCompSeq\<cdot>(spfCompSeq\<cdot>f\<cdot>g)\<cdot>h \<triangleq>\<^sub>f (spfCompSeq\<cdot>f\<cdot>(spfCompSeq\<cdot>g\<cdot>h))"
  apply(rule spfconvert2spfeq, auto)
  by (simp add: spfcompseq_assoc_spfconvert)

text \<open>In the sequential case the general composition @{const spfComp}
 is equivalent to @{const spfCompSeq}. The output of the general
composition is restricted to \<open>'Out\<close>, because the general
composition also returns the internal channels.\<close> 

theorem spfcomp_to_sequential:
  fixes f::"'In\<^sup>\<Omega> \<rightarrow> 'Intern\<^sup>\<Omega>"
    and g::"'Intern\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>"
  assumes "chDom TYPE ('In) \<inter> chDom TYPE ('Intern) = {}"
    and "chDom TYPE('In) \<inter> chDom TYPE('Out) = {}"
    and "chDom TYPE('Intern) \<inter> chDom TYPE('Out) = {}"
  shows "((f \<otimes> g)\<cdot>(sb\<star>) \<bar> TYPE('Out)) = spfCompSeq\<cdot>f\<cdot>g\<cdot>sb"
  apply(subst spfcomp_serial)
  using assms apply auto[6]
  unfolding spfCompSeq_def
  apply(subst sbtypecast_id)
  by auto 


theorem spfcomp_parallel:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gIn) = {}"
      and "chDom TYPE ('fOut) \<inter> chDom TYPE ('fIn) = {}"
      and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
      and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
    shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(sb\<star>) \<uplus> g\<cdot>(sb\<star>)"
  apply(subst spfcomp_nofeed1)
  by (simp_all add: assms)



definition spfCompPar:: "('In1\<^sup>\<Omega> \<rightarrow> 'Out1\<^sup>\<Omega>) \<rightarrow> ('In2\<^sup>\<Omega> \<rightarrow> 'Out2\<^sup>\<Omega>) \<rightarrow> 
  ('In1 \<union> 'In2)\<^sup>\<Omega> \<rightarrow> ('Out1 \<union> 'Out2)\<^sup>\<Omega>" where
"spfCompPar \<equiv> \<Lambda> spf1 spf2 sb. spf1\<cdot>(sb\<star>\<^sub>1) \<uplus>  spf2\<cdot>(sb\<star>\<^sub>2)"

definition spfCompPar_weak:: "('I::tchan\<^sup>\<Omega> \<rightarrow>\<^sub>w 'O::tchan\<^sup>\<Omega>) \<rightarrow> ('J::tchan\<^sup>\<Omega> \<rightarrow>\<^sub>w 'P::tchan\<^sup>\<Omega>) \<rightarrow> 
  ('I \<union> 'J)\<^sup>\<Omega> \<rightarrow>\<^sub>w ('O \<union> 'P)\<^sup>\<Omega>" where
"spfCompPar_weak = (\<Lambda> spf1 spf2. Abs_tspfw (spfCompPar\<cdot>(Rep_tspfw spf1)\<cdot>(Rep_tspfw spf2)))"

lemma spfcomppar_cont: 
  "cont (\<lambda> spf1 spf2 sb. spf1\<cdot>(sb\<star>\<^sub>1) \<uplus>  spf2\<cdot>(sb\<star>\<^sub>2))"
  by(intro cont2cont)
  
theorem spfcomp_to_parallel:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gIn) = {}"
      and "chDom TYPE ('fOut) \<inter> chDom TYPE ('fIn) = {}"
      and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
      and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
    shows "((f \<otimes> g)\<cdot>(sb\<star>) \<bar> TYPE('fOut \<union> 'gOut)) = spfCompPar\<cdot>f\<cdot>g\<cdot>sb"
  apply(subst spfcomp_parallel)
  using assms apply auto[5]
  unfolding spfCompPar_def
  apply simp
  by (rule cfun_arg_cong2; subst sb_star21; auto)

theorem spfcomppar_to_spfcomp:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gIn) = {}"
      and "chDom TYPE ('fOut) \<inter> chDom TYPE ('fIn) = {}"
      and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
      and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
    shows "spfCompPar\<cdot>f\<cdot>g = spfConvert\<cdot>(f \<otimes> g)"
  apply(rule cfun_eqI)
  apply(subst spfconvert_apply)
  apply(subst spfCompPar_def)
  apply(subst beta_cfun, auto)
  apply(subst spfcomp_parallel)
  using assms apply auto[5]
  apply(rule cfun_arg_cong2)
  apply(rule cfun_arg_cong)
  apply(subst sb_star21, auto)
  apply(rule cfun_arg_cong)
  apply(subst sb_star21, auto)
  done
  
lemma spfcomppar_commu_spfconvert:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
  shows "spfCompPar\<cdot>f\<cdot>g = spfConvert\<cdot>(spfCompPar\<cdot>g\<cdot>f)"
  apply(simp add: spfCompPar_def)
  apply(rule cfun_eqI, auto)
  apply(subst spfconvert_apply, auto)
  apply(subst sbunion_commu_sbtypecast)
  using assms apply auto[1]
  apply(rule sb_eqI)
  apply(case_tac " Rep c \<in> chDom TYPE('gOut)", auto)
  apply(rule cfun_arg_cong)+
  apply(rule sb_eqI, simp add: sbgetch_insert)
  apply(rule cfun_arg_cong)+
  by (rule sb_eqI, simp add: sbgetch_insert)

corollary spfcomppar_commu:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
  shows "spfCompPar\<cdot>f\<cdot>g \<triangleq>\<^sub>f spfCompPar\<cdot>g\<cdot>f"
  apply(rule spfconvert2spfeq)
  using assms apply(auto)[3]
  by (rule spfcomppar_commu_spfconvert, auto)

lemma spfcomppar_assoc_spfconvert:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
    and h::"'hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>"
assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
    and "chDom TYPE ('fOut) \<inter> chDom TYPE ('hOut) = {}"
  shows "spfCompPar\<cdot>(spfCompPar\<cdot>f\<cdot>g)\<cdot>h = spfConvert\<cdot>(spfCompPar\<cdot>f\<cdot>(spfCompPar\<cdot>g\<cdot>h))"
  apply(simp add: spfCompPar_def)
  apply(subst sbunion_assoc_sbtypecast)
  using assms apply auto[2]
  apply(rule cfun_eqI, auto)
  apply(subst spfconvert_apply, auto)
  apply(rule cfun_arg_cong)
  apply(rule cfun_arg_cong2)
  apply(rule cfun_arg_cong)
  apply(rule sb_eqI, simp add: sbgetch_insert)
  apply(rule cfun_arg_cong2)
  apply(rule cfun_arg_cong)
  apply(rule sb_eqI, simp add: sbgetch_insert)
  apply(rule cfun_arg_cong)
  by (rule sb_eqI, simp add: sbgetch_insert)

corollary spfcomppar_assoc:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
    and h::"'hIn\<^sup>\<Omega> \<rightarrow> 'hOut\<^sup>\<Omega>"
assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
    and "chDom TYPE ('fOut) \<inter> chDom TYPE ('hOut) = {}"
  shows "spfCompPar\<cdot>(spfCompPar\<cdot>f\<cdot>g)\<cdot>h  \<triangleq>\<^sub>f (spfCompPar\<cdot>f\<cdot>(spfCompPar\<cdot>g\<cdot>h))"
  apply(rule spfconvert2spfeq)
  using assms apply(auto)[3]
  by (rule spfcomppar_assoc_spfconvert, auto)

lemma spfcomp_parallel_serial: 
  fixes f1 :: "'fin\<^sup>\<Omega> \<rightarrow> 'fintern\<^sup>\<Omega>"
  and   g1 :: "'gin\<^sup>\<Omega> \<rightarrow> 'gintern\<^sup>\<Omega>"
  and   f2 :: "'fintern\<^sup>\<Omega> \<rightarrow> 'fout\<^sup>\<Omega>"
  and   g2 :: "'gintern\<^sup>\<Omega> \<rightarrow> 'gout\<^sup>\<Omega>"
  assumes "chDom TYPE ('gintern) \<inter> chDom TYPE ('fintern) = {}"
  shows "spfCompPar\<cdot>(f2 oo f1)\<cdot>(g2 oo g1) 
       = spfCompPar\<cdot>f2\<cdot>g2 oo spfCompPar\<cdot>f1\<cdot>g1"
  apply(simp add: spfCompPar_def oo_def)
  using assms by (simp add: inf_commute)

definition spfCompFeed ::"('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) \<rightarrow> ('In-'Out)\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>" where
"spfCompFeed \<equiv> \<Lambda> spf sb. \<mu> sbOut. spf\<cdot>(sb \<uplus>\<^sub>- sbOut)"

lemma spfcompfeed_cont:" cont (\<lambda> spf sb. \<mu> sbOut. spf\<cdot>(sb \<uplus>\<^sub>- sbOut))"
  by(intro cont2cont)

theorem spfcomp_to_feedback:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('gOut) = {}"
  shows "((f \<otimes> g)\<cdot>(sb\<star>) \<bar> TYPE('fOut)) = spfCompFeed\<cdot>f\<cdot>sb"
  apply(simp only: spfComp_def2 spfCompFeed_def)
  apply(simp add: sbunion_emptyr assms)
  apply(rule parallel_fix_ind, auto)
  apply(subst sb_star21, auto)
  apply(rule cfun_arg_cong)
  apply(rule sb_eqI, auto simp add: sbGetCh.rep_eq sbunion_rep_eq)
  using assms by blast

lemma spfcomp_self_fix:
  fixes f::"'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
  shows "(f \<otimes> f)\<cdot>sb = ((\<mu> sbOut . f\<cdot>((sb\<star>) \<uplus>\<^sub>- sbOut ))\<star>)"
  apply(subst spfComp_def2, auto)
  apply(subst sbunion_sbtypecast_idemp)
  apply(rule parallel_fix_ind, auto)
  apply(rule cfun_arg_cong)+
  apply(rule sb_eqI)
  by (case_tac "Rep c \<in> chDom TYPE((('in1 \<union> 'in1) - 'out1 \<union> 'out1))", auto)

theorem spfcomp_to_feedback2:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  shows "spfConvert\<cdot>(f \<otimes> f)\<cdot>(sb) = spfCompFeed\<cdot>f\<cdot>sb"
  apply(subst spfconvert_apply)
  apply(subst spfcomp_self_fix)
  apply(subst sbtypecast_id, auto)
  by (simp add: spfCompFeed_def)



lemma spfcomp_causal: 
  assumes "strong f" and "strong g"
  shows "strong (f \<otimes> g)"
proof (rule ccontr)
  assume not_strong: "\<not>strong (f \<otimes> g)"
  then obtain sb where sb_pred: "lnsuc\<cdot>(#\<^sub>\<surd>sb) > #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
    by (metis strong_def leI)
  have comp_min_len: 
    "min (#\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))) \<le> #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
    by (metis min.cobounded1 min_def sbunion_tlen_fst_leq_old
        sbunion_tlen_snd_leq spfComp.simps)
  have strong_f:
    "lnsuc\<cdot>(#\<^sub>\<surd>((sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) \<le> #\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))"
    using assms(1) strong_def by blast
  have strong_g: 
    "lnsuc\<cdot>(#\<^sub>\<surd>((sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))) \<le> #\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))"
    using assms(2) strong_def by blast
  hence sb_unionlen_lnsuc_min_leq: 
    "min (lnsuc\<cdot>(#\<^sub>\<surd>((sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))) (lnsuc\<cdot>(#\<^sub>\<surd>((sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))) \<le> #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
    using comp_min_len min.mono order.trans assms strong_f by blast
  hence sb_unionlen_min_lnsuc_leq:
    "lnsuc\<cdot>(min (#\<^sub>\<surd>((sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) (#\<^sub>\<surd>((sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))) \<le> #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
    by (metis lnsuc_lnle_emb min_def)
  have sbtypecast_snd_len:
    "lnsuc\<cdot>(#\<^sub>\<surd>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb)) \<le> lnsuc\<cdot>(#\<^sub>\<surd>((sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))"
    by (simp, rule sbtypecast_tlen, simp)
  have sbtypecast_fst_len:
    "lnsuc\<cdot>(#\<^sub>\<surd>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb)) \<le> lnsuc\<cdot>(#\<^sub>\<surd>((sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))"
    by (simp, rule sbtypecast_tlen, simp)
  hence sbunion_lnsuc_comp_leq:
    "lnsuc\<cdot>(#\<^sub>\<surd>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb)) \<le> #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
    using dual_order.trans  sbtypecast_snd_len min.bounded_iff
          sb_unionlen_lnsuc_min_leq by blast
  have "min (#\<^sub>\<surd>sb) (#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)) \<le> #\<^sub>\<surd>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb)"
    by (simp add: min_def sbunion_minus_tlen_fst_leq sbunion_minus_tlen_snd_leq)
  hence "lnsuc\<cdot>(min (#\<^sub>\<surd>sb) (#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))) \<le> #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
    using lnsuc_lnle_emb order_subst2 sbunion_lnsuc_comp_leq by blast
  thus False
    by (metis less2eq less_lnsuc lnle2le min.absorb2
        min.strict_order_iff min_rek sb_pred)
qed

lemma spfcomp_feed_weak1: 
  fixes f::"'fIn::tchan\<^sup>\<Omega> \<rightarrow> 'fOut::tchan\<^sup>\<Omega>"
    and g::"'gIn::tchan\<^sup>\<Omega> \<rightarrow> 'gOut::tchan\<^sup>\<Omega>"
  assumes
        "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    and "strong f" and "weak g"
  shows "weak (f \<otimes> g)"
  proof (rule weakI)
  fix sb
  have g_simps1:"(g\<cdot>(sb \<uplus>\<^sub>- (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))\<star>\<^sub>2)) = 
        (g\<cdot>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))))"
    apply (rule cfun_arg_cong)
    apply(rule sb_rep_eqI)
    by (simp add: union_minus_nomagsnd [symmetric] sbunion_rep_eq sbgetch_insert)
  have g_simps2: "g\<cdot>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))) = g\<cdot>(sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))"
    apply (subst ubunion_fst)
    apply (simp add: assms; fail)
    by blast
  have comp_def:"((f \<otimes> g)\<cdot>sb) = (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>((sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
    apply (subst spfcomp_unfold)
    apply (subst(2) spfcomp_unfold)
    by (simp add: g_simps1 g_simps2)
  have mina: "min (#\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) 
            (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))
        \<le>   #\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>((sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
     by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
  have strong_f:
      "(lnsuc\<cdot>(#\<^sub>\<surd>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) \<le> (#\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))"
    using assms(2) strong_def by blast
  have typecast_f:"(#\<^sub>\<surd>(sb \<uplus> (f \<otimes> g)\<cdot>sb)) \<le> (#\<^sub>\<surd>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))"
    apply (simp add: union_minus_nomagfst [symmetric])
    apply (rule sbtypecast_tlen)
    by auto
  have "min (#\<^sub>\<surd>sb) (#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)) \<le> (#\<^sub>\<surd>(sb \<uplus> (f \<otimes> g)\<cdot>sb))"
    by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
  then have "min (lnsuc\<cdot>(#\<^sub>\<surd>sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))) \<le> lnsuc\<cdot>(#\<^sub>\<surd>(sb \<uplus> (f \<otimes> g)\<cdot>sb))"
    by (metis lnsuc_lnle_emb min_def)
  then have min_f:"min (lnsuc\<cdot>(#\<^sub>\<surd>sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))) \<le> (#\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))"
    by (meson lnsuc_lnle_emb order.trans strong_f typecast_f)
  have weak_g: "(#\<^sub>\<surd>((sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))::'gIn\<^sup>\<Omega>)) \<le> (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
    using assms(3) weak_def by blast
  have typecast_g:"(#\<^sub>\<surd>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))))) \<le> (#\<^sub>\<surd>((sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))::'gIn\<^sup>\<Omega>))"
    apply (rule sbtypecast_tlen)
    using assms(1) by auto
  have minb: "min (#\<^sub>\<surd>(sb)) (#\<^sub>\<surd>((f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))) \<le> (#\<^sub>\<surd>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
    by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
  then have "min (#\<^sub>\<surd>(sb)) (min (lnsuc\<cdot>(#\<^sub>\<surd>sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) \<le> (#\<^sub>\<surd>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
    apply (subst min_trans,simp_all)
    apply blast
    by (simp add: min_f)
  then have "min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))) \<le> (#\<^sub>\<surd>((sb \<uplus> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
    by (metis (no_types, opaque_lifting) less_lnsuc min.assoc min_def)
  then have "min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))) \<le> (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
    using order.trans typecast_g weak_g by blast
  then have min_min: "min (min (lnsuc\<cdot>(#\<^sub>\<surd>sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) (min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) \<le> 
             #\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>((sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
    apply (subst min_trans,simp_all)
    using min_f mina by auto
  have "min (min (lnsuc\<cdot>(#\<^sub>\<surd>sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) (min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) 
       = (min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))))"
    apply (rule min.absorb2)
    using less_lnsuc min.mono by blast
  then have "(min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) \<le> #\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>((sb \<uplus>\<^sub>\<star> (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)))))"
    using min_min by presburger
  then show " #\<^sub>\<surd>sb \<le> #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
    apply (simp add: comp_def [symmetric])
  by (metis le_cases less_lnsuc min.commute min_absorb2 min_rek)
qed

lemma spfcomp_feed_weak2: 
  fixes f::"'fIn::tchan\<^sup>\<Omega> \<rightarrow> 'fOut::tchan\<^sup>\<Omega>"
  and g::"'gIn::tchan\<^sup>\<Omega> \<rightarrow> 'gOut::tchan\<^sup>\<Omega>"
  assumes
        "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
    and "weak f"
    and "strong g"
  shows "weak (f \<otimes> g)"
  proof (rule weakI)
  fix sb
  have f_simps1:"(f\<cdot>(sb \<uplus>\<^sub>- (f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus> g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))\<star>\<^sub>1)) = 
         f\<cdot>(f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1) \<uplus>\<^sub>\<star> sb \<uplus> g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))"
    apply (rule cfun_arg_cong)
    apply(rule sb_rep_eqI)
    by (simp add: union_minus_nomagfst [symmetric] sbunion_rep_eq sbgetch_insert)
  have f_simps2: "f\<cdot>(((f\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1))) \<uplus>\<^sub>\<star> (sb \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))) = f\<cdot>(sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))"
    apply (subst sbunion_conv_snd)
    apply (simp add: assms; fail)
    by blast
  have comp_def: "((f \<otimes> g)\<cdot>sb) = f\<cdot>((sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))) \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))"
    apply (subst spfcomp_unfold)
    apply (subst spfcomp_unfold)
    by (simp add: f_simps1 f_simps2)
  have mina: "min ( #\<^sub>\<surd>(f\<cdot>((sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))))) (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))
              \<le> #\<^sub>\<surd>(f\<cdot>((sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))) \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))"
    by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
  have strong_g:
      "(lnsuc\<cdot>(#\<^sub>\<surd>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))) \<le> (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))"
    using assms(3) strong_def by blast
  have typecast_g:"(#\<^sub>\<surd>(sb \<uplus> (f \<otimes> g)\<cdot>sb)) \<le> (#\<^sub>\<surd>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))"
    apply (simp add: union_minus_nomagsnd [symmetric])
    apply (rule sbtypecast_tlen)
    by auto
  have "min (#\<^sub>\<surd>sb) (#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)) \<le> (#\<^sub>\<surd>(sb \<uplus> (f \<otimes> g)\<cdot>sb))"
    by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
  then have "min (lnsuc\<cdot>(#\<^sub>\<surd>sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))) \<le> lnsuc\<cdot>(#\<^sub>\<surd>(sb \<uplus> (f \<otimes> g)\<cdot>sb))"
    by (metis lnsuc_lnle_emb min_def)
  then have min_g:"min (lnsuc\<cdot>(#\<^sub>\<surd>sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))) \<le> (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))"
    by (meson lnsuc_lnle_emb order.trans strong_g typecast_g)
  have weak_f: "(#\<^sub>\<surd>((sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))::'fIn\<^sup>\<Omega>)) \<le> (#\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))))"
    using assms(2) weak_def by blast
  have typecast_f:"(#\<^sub>\<surd>((sb \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2))))) \<le> (#\<^sub>\<surd>((sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))::'fIn\<^sup>\<Omega>))"
    apply (rule sbtypecast_tlen)
    using assms(1) by auto
  have minb: "min (#\<^sub>\<surd>(sb)) (#\<^sub>\<surd>((g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))) \<le> (#\<^sub>\<surd>((sb \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))))"
    by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
  then have "min (#\<^sub>\<surd>(sb)) (min (lnsuc\<cdot>(#\<^sub>\<surd>sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) \<le> (#\<^sub>\<surd>((sb \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))))"
    apply (subst min_trans,simp_all)
    apply blast
    by (simp add: min_g)
  then have "min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))) \<le> (#\<^sub>\<surd>((sb \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))))"
    by (metis (no_types, opaque_lifting) less_lnsuc min.assoc min_def)
  then have "min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))) \<le> (#\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))))"
    using order.trans typecast_f weak_f by blast
  then have min_min: "min (min (#\<^sub>\<surd>sb) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) (min (lnsuc\<cdot>(#\<^sub>\<surd>sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) \<le> 
            #\<^sub>\<surd>(f\<cdot>((sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))) \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))"
    apply (subst min_trans,simp_all)
    using min_g mina by auto
  have "min (min (#\<^sub>\<surd>sb) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) (min (lnsuc\<cdot>(#\<^sub>\<surd>(sb))) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) 
       = (min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb))))"
    apply (rule min.absorb1)
    using less_lnsuc min.mono by blast
  then have "(min (#\<^sub>\<surd>(sb)) (lnsuc\<cdot>(#\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)))) \<le> #\<^sub>\<surd>(f\<cdot>((sb \<uplus>\<^sub>\<star> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))) \<uplus> (g\<cdot>(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)))"
    using min_min by presburger
  then show " #\<^sub>\<surd>sb \<le> #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
    apply (simp add: comp_def [symmetric])
  by (metis le_cases less_lnsuc min.commute min_absorb2 min_rek)
qed

lemma spfcomp_nofeed_weak1: 
  fixes f::"'fIn::tchan\<^sup>\<Omega> \<rightarrow> 'fOut::tchan\<^sup>\<Omega>"
    and g::"'gIn::tchan\<^sup>\<Omega> \<rightarrow> 'gOut::tchan\<^sup>\<Omega>"
  assumes
        "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
    and "weak f" and "weak g"
  shows "weak (f \<otimes> g)"
  proof (rule weakI)
    fix sb
    have comp_def:"((f \<otimes> g)\<cdot>sb) = (f\<cdot>(sb\<star>) \<uplus> g\<cdot>(sb \<uplus>\<^sub>\<star> f\<cdot>(sb\<star>)))"
      by (simp add: assms spfcomp_nofeed1)
    have mina:"min (#\<^sub>\<surd>(f\<cdot>(sb\<star>))) (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>\<star> f\<cdot>(sb\<star>)))) \<le> #\<^sub>\<surd>(f\<cdot>(sb\<star>) \<uplus> g\<cdot>(sb \<uplus>\<^sub>\<star> f\<cdot>(sb\<star>)))"
      by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
    have weak_f: "(#\<^sub>\<surd>((sb\<star>)::'fIn\<^sup>\<Omega>)) \<le> (#\<^sub>\<surd>(f\<cdot>(sb\<star>)))"
      using assms(4) weak_def by blast
    have typecast_f: "#\<^sub>\<surd>sb \<le> (#\<^sub>\<surd>((sb\<star>)::'fIn\<^sup>\<Omega>))"
      apply (rule sbtypecast_tlen)
      using assms by auto
    then have f_leq: "#\<^sub>\<surd>sb \<le> (#\<^sub>\<surd>(f\<cdot>(sb\<star>)))"
      using weak_f by auto
    have weak_g: "(#\<^sub>\<surd>((sb \<uplus>\<^sub>\<star> f\<cdot>(sb\<star>))::'gIn\<^sup>\<Omega>)) \<le> (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>\<star> f\<cdot>(sb\<star>))))"
      using assms(5) weak_def by blast
    have typecast_g: "(#\<^sub>\<surd>(sb \<uplus> f\<cdot>(sb\<star>))) \<le> (#\<^sub>\<surd>((sb \<uplus>\<^sub>\<star> f\<cdot>(sb\<star>))::'gIn\<^sup>\<Omega>))"
      apply (rule sbtypecast_tlen)
      using assms by auto
    have "min (#\<^sub>\<surd>sb) (#\<^sub>\<surd>(f\<cdot>(sb\<star>))) \<le> (#\<^sub>\<surd>(sb \<uplus> f\<cdot>(sb\<star>)))" 
      by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
    then have "(#\<^sub>\<surd>sb) \<le> (#\<^sub>\<surd>(sb \<uplus> f\<cdot>(sb\<star>)))"
      using typecast_f weak_f by auto
    then have g_leq:"(#\<^sub>\<surd>sb) \<le> (#\<^sub>\<surd>(g\<cdot>(sb \<uplus>\<^sub>\<star> f\<cdot>(sb\<star>))))"
      using typecast_g weak_g by auto
    have "min (#\<^sub>\<surd>sb) (#\<^sub>\<surd>sb) \<le> #\<^sub>\<surd>(f\<cdot>(sb\<star>) \<uplus> g\<cdot>(sb \<uplus>\<^sub>\<star> f\<cdot>(sb\<star>)))"
      apply (rule min_trans)
      using mina apply blast
      using f_leq g_leq by auto
    then show "#\<^sub>\<surd>sb \<le> #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
      by (simp add: local.comp_def)
  qed   

lemma spfcomp_nofeed_weak2: 
  fixes f::"'fIn::tchan\<^sup>\<Omega> \<rightarrow> 'fOut::tchan\<^sup>\<Omega>"
  and g::"'gIn::tchan\<^sup>\<Omega> \<rightarrow> 'gOut::tchan\<^sup>\<Omega>"
  assumes
        "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gIn) = {}"
    and "weak f"
    and "weak g"
  shows "weak (f \<otimes> g)"
  proof (rule weakI)
    fix sb
    have comp_def:"((f \<otimes> g)\<cdot>sb) = (f\<cdot>(sb \<uplus>\<^sub>\<star> g\<cdot>(sb\<star>)) \<uplus> g\<cdot>(sb\<star>))"
      by (simp add: assms spfcomp_nofeed2)
    have mina:"min (#\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>\<star> g\<cdot>(sb\<star>)))) (#\<^sub>\<surd>(g\<cdot>(sb\<star>))) \<le> #\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>\<star> g\<cdot>(sb\<star>)) \<uplus> g\<cdot>(sb\<star>))"
      by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
    have weak_g: "(#\<^sub>\<surd>((sb\<star>)::'gIn\<^sup>\<Omega>)) \<le> (#\<^sub>\<surd>(g\<cdot>(sb\<star>)))"
      using assms(5) weak_def by blast
    have typecast_g: "#\<^sub>\<surd>sb \<le> (#\<^sub>\<surd>((sb\<star>)::'gIn\<^sup>\<Omega>))"
      apply (rule sbtypecast_tlen)
      using assms by auto
    then have g_leq: "#\<^sub>\<surd>sb \<le> (#\<^sub>\<surd>(g\<cdot>(sb\<star>)))"
      using weak_g by auto
    have weak_f: "(#\<^sub>\<surd>((sb \<uplus>\<^sub>\<star> g\<cdot>(sb\<star>))::'fIn\<^sup>\<Omega>)) \<le> (#\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>\<star> g\<cdot>(sb\<star>))))"
      using assms(4) weak_def by blast
    have typecast_f: "(#\<^sub>\<surd>(sb \<uplus> g\<cdot>(sb\<star>))) \<le> (#\<^sub>\<surd>((sb \<uplus>\<^sub>\<star> g\<cdot>(sb\<star>))::'fIn\<^sup>\<Omega>))"
      apply (rule sbtypecast_tlen)
      using assms by auto
    have "min (#\<^sub>\<surd>sb) (#\<^sub>\<surd>(g\<cdot>(sb\<star>))) \<le> (#\<^sub>\<surd>(sb \<uplus> g\<cdot>(sb\<star>)))" 
      by (metis min.cobounded1  min_def sbunion_tlen_fst_leq_old sbunion_tlen_snd_leq)
    then have "(#\<^sub>\<surd>sb) \<le> (#\<^sub>\<surd>(sb \<uplus> g\<cdot>(sb\<star>)))"
      using typecast_g weak_g by auto
    then have f_leq:"(#\<^sub>\<surd>sb) \<le> (#\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>\<star> g\<cdot>(sb\<star>))))"
      using typecast_f weak_f by auto
    have "min (#\<^sub>\<surd>sb) (#\<^sub>\<surd>sb) \<le> #\<^sub>\<surd>(f\<cdot>(sb \<uplus>\<^sub>\<star> g\<cdot>(sb\<star>)) \<uplus> g\<cdot>(sb\<star>))"
      apply (rule min_trans)
      using mina apply blast
      using f_leq g_leq by auto
    then show "#\<^sub>\<surd>sb \<le> #\<^sub>\<surd>((f \<otimes> g)\<cdot>sb)"
      by (simp add: local.comp_def)
  qed   




lemma spfcomp_rolling_l:
      fixes spfA::"'inA::chan\<^sup>\<Omega> \<rightarrow> 'outA::chan\<^sup>\<Omega>"
      fixes spfB::"'inB::chan\<^sup>\<Omega> \<rightarrow> 'outB::chan\<^sup>\<Omega>"
  shows "((conc outA) oo spfA) \<otimes> spfB = 
   (conc (outA\<star>)) oo ((spfA oo(conc (outA\<star>))) \<otimes> (spfB oo (conc (outA\<star>))))"
proof (rule cfun_eqI)
  fix sbIn
  have "(((conc outA) oo spfA) \<otimes> spfB)\<cdot>sbIn = (fix\<cdot>(conc (outA\<star>) oo 
                                            (\<Lambda> sbOut. spfA\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> spfB\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>2))))"
    apply(simp add: spfComp_def2 oo_def) 
    apply(intro cfun_arg_cong cfun_eqI, simp)
    by (metis (no_types, lifting) botconc1 sbconc_union sbunion_bottom_snd)
  moreover have "(fix\<cdot>(conc (outA\<star>) oo (\<Lambda> sbOut. spfA\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> spfB\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>2))))
        = (conc (outA\<star>))\<cdot>(fix\<cdot>((\<Lambda> sbOut. spfA\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> spfB\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>2)) oo (conc (outA\<star>))))"
    apply(subst fix_rolling) ..
  moreover have "fix\<cdot>((\<Lambda> sbOut. spfA\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> spfB\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>2)) oo (conc (outA\<star>)))
   = ((spfA oo(conc (outA\<star>))) \<otimes> (spfB oo (conc (outA\<star>))))\<cdot>sbIn"
    apply(simp add: spfComp_def2 oo_def) 
    apply(intro cfun_arg_cong cfun_eqI, simp)
    apply(intro uplus_arg_cong2 cfun_arg_cong)
    by(subst unionconc_before, simp add: Int_commute, subst sbtypecast_reduce, simp,
          simp add: sbtypecast_conc sbtypecast_reduce1 sbtypecast_reduce2)+
  ultimately show "(((conc outA) oo spfA) \<otimes> spfB)\<cdot>sbIn 
  =  ((conc (outA\<star>)) oo ((spfA oo(conc (outA\<star>))) \<otimes> (spfB oo (conc (outA\<star>)))))\<cdot>sbIn"
    by fastforce
qed
lemma sbTypeCast_conc:
  "sbTypeCast\<cdot>(a \<Zcat>\<Zcat> b) = a \<Zcat>\<Zcat> (sbTypeCast\<cdot>b)"
  by simp

lemma spfcomp_rolling_r:
  fixes spfA::"'inA::chan\<^sup>\<Omega> \<rightarrow> 'outA::chan\<^sup>\<Omega>"
      fixes spfB::"'inB::chan\<^sup>\<Omega> \<rightarrow> 'outB::chan\<^sup>\<Omega>"
      assumes "chDom TYPE('outA) \<inter> chDom TYPE('outB) = {}"
  shows "spfA \<otimes> ((conc outB) oo spfB) = 
   (conc (outB\<star>)) oo ((spfA oo(conc (outB\<star>))) \<otimes> (spfB oo (conc (outB\<star>))))"
proof (rule cfun_eqI)
  fix x
  show "(spfA \<otimes> ((conc outB) oo spfB))\<cdot>x = 
        ((conc (outB\<star>)) oo ((spfA oo(conc (outB\<star>))) \<otimes> (spfB oo (conc (outB\<star>)))))\<cdot>x"
    apply(subst spfcomp_commut_convert, simp add: assms)
    apply(subst spfcomp_rolling_l)
    apply(subst spfcomp_commut_convert, simp add: assms)
    apply (simp add: spfConvert.rep_eq oo_def)
    apply (rule sb_rep_eqI)
    apply (simp add: sbgetch_insert2)
    by (metis (mono_tags, lifting) assms
        sbconc_getch_split
        sbconc_mgetch_split
        sbgetch_insert2 sbtypecast_getch
        sbunion_bottom_fst
        sbunion_bottom_snd
        sbunion_commu_sbtypecast)
qed

lemma spfcomp_input:
      fixes spfA::"'inA::chan\<^sup>\<Omega> \<rightarrow> 'outA::chan\<^sup>\<Omega>"
      fixes spfB::"'inB::chan\<^sup>\<Omega> \<rightarrow> 'outB::chan\<^sup>\<Omega>"
  shows "(spfA \<otimes> spfB)\<cdot>(sb \<Zcat>\<Zcat> rest) = 
   ((spfA oo(conc (sb\<star>))) \<otimes> (spfB oo (conc (sb\<star>))))\<cdot>rest"
  apply(simp add: spfComp_def2)
  apply(intro cfun_arg_cong cfun_eqI, simp)
  apply(intro uplus_arg_cong2 cfun_arg_cong typecast_arg_cong)
   apply(rule sb_eqI, simp add: conc_getch,
        case_tac "Rep c \<in> chDom TYPE('outA \<union> 'outB)"; 
        simp add: conc_getch; 
        metis conc_sb_def sbconc_getch; fail)+
  done

lemma spfcomp_input_one: "(spfA \<otimes> spfB)\<cdot>(sb) = 
   ((spfA oo(conc (sb\<star>))) \<otimes> (spfB oo (conc (sb\<star>))))\<cdot>\<bottom>"
  apply(subst(2) botconc2[symmetric])
  by(rule spfcomp_input)

lemma comp_one_all: fixes spfA::"'inA::chan\<^sup>\<Omega> \<rightarrow> 'outA::chan\<^sup>\<Omega>"
  fixes spfB::"'inB::chan\<^sup>\<Omega> \<rightarrow> 'outB::chan\<^sup>\<Omega>"
      assumes out_disjunct: "chDom TYPE('outA) \<inter> chDom TYPE('outB) = {}"
  shows  "(((conc (x\<star>)) oo spfA) \<otimes> ((conc (x\<star>)) oo spfB))\<cdot>(((x\<star>)) \<Zcat>\<Zcat> rest) = 
        (x\<star>) \<Zcat>\<Zcat> ((spfA oo (conc (x\<star>))) \<otimes> (spfB oo (conc (x\<star>))))\<cdot>rest"
  apply(subst spfcomp_input)
  unfolding assoc_oo[symmetric]
  apply(subst spfcomp_rolling_r, simp add: out_disjunct)
  unfolding assoc_oo[symmetric]
  apply(subst spfcomp_rolling_l)

  apply(simp add: oo_def assoc[symmetric])
  apply(intro conc_arg_cong2)
  apply(subst conc_typecast_one; (simp add: out_disjunct inf_commute)?)
  apply(intro cfun_fun_cong cfun_arg_cong2;
        rule cfun_eqI, simp, intro cfun_arg_cong conc_arg_cong2; (simp?))

   
   apply(rule sb_eqI, simp add: conc_getch; 
       case_tac "Rep c \<in> chDom TYPE('outA)"; 
        case_tac "Rep c \<in> chDom TYPE('outB)"; 
         simp, (meson disjoint_iff out_disjunct)?)+
  done


lemma spfcomp_unfold_strong_strong_typecast:
  fixes sem1:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem2:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and sem3:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem4:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
  assumes "\<And> sb. output1  \<Zcat>\<^sup>\<surd> sem3\<cdot>sb = sem1\<cdot>((((((sbe2sb a)\<star>)::(('in1 \<union> 'in2) - 'out1 \<union> 'out2)\<^sup>\<Omega>) \<uplus>\<^sub>- ((sbe2sb io1) \<uplus> (sbe2sb io2)))\<star>\<^sub>1) \<Zcat>\<^sup>\<Omega> sb)"
      and "\<And> sb. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>sb = sem2\<cdot>((((((sbe2sb a)\<star>)::(('in1 \<union> 'in2) - 'out1 \<union> 'out2)\<^sup>\<Omega>) \<uplus>\<^sub>- ((sbe2sb io1) \<uplus> (sbe2sb io2)))\<star>\<^sub>2)  \<Zcat>\<^sup>\<Omega> sb)"
  shows "((\<Lambda> x. io1 \<Zcat>\<^sup>\<surd> sem1\<cdot>x)\<otimes>(\<Lambda> x. io2 \<Zcat>\<^sup>\<surd> sem2\<cdot>x))\<cdot>((a \<Zcat>\<^sup>\<surd> sb)\<star>) = 
       (sbeUnion io1 io2) \<Zcat>\<^sup>\<surd> ((\<Lambda> x. output1 \<Zcat>\<^sup>\<surd> sem3\<cdot>x)\<otimes>(\<Lambda> x. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>x))\<cdot>(sb\<star>)"
  apply (simp add: spfComp_def2 sbecons_union)
  apply (rule below_antisym)
  apply (rule fix_least,simp)
  apply (subst(3) fix_eq,simp)
  apply (simp add: sbecons_union sbtypecast_reduce1 sbtypecast_reduce2  sbtypecast_sbconc sbeUnion2sbUnion sbunion_sbconc)
  apply (simp add: sbtypecast_sbconc union_minus_nomagfst union_minus_nomagsnd sbunion_sbconc [symmetric] assms(1)  assms(2); fail)
  apply (subst(2) fix_eq,simp)
  apply (rule monofun_cfun_arg)
  apply (rule fix_least,simp)
  apply (simp add: sbecons_union [symmetric] assms(1) assms(2))
  apply (subst(6) fix_eq,simp)
  apply (subst(5) fix_eq,simp)
  apply (simp add: sbecons_union)
  by (simp add: sbeUnion2sbUnion sbtypecast_sbconc union_minus_nomagfst union_minus_nomagsnd sbunion_sbconc)

lemma spfcomp_unfold_strong_strong:
  fixes sem1:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem2:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and sem3:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem4:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
  assumes "\<And> sb. output1  \<Zcat>\<^sup>\<surd> sem3\<cdot>sb = sem1\<cdot>(((((sbe2sb a)) \<uplus>\<^sub>- ((sbe2sb io1) \<uplus> (sbe2sb io2)))\<star>\<^sub>1) \<Zcat>\<^sup>\<Omega> sb)"
      and "\<And> sb. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>sb = sem2\<cdot>(((((sbe2sb a)) \<uplus>\<^sub>- ((sbe2sb io1) \<uplus> (sbe2sb io2)))\<star>\<^sub>2)  \<Zcat>\<^sup>\<Omega> sb)"
  shows "((\<Lambda> x. io1 \<Zcat>\<^sup>\<surd> sem1\<cdot>x)\<otimes>(\<Lambda> x. io2 \<Zcat>\<^sup>\<surd> sem2\<cdot>x))\<cdot>((a \<Zcat>\<^sup>\<surd> sb)) = 
        (sbeUnion io1 io2) \<Zcat>\<^sup>\<surd> ((\<Lambda> x. output1 \<Zcat>\<^sup>\<surd> sem3\<cdot>x)\<otimes>(\<Lambda> x. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>x))\<cdot>sb"
  apply (insert spfcomp_unfold_strong_strong_typecast [of output1 sem3 sem1 a io1 io2 output2 sem4 sem2 sb])
  using assms by auto

lemma spfcomp_unfold_strong_weak_typecast:
  fixes sem1:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem2:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and sem3:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem4:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
  assumes "\<And> sb. output1  \<Zcat>\<^sup>\<surd> sem3\<cdot>sb = sem1\<cdot>(((((sbe2sb a)\<star>::(('in1 \<union> 'in2) - 'out1 \<union> 'out2)\<^sup>\<Omega>) \<uplus>\<^sub>- ((sbe2sb io1)\<star>))\<star>\<^sub>1) \<Zcat>\<^sup>\<Omega> sb)"
      and "\<And> sb. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>sb = sem2\<cdot>(((((sbe2sb a)\<star>::(('in1 \<union> 'in2) - 'out1 \<union> 'out2)\<^sup>\<Omega>) \<uplus>\<^sub>- ((sbe2sb io1)\<star>))\<star>\<^sub>2) \<Zcat>\<^sup>\<Omega> sb)"
  shows "((\<Lambda> x. io1 \<Zcat>\<^sup>\<surd> sem1\<cdot>x)\<otimes>sem2)\<cdot>((a \<Zcat>\<^sup>\<surd> sb)\<star>) = 
        ((sbe2sb io1)\<star>) \<Zcat>\<^sup>\<Omega> ((\<Lambda> x. output1 \<Zcat>\<^sup>\<surd> sem3\<cdot>x)\<otimes>(\<Lambda> x. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>x))\<cdot>(sb\<star>)"
  apply (simp add: spfComp_def2 sbecons_union)
  apply (rule below_antisym)
  apply (rule fix_least,simp)
  apply (subst(3) fix_eq,simp)
  apply (simp add: sbecons_union sbtypecast_reduce1 sbtypecast_reduce2 sbtypecast_sbconc sbeUnion2sbUnion sbunion_sbconc)
  apply (simp add: sbtypecast_sbconc union_minus_nomagfst union_minus_nomagsnd sbunion_sbconc [symmetric] assms(1)  assms(2) sbunion_sbconc3; fail)
  apply (subst(2) fix_eq,simp)
  apply (simp add: sbunion_sbconc3)
  apply (rule monofun_cfun_arg)
  apply (rule fix_least,simp)
  apply (simp add: sbecons_union [symmetric] assms(1) assms(2))
  apply (subst(6) fix_eq,simp)
  apply (subst(5) fix_eq,simp)
  apply (simp add: union_minus_nomagfst [symmetric] union_minus_nomagsnd [symmetric] sbunion_sbconc3[symmetric])
  by (simp add: sbunion_sbconc [symmetric] sbtypecast_sbconc[symmetric] sbunion_sbconc3)

lemma spfcomp_unfold_strong_weak:
  fixes sem1:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem2:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and sem3:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem4:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
  assumes "\<And> sb. output1  \<Zcat>\<^sup>\<surd> sem3\<cdot>sb = sem1\<cdot>((((sbe2sb a) \<uplus>\<^sub>- ((sbe2sb io1)\<star>))\<star>\<^sub>1) \<Zcat>\<^sup>\<Omega> sb)"
      and "\<And> sb. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>sb = sem2\<cdot>((((sbe2sb a) \<uplus>\<^sub>- ((sbe2sb io1)\<star>))\<star>\<^sub>2) \<Zcat>\<^sup>\<Omega> sb)"
  shows "((\<Lambda> x. io1 \<Zcat>\<^sup>\<surd> sem1\<cdot>x)\<otimes>sem2)\<cdot>(a \<Zcat>\<^sup>\<surd> sb) = 
         ((sbe2sb io1)\<star>) \<Zcat>\<^sup>\<Omega> ((\<Lambda> x. output1 \<Zcat>\<^sup>\<surd> sem3\<cdot>x)\<otimes>(\<Lambda> x. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>x))\<cdot>(sb)"
  apply (insert spfcomp_unfold_strong_weak_typecast [of output1 sem3 sem1 a io1 output2 sem4 sem2 sb])
  using assms by auto

lemma spfcomp_unfold_strong_weak_typecast_rightside:
  fixes sem1:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem2:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and sem4:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and sb:: "'a\<^sup>\<Omega>"
  assumes "\<And> sb. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>sb = sem2\<cdot>(((((sbe2sb a)\<star>::(('in1 \<union> 'in2) - 'out1 \<union> 'out2)\<^sup>\<Omega>) \<uplus>\<^sub>- ((sbe2sb io1)\<star>))\<star>\<^sub>2) \<Zcat>\<^sup>\<Omega> sb)"
    and "chDom TYPE('out1) \<inter> chDom TYPE('in1) = {}"
    and "chDom TYPE('a) \<inter> chDom TYPE('in1) = {}"
  shows "((\<Lambda> x. io1 \<Zcat>\<^sup>\<surd> sem1\<cdot>x)\<otimes>sem2)\<cdot>((a \<Zcat>\<^sup>\<surd> sb)\<star>) = 
        ((sbe2sb io1)\<star>) \<Zcat>\<^sup>\<Omega> (sem1\<otimes>(\<Lambda> x. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>x))\<cdot>(sb\<star>)"
  apply (simp add: spfComp_def2)
  apply (rule below_antisym)
  apply (rule fix_least,simp)
  apply (subst(3) fix_eq,simp)
  apply (simp add: sbecons_union sbtypecast_reduce1 sbtypecast_reduce2 sbtypecast_sbconc sbeUnion2sbUnion sbunion_sbconc)
  apply (simp add: union_minus_nomagsnd sbunion_sbconc [symmetric] assms(1) sbunion_sbconc3 unionm_empty_bottom assms(2) assms(3); fail)
  apply (subst(2) fix_eq,simp)
  apply (simp add: sbunion_sbconc3)
  apply (rule monofun_cfun_arg)
  apply (rule fix_least,simp)
  apply (subst(6) fix_eq,simp)
  apply (subst(5) fix_eq,simp)
  by (simp add: union_minus_nomagfst [symmetric] union_minus_nomagsnd [symmetric] sbtypecast_sbconc 
      sbunion_sbconc unionm_empty_bottom assms)

lemma spfcomp_unfold_weak_strong_typecast_leftside:
  fixes sem1:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem2:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and sem3:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sb:: "'a\<^sup>\<Omega>"
  assumes "\<And> sb. output \<Zcat>\<^sup>\<surd> sem3\<cdot>sb = sem1\<cdot>(((sbe2sb io1)\<star>) \<Zcat>\<^sup>\<Omega> sb)"
    and "chDom TYPE('in2) \<inter> chDom TYPE('out2) = {}"
    and "chDom TYPE('out1) \<inter> chDom TYPE('out2) = {}"
  shows "(sem1\<otimes>(\<Lambda> x. io1 \<Zcat>\<^sup>\<surd> sem2\<cdot>x))\<cdot>(sb\<star>) = 
         ((sbe2sb io1)\<star>) \<Zcat>\<^sup>\<Omega> ((\<Lambda> x. output \<Zcat>\<^sup>\<surd> sem3\<cdot>x)\<otimes>sem2)\<cdot>(sb\<star>)"
  apply (simp add: spfComp_def2)
  apply (rule below_antisym)
  apply (rule fix_least,simp)
  apply (subst(3) fix_eq,simp)
  apply (simp add: sbecons_union sbtypecast_reduce1 sbtypecast_reduce2 sbtypecast_sbconc sbeUnion2sbUnion sbunion_sbconc)
  apply (simp add: union_minus_nomagsnd sbunion_sbconc [symmetric] assms(1))
  apply (subst sbunion_sbconc4,auto) 
  apply (subst sbunion_sbconc4,simp add: assms) 
  apply (subst sbunion_sbconc4,auto)
  apply (simp add: sbtypecast_sbconc sbtypecast_reduce sbtypecast_reduce2 assms)
  apply (subst sbtypecast_reduce,auto)
  apply (subst sbtypecast_reduce,auto)
  apply (simp add: sbtypecast_empty2 assms)
  apply (subst(2) fix_eq,simp)
  apply (simp add: sbunion_sbconc4 assms)
  apply (rule monofun_cfun_arg)
  apply (rule fix_least,simp)
  apply (subst(6) fix_eq,simp)
  apply (subst(5) fix_eq,simp)
  apply (simp add: union_minus_nomagfst [symmetric] union_minus_nomagsnd [symmetric])
  apply (subst(2) sbunion_sbconc4) apply auto[1]
  apply (simp add: sbtypecast_sbconc sbunion_sbconc sbtypecast_reduce)
  apply (subst sbtypecast_reduce,auto)
  apply (simp add: sbtypecast_empty2 assms)
  apply (subst sbunion_sbconc4) apply auto [1]
  apply (simp add: sbtypecast_sbconc sbunion_sbconc sbtypecast_reduce)
  apply (subst sbtypecast_reduce) 
  by auto

lemma spfcomp_unfold_strong_weak_typecast_noselfloops:
  fixes sem1:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem2:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and sem3:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem4:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
    and sb:: "'a\<^sup>\<Omega>"
  assumes "\<And> sb. output2 \<Zcat>\<^sup>\<surd> sem4\<cdot>sb = sem2\<cdot>(((((sbe2sb a)\<star>::(('in1 \<union> 'in2) - 'out1 \<union> 'out2)\<^sup>\<Omega>) \<uplus>\<^sub>- ((sbe2sb io1)\<star>))\<star>\<^sub>2) \<Zcat>\<^sup>\<Omega> sb)"
    and "\<And> sb. output1 \<Zcat>\<^sup>\<surd> sem3\<cdot>sb = sem1\<cdot>((sbe2sb output2)\<star> \<Zcat>\<^sup>\<Omega> sb)"
    and "chDom TYPE('out1) \<inter> chDom TYPE('in1) = {}"
    and "chDom TYPE('in2) \<inter> chDom TYPE('out2) = {}"
    and "chDom TYPE('a) \<inter> chDom TYPE('in1) = {}"
    and "chDom TYPE('out1) \<inter> chDom TYPE('out2) = {}"
  shows "((\<Lambda> x. io1 \<Zcat>\<^sup>\<surd> sem1\<cdot>x)\<otimes>sem2)\<cdot>((a \<Zcat>\<^sup>\<surd> sb)\<star>) = 
        ((sbe2sb io1)\<star>) \<Zcat>\<^sup>\<Omega> ((sbe2sb output2)\<star>) \<Zcat>\<^sup>\<Omega> ((\<Lambda> x. output1 \<Zcat>\<^sup>\<surd> sem3\<cdot>x)\<otimes>sem4)\<cdot>(sb\<star>)"
  apply (subst spfcomp_unfold_strong_weak_typecast_rightside [of output2 sem4])
  apply (simp_all add: assms)
  apply (rule cfun_arg_cong)
  apply (simp add: assms(1)[symmetric])
  apply (subst spfcomp_unfold_weak_strong_typecast_leftside [of output1 sem3])
  by (simp_all add: assms)

lemma spfcomp_unfold_strong_weak_bottom:
  fixes sem1:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem2:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
  assumes "sem2\<cdot>((sbe2sb io1)\<star>) = \<bottom>"
      and "sem1\<cdot>\<bottom> = \<bottom>"
      and "sem2\<cdot>\<bottom> = \<bottom>"
      and "chDom TYPE('out1) \<inter> chDom TYPE('in1) = {}"
  shows "((\<Lambda> x. io1 \<Zcat>\<^sup>\<surd> sem1\<cdot>x) \<otimes> sem2)\<cdot>\<bottom> = ((sbe2sb io1)\<star>)" 
  apply (simp add: spfComp_def2)
  apply (rule below_antisym)
  apply (rule fix_least,simp)
  apply (simp add: sbtypecast_reduce1 sbtypecast_reduce2 sbunion_sbconc3)
  apply (simp add: assms ubunion_fst2)
  apply (case_tac "chDom TYPE('out1) \<inter> chDom TYPE('in2) = {}")
  apply (simp add: assms ubunion_fst2 sbunion_bottom_snd)
  apply (subst(2) sbunion_bottom_fst)
  apply auto[1] 
  apply (simp add: sbtypecast_reduce)
  apply (subst sbtypecast_reduce)
  apply auto[1]
  apply (simp add: assms(1) sbunion_bottom_snd)
  apply (subst fix_eq,simp)
  apply (simp add: sbunion_sbconc3)
  apply (subst  sbconc_bot_r [symmetric])
  apply (rule monofun_cfun_arg)
  by simp
  
lemma spfcomp_unfold_weak_weak_bottom:
  fixes sem1:: "'in1\<^sup>\<Omega> \<rightarrow> 'out1\<^sup>\<Omega>"
    and sem2:: "'in2\<^sup>\<Omega> \<rightarrow> 'out2\<^sup>\<Omega>"
  assumes "sem1\<cdot>\<bottom> = \<bottom>"
      and "sem2\<cdot>\<bottom> = \<bottom>"
  shows "(sem1\<otimes>sem2)\<cdot>\<bottom> = \<bottom>"
  apply (simp add: spfComp_def2)
  apply (rule below_antisym)
  apply (rule fix_least,simp)
  apply (simp add: sbtypecast_reduce sbunion_bottom_snd assms)
  by simp

definition spfComp_strong::
"('I1::tchan\<^sup>\<Omega> \<rightarrow>\<^sub>s 'O1::tchan\<^sup>\<Omega>) \<rightarrow> ('I2::tchan\<^sup>\<Omega> \<rightarrow>\<^sub>s 'O2::tchan\<^sup>\<Omega>)
 \<rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow>\<^sub>s ('O1 \<union> 'O2)\<^sup>\<Omega>)" where 
"spfComp_strong \<equiv> \<Lambda> tspf1 tspf2. Abs_tspfs_fun(spfComp\<cdot>(Rep_tspfs_fun\<cdot>tspf1)\<cdot>(Rep_tspfs_fun\<cdot>tspf2))"

abbreviation spfComp_strong_abbr::
"('I1::tchan\<^sup>\<Omega> \<rightarrow>\<^sub>s 'O1::tchan\<^sup>\<Omega>) \<Rightarrow> ('I2::tchan\<^sup>\<Omega> \<rightarrow>\<^sub>s 'O2::tchan\<^sup>\<Omega>)
 \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow>\<^sub>s ('O1 \<union> 'O2)\<^sup>\<Omega>)" 
(infixr "\<otimes>\<^sub>s" 70) where "tspf1 \<otimes>\<^sub>s tspf2 \<equiv> spfComp_strong\<cdot>tspf1\<cdot>tspf2"

lemma spfcomps2comp:
      "(Rep_tspfs_fun\<cdot>(tspf1 \<otimes>\<^sub>s tspf2)) 
     = (Rep_tspfs_fun\<cdot>tspf1) \<otimes> (Rep_tspfs_fun\<cdot>tspf2)"
  apply(simp add: spfComp_strong_def)
  apply(subst beta_cfun, intro cont2cont, (simp add: spfcomp_causal)?)+
  by(rule rep_abs_tspfs, simp add: spfcomp_causal)

lemma wrapped_spf_comp_eq:
  fixes i1::"'wIn1\<^sup>\<Omega> \<rightarrow> 'In1\<^sup>\<Omega>"
    and i2::"'wIn2\<^sup>\<Omega> \<rightarrow> 'In2\<^sup>\<Omega>"
    and i3::"(('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega> \<rightarrow> (('In1 \<union> 'In2) - 'Out1 \<union> 'Out2)\<^sup>\<Omega>"
    and o1::"'Out1\<^sup>\<Omega> \<rightarrow> 'wOut1\<^sup>\<Omega>"
    and o2::"'Out2\<^sup>\<Omega> \<rightarrow> 'wOut2\<^sup>\<Omega>"
    and o3::"('Out1 \<union> 'Out2)\<^sup>\<Omega> \<rightarrow> ('wOut1 \<union> 'wOut2)\<^sup>\<Omega>"
assumes "o3\<cdot>\<bottom> = \<bottom>"
    and "\<And>c out1 out2. Rep c \<in> chDom TYPE('wOut1) \<longrightarrow> o3\<cdot>(out1 \<uplus> out2) \<^enum> c = o1\<cdot>out1 \<^enum>\<^sub>\<star> c"
    and "\<And>c out1 out2. Rep c \<notin> chDom TYPE('wOut1) \<longrightarrow> o3\<cdot>(out1 \<uplus> out2) \<^enum> c = o2\<cdot>out2 \<^enum>\<^sub>\<star> c"
    and "\<And>c y (x:: (('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega>). \<not>chDomEmpty TYPE('In1) \<and> \<not>chDomEmpty TYPE('Out1) \<longrightarrow> Rep c \<in> chDom TYPE('Out1 \<union> 'Out2) \<longrightarrow> i1\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>1)  \<^enum>  c = y  \<^enum>\<^sub>\<star>  c"
    and "\<And>c y (x:: (('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega>). \<not>chDomEmpty TYPE('In2) \<and> \<not>chDomEmpty TYPE('Out2) \<longrightarrow> Rep c \<in> chDom TYPE('Out1 \<union> 'Out2) \<longrightarrow> i2\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>2)  \<^enum>  c = y  \<^enum>\<^sub>\<star>  c"
    and "\<And>c y (x:: (('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega>). \<not>chDomEmpty TYPE('In1) \<and> \<not>chDomEmpty TYPE('Out1) \<longrightarrow> Rep c \<notin> chDom TYPE('Out1 \<union> 'Out2) \<longrightarrow> i1\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>1)  \<^enum>  c = i3\<cdot>x  \<^enum>\<^sub>\<star>  c"
    and "\<And>c y (x:: (('wIn1 \<union> 'wIn2) - 'wOut1 \<union> 'wOut2)\<^sup>\<Omega>). \<not>chDomEmpty TYPE('In2) \<and> \<not>chDomEmpty TYPE('Out2) \<longrightarrow> Rep c \<notin> chDom TYPE('Out1 \<union> 'Out2) \<longrightarrow> i2\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>2)  \<^enum>  c = i3\<cdot>x  \<^enum>\<^sub>\<star>  c"
  shows "(o1 oo f oo i1) \<otimes> (o2 oo g oo i2) = o3 oo (f \<otimes> g) oo i3"
  apply(rule cfun_eqI)
  apply(simp add: spfComp_def2)
  apply(rule parallel_fix_ind)
  apply(simp)
  apply(simp add: assms(1))
  apply(rule sb_eqI, simp)
  apply(case_tac "Rep c \<in> chDom TYPE('wOut1)")
  apply(subst assms(2), simp, simp)
  apply(case_tac "chDomEmpty TYPE('In1)")
  apply(subst sbtypeepmpty_sbbot[where sb="(i1\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>1))"], simp)
  apply(subst sbtypeepmpty_sbbot[where sb="(i3\<cdot>x \<uplus>\<^sub>- y\<star>\<^sub>1)"], simp)
  apply simp
  apply(case_tac "chDomEmpty TYPE('Out1)")
  apply(subst sbtypeepmpty_sbbot[where sb="(f\<cdot>(i1\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>1)))"], simp)
  apply(subst sbtypeepmpty_sbbot[where sb="(f\<cdot>(i3\<cdot>x \<uplus>\<^sub>- y\<star>\<^sub>1))"], simp)
  apply simp
  apply(subgoal_tac "(i1\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>1)) = (i3\<cdot>x \<uplus>\<^sub>- y\<star>\<^sub>1)", simp)
  apply(rule sb_eqI)
  apply(case_tac "Rep ca \<in> chDom TYPE('Out1 \<union> 'Out2)")
  apply simp
  apply(simp add: assms(4))
  apply simp
  apply(simp add: assms(6))
  apply(subst assms(3), simp, simp)
  apply(case_tac "chDomEmpty TYPE('In2)")
  apply(subst sbtypeepmpty_sbbot[where sb="(i2\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>2))"], simp)
  apply(subst sbtypeepmpty_sbbot[where sb="(i3\<cdot>x \<uplus>\<^sub>- y\<star>\<^sub>2)"], simp)
  apply simp
  apply(case_tac "chDomEmpty TYPE('Out2)")
  apply(subst sbtypeepmpty_sbbot[where sb="(g\<cdot>(i2\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>2)))"], simp)
  apply(subst sbtypeepmpty_sbbot[where sb="(g\<cdot>(i3\<cdot>x \<uplus>\<^sub>- y\<star>\<^sub>2))"], simp)
  apply simp
  apply(subgoal_tac "(i2\<cdot>(x \<uplus>\<^sub>- o3\<cdot>y\<star>\<^sub>2)) = (i3\<cdot>x \<uplus>\<^sub>- y\<star>\<^sub>2)", simp)
  apply(rule sb_eqI)
  apply(case_tac "Rep ca \<in> chDom TYPE('Out1 \<union> 'Out2)")
  apply simp
  apply(simp add: assms(5))
  apply simp
  by(simp add: assms(7))

lemma spfcomp_sbrenamech_single_feedback:
  fixes f::"'fOut \<Rightarrow> 'fIn"
    and g::"'gOut \<Rightarrow> 'gIn"
    and h::"'hOut \<Rightarrow> 'hIn"
assumes "chDom TYPE('hIn) \<subseteq> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)"
    and "chDom TYPE('hOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
    and "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (g c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (h c)) \<subseteq> ctype (Rep c)"
    and "\<And>c::'hOut.  Rep c \<in> chDom TYPE('hOut) \<Longrightarrow> Rep (h c) \<in> chDom TYPE('hIn)"
    and "\<And>c::'hOut.  Rep c \<in> chDom TYPE('hOut) \<Longrightarrow> Rep c \<in> chDom TYPE('fOut) \<Longrightarrow> Rep (f (Abs (Rep c))) \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep (f (Abs (Rep c))) = Rep (h c)"
    and "\<And>c::'hOut.  Rep c \<in> chDom TYPE('hOut) \<Longrightarrow> Rep c \<in> chDom TYPE('fOut) \<Longrightarrow> Rep (f (Abs (Rep c))) \<notin> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep (f (Abs (Rep c))) \<in> chDom TYPE('fIn \<union> 'gIn)"
    and "\<And>c::'hOut.  Rep c \<in> chDom TYPE('hOut) \<Longrightarrow> Rep c \<in> chDom TYPE('fOut) \<Longrightarrow> Rep (f (Abs (Rep c))) \<notin> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep (f (Abs (Rep c))) \<notin> chDom TYPE('fOut)"
    and "\<And>c::'hOut.  Rep c \<in> chDom TYPE('hOut) \<Longrightarrow> Rep c \<in> chDom TYPE('fOut) \<Longrightarrow> Rep (f (Abs (Rep c))) \<notin> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep (g (Abs (Rep (f (Abs (Rep c)))))) = Rep (h c)"
    and "\<And>c::'hOut.  Rep c \<in> chDom TYPE('hOut) \<Longrightarrow> Rep c \<notin> chDom TYPE('fOut) \<Longrightarrow> Rep (g (Abs (Rep c))) \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep (g (Abs (Rep c))) = Rep (h c)"
    and "\<And>c::'hOut.  Rep c \<in> chDom TYPE('hOut) \<Longrightarrow> Rep c \<notin> chDom TYPE('fOut) \<Longrightarrow> Rep (g (Abs (Rep c))) \<notin> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep (g (Abs (Rep c))) \<in> chDom TYPE('fIn \<union> 'gIn)"
    and "\<And>c::'hOut.  Rep c \<in> chDom TYPE('hOut) \<Longrightarrow> Rep c \<notin> chDom TYPE('fOut) \<Longrightarrow> Rep (g (Abs (Rep c))) \<notin> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep (g (Abs (Rep c))) \<in> chDom TYPE('fOut)"
    and "\<And>c::'hOut.  Rep c \<in> chDom TYPE('hOut) \<Longrightarrow> Rep c \<notin> chDom TYPE('fOut) \<Longrightarrow> Rep (g (Abs (Rep c))) \<notin> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep (f (Abs (Rep (g (Abs (Rep c)))))) = Rep (h c)"
  shows "spfConvert\<cdot>(sbRenameCh f \<otimes> sbRenameCh g) = sbRenameCh h"
  apply(rule cfun_eqI)
  apply(rule sb_eqI)
  apply(subst sbrenamech_getch[OF assms(5)])
  apply(simp add: spfConvert_def)
  apply(subst spfcomp_unfold)
  apply(case_tac "Rep c \<in> chDom TYPE('fOut)"; simp)
  apply(subst sbrenamech_getch2[OF _ assms(3)], simp)
  apply simp
  apply(case_tac "Rep (f (Abs (Rep c))) \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)")
  apply simp
  using assms(7) apply(simp add: sbgetch_insert)
  apply(subst sbunion_minus_getchr)
  using assms(8) apply fastforce
  apply blast
  apply(subst spfcomp_unfold)
  apply(subst sbunion_getchr)
  using assms(9) apply blast
  apply(subst sbrenamech_getch2[OF _ assms(4)])
  using assms(8) assms(9) apply force
  apply(simp, subst sbunion_minus_getchl)
  apply(subst assms(10)) apply auto[3]
  using assms(1) assms(6) apply fastforce
  apply(subst sbtypecast_getch3)
  using assms(1) apply fastforce
  using assms(10) apply(simp add: sbgetch_insert)
  apply(subst sbrenamech_getch2[OF _ assms(4)])
  using assms(2) apply fastforce
  apply simp
  apply(case_tac "Rep (g (Abs (Rep c))) \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)")
  apply simp
  using assms(11) apply(simp add: sbgetch_insert)
  apply(subst sbunion_minus_getchr)
  using assms(12) apply fastforce
  apply blast
  apply(subst spfcomp_unfold)
  apply(subst sbunion_getchl)
  using assms(13) apply fastforce
  apply(subst sbrenamech_getch2[OF _ assms(3)])
  using assms(13) assms(12) apply force
  apply(simp, subst sbunion_minus_getchl)
  apply(subst assms(14)) apply auto[3]
  using assms(1) assms(6) apply fastforce
  apply(subst sbtypecast_getch3)
  using assms(1) apply fastforce
  using assms(14) by(simp add: sbgetch_insert)

lemma spfcomp_add_remove_left: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE('fOut) \<inter> chDom TYPE('Out) = {}"
      and "chDom TYPE('fOut) \<inter> chDom TYPE('gIn) = {}"
      and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    shows "spfConvert\<cdot>(f \<otimes> g) = (spfConvert\<cdot>(g)::'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)"
  apply(rule cfun_eqI)
  apply(simp add: spfConvert_def)
  apply(subst spfcomp_unfold)
  apply(rule sb_eqI, simp)
  apply(subst sbunion_getchr)
  using assms(1) apply blast
  apply(rule spf_arg_cong, simp)
  apply(subst sbunion_getchl)
  using assms(2) assms(3) apply(simp, blast)
  using assms(2) assms(3) by(simp add: sbgetch_insert, blast)

lemma spfcomp_add_remove_right: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "chDom TYPE('gOut) \<inter> chDom TYPE('Out) \<subseteq> chDom TYPE('fOut)"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
  shows "spfConvert\<cdot>(f \<otimes> g) = (spfConvert\<cdot>(f)::'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)"
  apply(rule cfun_eqI)                 
  apply(simp add: spfConvert_def)
  apply(subst spfcomp_unfold)
  apply(rule sb_eqI, simp)
  apply(case_tac "Rep c \<in> chDom TYPE('gOut)"; simp?)
  apply(subst sbunion_getchl)
  using assms(1) apply blast
  apply(rule spf_arg_cong, simp)
  apply(subst sbunion_getchl)
  using assms(2,3) apply(simp, blast) 
  using assms(2,3) apply(simp add: sbgetch_insert, blast)
  apply(case_tac "Rep c \<in> chDom TYPE('fOut)"; simp?)
  apply(rule spf_arg_cong, simp)
  apply(subst sbunion_getchl)
  using assms(2,3) apply(simp, blast)
  using assms(2,3) by(simp add: sbgetch_insert, blast)

lemma spfcomp_convert_left:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "chDom TYPE('fOut2) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut)"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut2)"
    and "\<not>chDomEmpty TYPE('gOut) \<longrightarrow> chDom TYPE('fOut) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut \<union> 'gOut) \<inter> chDom TYPE('fOut2 \<union> 'gOut) \<subseteq> chDom TYPE('fIn2)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fOut) \<subseteq> chDom TYPE('fOut2 \<union> 'gOut)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut \<union> 'gOut \<union> 'fIn2 \<union> 'fOut2)"
    and "\<not>chDomEmpty TYPE('fOut \<union> 'fOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('fIn2) \<inter> chDom TYPE('fOut2) \<subseteq> chDom TYPE('fOut \<union> 'gOut)"
  shows "(spfConvert\<cdot>(f)::'fIn2\<^sup>\<Omega> \<rightarrow> 'fOut2\<^sup>\<Omega>) \<otimes> g = spfConvert\<cdot>(f \<otimes> g)"
  apply(rule cfun_eqI)
  apply(simp add: spfComp_def2 spfConvert_def)
  apply(rule parallel_fix_ind)
  apply(auto)[3]
  apply(rule sb_eqI)
  apply(rename_tac in2 out1 c)
  apply(case_tac "Rep c \<in> chDom TYPE('fOut2)"; case_tac "Rep c \<in> chDom TYPE('fOut)"; simp)
  apply(rule spf_arg_cong, simp)
  apply(subst union_minus_nomagfst[symmetric])
  apply(case_tac "Rep ca \<in> chDom TYPE('fOut \<union> 'gOut)"; simp)
  apply(subst sbunion_star_getchr_general; simp)
  using assms(5) apply fastforce
  using assms(4) apply fastforce
  using assms(5) apply fastforce
  apply(subst sbunion_star_getchl_general; simp)
  using assms(6) apply fastforce
  using assms(7) apply fastforce
  using assms(1) apply(auto simp add: sbgetch_insert)[1]
  using assms(2) apply fastforce
  apply(rule spf_arg_cong, simp)
  apply(case_tac "Rep ca \<in> chDom TYPE('fOut2 \<union> 'gOut)"; case_tac "Rep ca \<in> chDom TYPE('fOut \<union> 'gOut)"; simp)
  using assms(3) by fastforce

lemma spfcomp_convert_right: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "\<not>chDomEmpty TYPE('fOut) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)" 
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('fOut \<union> 'gOut2) \<inter> chDom TYPE('fOut \<union> 'gOut) \<subseteq> chDom TYPE('gIn2)" 
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gOut) \<subseteq> chDom TYPE('fOut \<union> 'gOut2)" 
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('fIn) \<inter> chDom TYPE('gIn) \<subseteq> chDom TYPE('fOut \<union> 'gOut \<union> 'gIn2 \<union> 'gOut2) " 
    and "\<not>chDomEmpty TYPE('gOut2) \<longrightarrow> chDom TYPE('gIn) \<inter> chDom TYPE('gIn2) \<inter> chDom TYPE('gOut2) \<subseteq> chDom TYPE('fOut \<union> 'gOut)" 
  shows "f \<otimes> (spfConvert\<cdot>(g)::'gIn2\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) = spfConvert\<cdot>(f \<otimes> g)"
  apply(rule cfun_eqI)
  apply(simp add: spfComp_def2 spfConvert_def)
  apply(rule parallel_fix_ind)
  apply(auto)[3]
  apply(rule sb_eqI)
  apply(rename_tac in2 out1 c)
  apply(case_tac "Rep c \<in> chDom TYPE('fOut)"; simp; rule spf_arg_cong; simp)
  apply(case_tac "Rep ca \<in> chDom TYPE('fOut \<union> 'gOut)"; case_tac "Rep ca \<in> chDom TYPE('fOut \<union> 'gOut2)"; simp)
  using assms(1) apply fastforce
  apply(subst union_minus_nomagsnd[symmetric])
  apply(case_tac "Rep ca \<in> chDom TYPE('fOut \<union> 'gOut)"; simp)
  apply(case_tac "Rep ca \<in> chDom TYPE('fOut \<union> 'gOut2)")
  apply(subst sbunion_star_getchr_general; simp)
  using assms(2) apply auto[1]
   apply(subst sbunion_star_getchr_general; simp)
  using assms(3) apply fastforce
  using assms(3) apply fastforce
  apply(rule sbunion_star_getchl_general; simp)
  using assms(4) apply fastforce
  using assms(5) by fastforce

lemma spfcomp_convert_left_equal_in:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "chDom TYPE('gOut2) \<subseteq> chDom TYPE('gOut)"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn \<union> 'fOut \<union> 'Out) \<subseteq> chDom TYPE('gOut2)"
    and "chDom TYPE('gIn) \<inter> chDom TYPE('gOut) = {}"
  shows "spfConvert\<cdot>((spfConvert\<cdot>(g)::'gIn\<^sup>\<Omega> \<rightarrow> 'gOut2\<^sup>\<Omega>) \<otimes> f) = (spfConvert\<cdot>(g \<otimes> f)::'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)"
  apply(subst spfcomp_convert_left)
  using assms(1) apply fastforce
  using assms(2) apply fastforce
  using assms(2) apply fastforce
  apply fastforce
  using assms(3) apply fastforce
  apply fastforce
  using assms(1) apply fastforce
  apply(rule spfconvert_merge)
  using assms(1) apply fastforce
  using assms(2) by fastforce

lemma spfcomp_convert_left_equal_out:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "chDom TYPE('gIn) \<subseteq> chDom TYPE('gIn2)"
  shows "spfConvert\<cdot>((spfConvert\<cdot>(g)::'gIn2\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>) \<otimes> f) = (spfConvert\<cdot>(g \<otimes> f)::'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)"
  apply(subst spfcomp_convert_left)
  apply fastforce+
  using assms(1) apply fastforce+
  apply(rule spfconvert_merge)
  using assms(1) apply fastforce
  by fastforce

lemma spf_connector_replace:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and m1::"'Out1 \<Rightarrow> 'In1"
    and m2::"'Out2 \<Rightarrow> 'In2"
assumes "\<And>c. ctype (Rep (m1 c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (m2 c)) \<subseteq> ctype (Rep c)"
    and "\<And>c::'Out2. Rep c \<in> chDom TYPE('Out1) \<longrightarrow> Rep c \<in> chDom TYPE('Out2) \<longrightarrow> Rep (m1 (Abs (Rep c))) = Rep (m2 c)"
    and "chDom TYPE('In2) \<subseteq> chDom TYPE('In1)"
    and "chDom TYPE('Out2) \<subseteq> chDom TYPE('Out1)"
    and "chDom TYPE('Out1) \<inter> chDom TYPE('fIn \<union> 'fOut \<union> 'Out) \<subseteq> chDom TYPE('Out2)"
    and "chDom TYPE('In1) \<inter> chDom TYPE('Out1) = {}"
  shows "(spfConvert\<cdot>(sbRenameCh m1 \<otimes> f)::'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) = spfConvert\<cdot>(sbRenameCh m2 \<otimes> f)"
  apply(subst spfcomp_convert_left_equal_in[symmetric, OF assms(5-7)])
  apply(subst spfcomp_convert_left_equal_out[symmetric, OF assms(4)])
  apply(subst sbrenamech_convert_eq[where g="m2", OF assms(1,2)])
  using assms(3) apply simp
  using assms(5) apply fastforce
  by simp

lemma spfcomp_sbrenamech_eq:
  fixes m1::"'mOut \<Rightarrow> 'mIn"
    and m2::"'mOut \<Rightarrow> 'mIn"
    and k::"'kOut \<Rightarrow> 'kIn"
assumes "\<And>c. ctype (Rep (m1 c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (m2 c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (k c)) \<subseteq> ctype (Rep c)"
    and "chDom TYPE('kIn) \<subseteq>  chDom TYPE('mOut)"
    and "chDom TYPE('mIn) \<inter> chDom TYPE('mOut) = {}"
    and "\<And>c::'mOut. Rep c \<in> chDom TYPE('mOut) \<longrightarrow> Rep (m1 c) \<in> chDom TYPE('mIn)"
    and "\<And>c::'mOut. Rep c \<in> chDom TYPE('mOut) \<longrightarrow> Rep (m2 c) \<in> chDom TYPE('mIn)"
    and "\<And>c::'kOut. Rep c \<in> chDom TYPE('kOut) \<longrightarrow> Rep (k c) \<in> chDom TYPE('kIn)"
    and "\<And>c::'kIn. Rep c \<in> chDom TYPE('kIn) \<longrightarrow> Rep (m1 (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut)"
    and "\<And>c::'kIn. Rep c \<in> chDom TYPE('kIn) \<longrightarrow> Rep (m2 (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut)"
    and "\<And>c::'mOut. Rep c \<in> chDom TYPE('mOut) \<longrightarrow> Rep (m1 c) \<in> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut) \<longrightarrow> Rep (m2 c) \<in> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut) \<longrightarrow> Rep (m1 c) = Rep (m2 c)"
    and "\<And>c::'mOut. Rep c \<in> chDom TYPE('mOut) \<longrightarrow> Rep (m1 c) \<in> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut) \<longrightarrow> Rep (m2 c) \<notin> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut) \<longrightarrow> Rep (m1 c) = Rep (m2 (Abs (Rep (k (Abs (Rep (m2 c)))))))"
    and "\<And>c::'mOut. Rep c \<in> chDom TYPE('mOut) \<longrightarrow> Rep (m1 c) \<notin> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut) \<longrightarrow> Rep (m2 c) \<in> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut) \<longrightarrow> Rep (m2 c) = Rep (m1 (Abs (Rep (k (Abs (Rep (m1 c)))))))"
    and "\<And>c::'mOut. Rep c \<in> chDom TYPE('mOut) \<longrightarrow> Rep (m1 c) \<notin> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut) \<longrightarrow> Rep (m2 c) \<notin> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut) \<longrightarrow> Rep (m2 (Abs (Rep (k (Abs (Rep (m2 c))))))) = Rep (m1 (Abs (Rep (k (Abs (Rep (m1 c)))))))"
  shows "sbRenameCh m1 \<otimes> sbRenameCh k = sbRenameCh m2 \<otimes> sbRenameCh k"
  apply(rule cfun_eqI)
  apply(rule sb_eqI)
  apply(simp add: spfConvert_def)
  apply(case_tac "Rep c \<in> chDom TYPE('mOut)"; simp)
  apply(case_tac "Rep (m1 (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut)"; 
        case_tac "Rep (m2 (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'kIn) - 'mOut \<union> 'kOut)")
  apply(subst spfcomp_sbrename_getch_l[OF assms(1)], simp, simp)
  apply(subst spfcomp_sbrename_getch_l[OF assms(2)], simp, simp)
  using assms(11) sbgetch_insert rep_reduction apply metis
  apply(subst spfcomp_sbrename_getch_l[OF assms(1)], simp, simp)
  apply(subst spfcomp_sbrename_getch_lrl[OF assms(2)], simp, simp)
  using assms(6) apply (metis Un_iff chdom_in chdom_union empty_iff)
  using assms(5) using cdom_notempty cempty_rule chdomnotempty_rangeeq apply blast
  using assms(4) apply auto[1]
  using assms(10) apply auto[1]
  apply(subst sbrenamech_getch2[OF _ assms(3)])
  apply simp using assms(5,7) cnotempty_cdom apply blast
  apply(simp del: chdom_minus)
  apply(subst sbrenamech_getch2[OF _ assms(2)])
  apply(subgoal_tac "Rep (k (Abs (Rep (m2 (Abs (Rep c)))))) \<in> chDom TYPE('kIn)")
  using assms(4) apply auto[1]
  using assms(5,7,8) apply (simp add: disjoint_iff)
  apply(simp del: chdom_minus)
  using assms(12) sbgetch_insert rep_reduction apply metis
  apply(subst spfcomp_sbrename_getch_l[OF assms(2)], simp, simp)
  apply(subst spfcomp_sbrename_getch_lrl[OF assms(1)], simp, simp)
  using assms(7) apply (metis Un_iff chdom_in chdom_union empty_iff)
  using assms(5) using cdom_notempty cempty_rule chdomnotempty_rangeeq apply blast
  using assms(4) apply auto[1]
  using assms(9) apply auto[1]
  apply(subst sbrenamech_getch2[OF _ assms(3)])
  apply simp using assms(5,6) cnotempty_cdom apply blast
  apply(simp del: chdom_minus)
  apply(subst sbrenamech_getch2[OF _ assms(1)])
  apply(subgoal_tac "Rep (k (Abs (Rep (m1 (Abs (Rep c)))))) \<in> chDom TYPE('kIn)")
  using assms(4) apply auto[1]
  using assms(5,6,8) apply (simp add: disjoint_iff)
  apply(simp del: chdom_minus)
  using assms(13) sbgetch_insert rep_reduction apply metis
  apply(subst spfcomp_sbrename_getch_lrl[OF assms(1)], simp, simp)
  using assms(6) apply (metis Un_iff chdom_in chdom_union empty_iff)
  using assms(5) using cdom_notempty cempty_rule chdomnotempty_rangeeq apply blast
  using assms(4) apply auto[1]
  using assms(9) apply auto[1]
  apply(subst spfcomp_sbrename_getch_lrl[OF assms(2)], simp, simp)
  using assms(6) apply (metis Un_iff chdom_in chdom_union empty_iff)
  using assms(5) using cdom_notempty cempty_rule chdomnotempty_rangeeq apply blast
  using assms(4) apply auto[1]
  using assms(10) apply auto[1]
  apply(subst sbrenamech_getch2[OF _ assms(3)])
  apply simp using assms(5,6) cnotempty_cdom apply blast
  apply(subst sbrenamech_getch2[OF _ assms(3)])
  apply simp using assms(5,7) cnotempty_cdom apply blast
  apply(simp del: chdom_minus)
  apply(subst sbrenamech_getch2[OF _ assms(1)])
  apply(subgoal_tac "Rep (k (Abs (Rep (m1 (Abs (Rep c)))))) \<in> chDom TYPE('kIn)")
  using assms(4) apply auto[1]
  using assms(5,6,8) apply (simp add: disjoint_iff)
  apply(subst sbrenamech_getch2[OF _ assms(2)])
  apply(subgoal_tac "Rep (k (Abs (Rep (m2 (Abs (Rep c)))))) \<in> chDom TYPE('kIn)")
  using assms(4) apply auto[1]
  using assms(5,7,8) apply (simp add: disjoint_iff)
  apply(simp del: chdom_minus)
  using assms(14) sbgetch_insert rep_reduction apply metis
  apply(subst spfcomp_sbrename_getch_rl[OF assms(1)], simp)
  using assms(4) apply auto[1]
  using assms(9) apply auto[1]
  apply(subst spfcomp_sbrename_getch_rl[OF assms(2)], simp)
  using assms(4) apply auto[1]
  using assms(10) apply auto[1]
  apply(subst sbrenamech_getch2[OF _ assms(3)], simp)+
  apply(simp)
  apply(subst sbrenamech_getch2[OF _ assms(1)])
  using assms(4,8) apply auto[1]
  apply(subst sbrenamech_getch2[OF _ assms(2)])
  using assms(4,8) apply auto[1]
  apply(subgoal_tac "Rep (m1 (Abs (Rep (k (Abs (Rep c)))))) = Rep(m2 (Abs (Rep (k (Abs (Rep c))))))")
  apply(simp add: sbgetch_insert)
  apply(subst assms(11))
  apply (metis assms(4) assms(8) rep_reduction subsetD)
  apply (metis assms(8) assms(9) rep_reduction)
  apply (metis assms(8) assms(10) rep_reduction)
  by simp

lemma spfcomp_connect_component:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and m1::"'mOut \<Rightarrow> 'mIn"
    and m2::"'fIn \<Rightarrow> 'fIn2"
assumes "\<And>c. ctype (Rep (m1 c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (m2 c)) \<subseteq> ctype (Rep c)"
    and "chDom TYPE('fIn) \<subseteq> chDom TYPE('mOut)"
    and "chDom TYPE('fIn2) \<subseteq> chDom TYPE('mIn)"
    and "chDom TYPE('fIn2) \<inter> chDom TYPE('mOut \<union> 'fOut) = {}"
    and "chDom TYPE('mIn) \<inter> chDom TYPE('mOut) = {}"
    and "\<And>c::'mOut. Rep c \<in> chDom TYPE('mOut) \<Longrightarrow> Rep (m1 c) \<in> chDom TYPE('mIn)"
    and "\<And>c::'fIn. Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (m1 (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'fIn) - 'mOut \<union> 'fOut)"
    and "\<And>c. Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (m2 c) = Rep (m1 (Abs (Rep c)))"
  shows "sbRenameCh m1 \<otimes> f oo sbRenameCh m2 = spfConvert\<cdot>(sbRenameCh m1 \<otimes> f)"
  apply(rule cfun_eqI)
  apply(rule sb_eqI)
  apply(simp add: spfConvert_def)
  apply(case_tac "Rep c \<in> chDom TYPE('mOut)"; simp)
  apply(case_tac "Rep (m1 (Abs (Rep c))) \<in> chDom TYPE(('mIn \<union> 'fIn) - 'mOut \<union> 'fOut)")
  apply(subst(2) spfcomp_sbrename_getch_l[OF assms(1)], simp, simp)
  apply(subst spfcomp_sbrename_getch_l[OF assms(1)], simp)
  using assms(3,4) apply auto[2]
  apply(subst(2) spfcomp_sbrename_getch_lrl[OF assms(1)], simp, simp)
  using assms(7) apply auto[1]
  using assms(6) cdom_notempty cempty_rule cnotempty_cdom apply blast
  using assms(3) apply auto[1]
  using assms(8) apply auto[1]
  apply(subst spfcomp_sbrename_getch_lr[OF assms(1)], simp)
  using assms(3,4) apply auto[1]
  using assms(7) apply auto[1]
  using assms(6,7) chdomnotempty_rangeeq apply blast
  using assms(5) apply auto[1]
  apply(simp del: chdom_minus, rule spf_arg_cong, simp del: chdom_minus)
  apply(subst sbrenamech_getch[OF assms(2)])
  apply(subst sbrenamech_getch2[OF _ assms(1)])
  using assms(3) apply auto[1]
  apply(simp del: chdom_minus)
  apply(subst sbtypecast_getch2)
  using assms(3,4,8,9) apply auto[1]
  using assms(9) apply(simp add: sbgetch_insert)
  apply(subst(2) spfcomp_sbrename_getch_rl[OF assms(1)], simp)
  using assms(3) apply auto[1]
  using assms(8) apply auto[1]
  apply(subst spfcomp_getch_r, simp)
  using assms(5) apply auto[1]
  apply(simp, rule spf_arg_cong, simp)
  apply(subst sbrenamech_getch[OF assms(2)])
  apply(subst sbrenamech_getch2[OF _ assms(1)])
  using assms(3) apply auto[1]
  apply(simp, subst sbtypecast_getch2)
  using assms(3,4,8,9) apply auto[1]
  using assms(9) by(simp add: sbgetch_insert)

end

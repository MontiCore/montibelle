theory WrappedSPSComp

imports sps.SPSComp

begin

locale renameWell =
  fixes f :: "'cs1::{chan} \<Rightarrow> 'cs2::{chan}"
  assumes ctype_f: "\<And>c. ctype (Rep (f c)) = ctype (Rep c)"
begin

lemma empty_eq: "chDomEmpty TYPE('cs1) \<longleftrightarrow> chDomEmpty TYPE('cs2)"
  apply(rule iffI)
  apply(metis ctype_f dom2ctypeempty dom2ctypenempty)
  by(metis ctype_f dom2ctypeempty dom2ctypenempty)

end

locale wrappedSPS = rename_in: renameWell f_in + rename_out: renameWell f_out
    for f_in::"'In \<Rightarrow> 'WrappedIn"
    and f_out::"'WrappedOut \<Rightarrow> 'Out" +
assumes in_well: "\<And>c. \<not>chDomEmpty TYPE('In) \<Longrightarrow> (Rep c \<in> chDom TYPE('Out)) \<longleftrightarrow> (Rep (f_in c) \<in> chDom TYPE('WrappedOut))"
    and in_inverse: "\<And>c. \<not>chDomEmpty TYPE('In) \<Longrightarrow> Rep c \<in> chDom TYPE('Out) \<Longrightarrow> Rep (f_out (Abs (Rep (f_in c)))) = Rep c"
    and in_surj: "\<not>chDomEmpty TYPE('WrappedIn) \<Longrightarrow> surj f_in"
begin end

locale wrappedSPSComp = F: wrappedSPS f_in f_out + G: wrappedSPS g_in g_out
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and g_in::"'gIn \<Rightarrow> 'gWrappedIn"
    and g_out::"'gWrappedOut \<Rightarrow> 'gOut" +
assumes output_overlap: "\<And>c. Rep c \<notin> chDom TYPE('fWrappedOut) \<Longrightarrow>  Rep c \<in> chDom TYPE('gWrappedOut) \<Longrightarrow> Rep (g_out c) \<notin> chDom TYPE('fOut)"
    and input_overlap: "\<And>c. Rep c \<notin> chDom TYPE('fOut \<union> 'gOut) \<Longrightarrow> Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (f_in (Abs (Rep c))) = Rep (g_in c)"
    and f_in_well1: "\<And>c. \<not>chDomEmpty TYPE('fIn) \<longrightarrow> Rep c \<in> chDom TYPE('gOut) \<longrightarrow> Rep (f_in c) \<in> chDom TYPE('gWrappedOut)"
    and f_in_well2: "\<And>c. \<not>chDomEmpty TYPE('fIn) \<longrightarrow> Rep c \<notin> chDom TYPE('gOut) \<longrightarrow> Rep (f_in c) \<notin> chDom TYPE('gWrappedOut)"
    and f_in_inverse: "\<And>c. \<not>chDomEmpty TYPE('fIn) \<longrightarrow> Rep (f_in c) \<in> chDom TYPE('gWrappedOut) \<longrightarrow> Rep (g_out (Abs (Rep (f_in c)))) = Rep c"
    and g_in_well1: "\<And>c. \<not>chDomEmpty TYPE('gIn) \<longrightarrow> Rep c \<in> chDom TYPE('fOut) \<longrightarrow> Rep (g_in c) \<in> chDom TYPE('fWrappedOut)"
    and g_in_well2: "\<And>c. \<not>chDomEmpty TYPE('gIn) \<longrightarrow> Rep c \<notin> chDom TYPE('fOut) \<longrightarrow> Rep (g_in c) \<notin> chDom TYPE('fWrappedOut)"
    and g_in_inverse: "\<And>c. \<not>chDomEmpty TYPE('gIn) \<longrightarrow> Rep (g_in c) \<in> chDom TYPE('fWrappedOut) \<longrightarrow> Rep (f_out (Abs (Rep (g_in c)))) = Rep c"
begin


abbreviation comp_in:: "(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Rightarrow> (('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)" where
"comp_in c \<equiv> if Rep c \<in> chDom TYPE('fIn) 
                         then Abs (Rep (f_in (Abs (Rep c)))) 
                         else Abs (Rep (g_in (Abs (Rep c))))"

abbreviation comp_out:: "('fWrappedOut \<union> 'gWrappedOut) \<Rightarrow> ('fOut \<union> 'gOut)" where
"comp_out c \<equiv> if Rep c \<in> chDom TYPE('fWrappedOut) 
                         then Abs (Rep (f_out (Abs (Rep c)))) 
                         else Abs (Rep (g_out (Abs (Rep c))))"



lemma f_in_well: "\<And>c. Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> (Rep c \<in> chDom TYPE('fOut \<union> 'gOut)) \<longleftrightarrow> (Rep (f_in c) \<in> chDom TYPE('fWrappedOut \<union> 'gWrappedOut))"
  using F.in_well f_in_well1 f_in_well2 by fastforce

lemma g_in_well: "\<And>c. Rep c \<in> chDom TYPE('gIn) \<Longrightarrow> (Rep c \<in> chDom TYPE('fOut \<union> 'gOut)) \<longleftrightarrow> (Rep (g_in c) \<in> chDom TYPE('fWrappedOut \<union> 'gWrappedOut))"
  using G.in_well g_in_well1 g_in_well2 by fastforce


lemma comp_in_empty_implies1:
  assumes "chDomEmpty TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)"
  shows  "chDomEmpty TYPE(('fIn  \<union> 'gIn) - 'fOut \<union> 'gOut)"
proof (rule ccontr)
  assume "\<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)"
  then obtain x where elem: "x \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)" by force
  have elem2: "x \<in> chDom TYPE('fIn \<union> 'gIn)"
    using elem by simp
  have elem3: "x \<notin> chDom TYPE('fOut)"
    using elem by simp
  have elem4: "x \<notin> chDom TYPE('gOut)"
    using elem by simp

  show "False"
  proof(cases "x \<in> chDom TYPE('fIn)")
    case True
    have notempty: "\<not>chDomEmpty TYPE('fIn)"
      using True by blast
    
    have "Rep ((Abs x) :: 'fIn) \<notin> chDom TYPE('fOut)"
      using True elem3 by simp
    then have notin1: "Rep (f_in (Abs x)) \<notin> chDom TYPE('fWrappedOut)"
      using notempty subst F.in_well by force

    have "Rep ((Abs x) :: 'fIn) \<notin> chDom TYPE('gOut)"
      using True elem4 by simp
    then have notin2: "Rep (f_in (Abs x)) \<notin> chDom TYPE('gWrappedOut)"
      using notempty by(subst f_in_well2, simp, simp, simp)

    have "Rep (f_in (Abs x)) \<in> chDom TYPE('fWrappedIn)"
      using notempty F.rename_in.empty_eq by simp
    then have "Rep (f_in (Abs x)) \<in> chDom TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)"
      using notin1 notin2 by simp
    then show ?thesis using assms by force
  next
    case False
    have elem5: "x \<in> chDom TYPE('gIn)" using elem2 False by simp
    then have notempty: "\<not>chDomEmpty TYPE('gIn)"
      by blast

    have "Rep ((Abs x) :: 'gIn) \<notin> chDom TYPE('fOut)"
      using elem5 elem3 by simp
    then have notin1: "Rep (g_in (Abs x)) \<notin> chDom TYPE('fWrappedOut)"
      using notempty by(subst g_in_well2, simp, simp, simp)

    have "Rep ((Abs x) :: 'gIn) \<notin> chDom TYPE('gOut)"
      using elem5 elem4 by simp
    then have notin2: "Rep (g_in (Abs x)) \<notin> chDom TYPE('gWrappedOut)"
      using notempty G.in_well by force

    have "Rep (g_in (Abs x)) \<in> chDom TYPE('gWrappedIn)"
      using notempty G.rename_in.empty_eq by simp
    then have "Rep (g_in (Abs x)) \<in> chDom TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)"
      using notin1 notin2 by simp
    then show ?thesis using assms by force
  qed
qed

lemma comp_in_empty_implies2:
  assumes "chDomEmpty TYPE(('fIn  \<union> 'gIn) - 'fOut \<union> 'gOut)"
  shows  "chDomEmpty TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)"
proof (rule ccontr)
  assume asm: "\<not>chDomEmpty TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)"
  then obtain x where elem: "x \<in> chDom TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)" by force
  have elem2: "x \<in> chDom TYPE('fWrappedIn \<union> 'gWrappedIn)"
    using elem by simp
  have elem3: "x \<notin> chDom TYPE('fWrappedOut)"
    using elem by simp
  have elem4: "x \<notin> chDom TYPE('gWrappedOut)"
    using elem by simp

  show "False"
  proof(cases "x \<in> chDom TYPE('fWrappedIn)")
    case True
    have notempty: "\<not>chDomEmpty TYPE('fWrappedIn)"
      using True by blast

    obtain y where elemy: "x = Rep (f_in y)"
      by (metis notempty F.in_surj True rep_reduction surjD)

    have "Rep ((Abs x) :: 'fWrappedIn) \<notin> chDom TYPE('fWrappedOut)"
      using True elem3 by simp
    then have notin1: "Rep y \<notin> chDom TYPE('fOut)"
      by (metis True notempty elemy rep_reduction F.rename_in.empty_eq F.in_well)

    have "Rep ((Abs x) :: 'fWrappedIn) \<notin> chDom TYPE('gWrappedOut)"
      using True elem4 by simp
    then have notin2: "Rep y \<notin> chDom TYPE('gOut)"
      using notempty elemy elem4 f_in_well1 F.rename_in.empty_eq by blast

    have "Rep y \<in> chDom TYPE('fIn)"
      using notempty F.rename_in.empty_eq elemy by simp
    then have "Rep y \<in> chDom TYPE(('fIn  \<union> 'gIn) - 'fOut \<union> 'gOut)"
      using notin1 notin2 by simp
    then show ?thesis using assms by force
  next
    case False
    have elem5: "x \<in> chDom TYPE('gWrappedIn)" using elem2 False by simp
    then have notempty: "\<not>chDomEmpty TYPE('gWrappedIn)"
      by blast

    obtain y where elemy: "x = Rep (g_in y)"
      by (metis notempty G.in_surj elem5 rep_reduction surjD)

    have "Rep ((Abs x) :: 'gWrappedIn) \<notin> chDom TYPE('gWrappedOut)"
      using elem5 elem3 elem4 by simp
    then have notin1: "Rep y \<notin> chDom TYPE('gOut)"
      by (metis elem5 notempty elemy rep_reduction G.rename_in.empty_eq G.in_well)

    have "Rep ((Abs x) :: 'gWrappedIn) \<notin> chDom TYPE('gWrappedOut)"
      using elem5 elem4 by simp
    then have notin2: "Rep y \<notin> chDom TYPE('fOut)"
      using notempty elemy elem3 g_in_well1 G.rename_in.empty_eq by blast

    have "Rep y \<in> chDom TYPE('gIn)"
      using notempty G.rename_in.empty_eq elemy by simp
    then have "Rep y \<in> chDom TYPE(('fIn  \<union> 'gIn) - 'fOut \<union> 'gOut)"
      using notin1 notin2 by simp
    then show ?thesis using assms by force
  qed
qed

lemma comp_in_empty_eq: "chDomEmpty TYPE(('fIn  \<union> 'gIn) - 'fOut \<union> 'gOut) \<longleftrightarrow> chDomEmpty TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)"
  using comp_in_empty_implies1 comp_in_empty_implies2 by blast

lemma comp_out_empty_eq: "chDomEmpty TYPE('fOut \<union> 'gOut) \<longleftrightarrow> chDomEmpty TYPE('fWrappedOut \<union> 'gWrappedOut)"
  using F.rename_out.empty_eq G.rename_out.empty_eq by simp


lemma comp_in_eq1: "\<And>c. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (comp_in c) = Rep (f_in (Abs (Rep c)))"
  apply(subgoal_tac "Rep c \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)")
  apply(subgoal_tac "\<not>chDomEmpty TYPE('fWrappedIn)")
  apply(subgoal_tac "\<not>chDomEmpty TYPE((('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut))")
  apply(simp del: chdom_minus chdom_union add: Abs_minus_def Rep_minus_def)
  apply(rule Abs_minus_inverse)
  apply(simp del: chdom_minus chdom_union)
  apply(rule conjI)
  apply fastforce
  apply(subgoal_tac "Rep (f_in (Abs (Rep_minus c))) \<in> chDom TYPE('fWrappedIn)")
  apply(subgoal_tac "Rep (Abs (Rep_minus c)) \<notin> chDom TYPE('fOut \<union> 'gOut)")
  apply(subgoal_tac "Rep (Abs (Rep_minus c)) \<in> chDom TYPE('fIn)")
  using f_in_well apply simp apply blast
  apply simp
  apply simp
  using F.rename_in.empty_eq apply simp
  using comp_in_empty_eq apply blast
  using F.rename_in.empty_eq apply blast
  using chdom_in by blast

lemma comp_in_eq2: "\<And>c. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep c \<notin> chDom TYPE('fIn) \<Longrightarrow> Rep (comp_in c) = Rep (g_in (Abs (Rep c)))"
  apply(subgoal_tac "Rep c \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)")
  apply(subgoal_tac "\<not>chDomEmpty TYPE((('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut))")
  apply(case_tac "Rep c \<in> chDom TYPE('gIn)")
  apply(subgoal_tac "\<not>chDomEmpty TYPE('gWrappedIn)")
  apply(simp del: chdom_minus chdom_union add: Abs_minus_def Rep_minus_def)
  apply(rule Abs_minus_inverse)
  apply(simp del: chdom_minus chdom_union)
  apply(rule conjI)
  apply fastforce
  apply(subgoal_tac "Rep (g_in (Abs (Rep_minus c))) \<in> chDom TYPE('gWrappedIn)")
  apply(subgoal_tac "Rep (Abs (Rep_minus c)) \<notin> chDom TYPE('fOut \<union> 'gOut)")
  apply(subgoal_tac "Rep (Abs (Rep_minus c)) \<in> chDom TYPE('gIn)")
  using g_in_well apply simp apply blast
  apply simp
  apply simp
  using G.rename_in.empty_eq apply simp
  using G.rename_in.empty_eq apply blast
  apply(subgoal_tac "chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)", simp)
  apply(rule minus_empty, simp)
  using comp_in_empty_eq apply blast
  using chdom_in by blast
  
lemma comp_out_eq1: "\<And>c. Rep c \<in> chDom TYPE('fWrappedOut) \<Longrightarrow> Rep (comp_out c) = Rep (f_out (Abs (Rep c)))"
  apply(simp del: chdom_union add: Abs_union_def Rep_union_def)
  apply(rule Abs_union_inverse, simp)
  by(metis all_not_in_conv chdom_in F.rename_out.empty_eq)

lemma comp_out_eq2: "\<And>c. Rep c \<notin> chDom TYPE('fWrappedOut) \<Longrightarrow> Rep c \<in> chDom TYPE('gWrappedOut) \<Longrightarrow> Rep (comp_out c) = Rep (g_out (Abs (Rep c)))"
  apply(simp del: chdom_union add: Abs_union_def Rep_union_def)
  apply(rule Abs_union_inverse, simp)
  by(metis all_not_in_conv chdom_in G.rename_out.empty_eq)



lemma comp_in_property:
assumes "\<And>c. \<not>chDomEmpty TYPE('fIn - 'fOut \<union> 'gOut) \<Longrightarrow> P (Rep c) (Rep (f_in c))"
    and "\<And>c. \<not>chDomEmpty TYPE('gIn - 'fOut \<union> 'gOut) \<Longrightarrow> P (Rep c) (Rep (g_in c))"
  shows "\<And>c. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> P (Rep c) (Rep (comp_in c))"
  apply(case_tac "Rep c \<in> chDom TYPE('fIn)")
  apply(subst comp_in_eq1)
  using cdom_notempty cempty_rule apply blast
  apply simp
  using assms(1) rep_reduction union_minus_notempty_left apply metis
  apply(case_tac "Rep c \<in> chDom TYPE('gIn)")
  apply(subst comp_in_eq2)
  using cdom_notempty cempty_rule apply blast
  apply simp
  using assms(2) rep_reduction union_minus_notempty_right apply metis
  apply(subgoal_tac "chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)")
  using assms(1) apply simp
  by(rule minus_empty, simp)

lemma comp_out_property:
assumes "\<And>c. \<not>chDomEmpty TYPE('fWrappedOut) \<Longrightarrow> P (Rep c) (Rep (f_out c))"
    and "\<And>c. \<not>chDomEmpty TYPE('gWrappedOut) \<Longrightarrow> P (Rep c) (Rep (g_out c))"
  shows "\<And>c. \<not>chDomEmpty TYPE('fWrappedOut \<union> 'gWrappedOut) \<Longrightarrow> P (Rep c) (Rep (comp_out c))"
  apply(case_tac "Rep c \<in> chDom TYPE('fWrappedOut)")
  apply(subst comp_out_eq1, simp)
  using assms(1) rep_reduction empty_iff apply metis
  apply(case_tac "Rep c \<in> chDom TYPE('gWrappedOut)")
  apply(subst comp_out_eq2, simp, simp)
  using assms(2) rep_reduction empty_iff apply metis
  apply(subgoal_tac "chDomEmpty TYPE('fWrappedOut \<union> 'gWrappedOut)", simp)
  by(rule union_empty, simp)


lemma comp_in_ctype: "\<And>c. ctype (Rep (comp_in c)) = ctype (Rep c)"
  apply(case_tac "chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)")
  apply(subgoal_tac "chDomEmpty TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)", simp)
  using comp_in_empty_eq apply blast
  apply(rule comp_in_property)
  apply(rule F.rename_in.ctype_f)
  apply(rule G.rename_in.ctype_f)
  by simp

lemma comp_out_ctype: "\<And>c. ctype (Rep (comp_out c)) = ctype (Rep c)"
  apply(case_tac "chDomEmpty TYPE('fWrappedOut \<union> 'gWrappedOut)")
  apply(subgoal_tac "chDomEmpty TYPE('fOut \<union> 'gOut)", simp)
  using comp_out_empty_eq apply blast
  apply(rule comp_out_property)
  apply(rule F.rename_out.ctype_f)
  apply(rule G.rename_out.ctype_f)
  by simp

lemma comp_in_well: "\<And>c. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> (Rep c \<in> chDom TYPE('fOut \<union> 'gOut)) = (Rep (comp_in c) \<in> chDom TYPE('fWrappedOut \<union> 'gWrappedOut))"
  apply(rule comp_in_property)
  apply(rule f_in_well) using minus_notempty apply blast
  apply(rule g_in_well) using minus_notempty apply blast
  by simp

lemma comp_in_inverse: "\<And>c. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> Rep c \<in> chDom TYPE('fOut \<union> 'gOut) \<Longrightarrow> Rep (comp_out (Abs (Rep (comp_in c)))) = Rep c"
  apply(subgoal_tac "Rep c \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)", simp)
  by(rule inchdom, simp)

lemma comp_in_surj: 
  assumes "\<not>chDomEmpty TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)"
  shows "surj comp_in"
proof(subst surj_def, rule allI)
  fix y::"('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut"
  have elem1: "Rep y \<in> chDom TYPE(('fWrappedIn \<union> 'gWrappedIn) - 'fWrappedOut \<union> 'gWrappedOut)"
    using assms chdom_in by blast
  have elem2: "Rep y \<in> chDom TYPE('fWrappedIn \<union> 'gWrappedIn)"
    using elem1 by simp
  have elem3: "Rep y \<notin> chDom TYPE('fWrappedOut)"
    using elem1 by simp
  have elem4: "Rep y \<notin> chDom TYPE('gWrappedOut)"
    using elem1 by simp

  show "\<exists>x. y = comp_in x"
  proof(cases "Rep y \<in> chDom TYPE('fWrappedIn)")
    case True
    have notempty: "\<not>chDomEmpty TYPE('fWrappedIn)" using True by blast

    obtain x where elemx: "Rep y = Rep (f_in x)"
      by (metis notempty F.in_surj True rep_reduction surjD)

    have xin: "Rep x \<in> chDom TYPE('fIn)"
      using elemx chdom_in notempty F.rename_in.empty_eq by blast
    moreover have "Rep x \<notin> chDom TYPE('fOut)"
      using elemx elem3 notempty F.rename_in.empty_eq F.in_well by presburger
    moreover have "Rep x \<notin> chDom TYPE('gOut)"
      by (metis elemx elem4 f_in_well1 notempty F.rename_in.empty_eq)
    ultimately have "Rep x \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)"
      by simp
    then have "y = comp_in (Abs (Rep x))"
      using xin apply simp using elemx by (metis abs_rep_id)
    then show ?thesis
      by blast
  next
    case False
    then have elem5: "Rep y \<in> chDom TYPE('gWrappedIn)"
      using False elem2 by force
    have notempty: "\<not>chDomEmpty TYPE('gWrappedIn)" using elem5 by blast

    obtain x where elemx: "Rep y = Rep (g_in x)"
      by (metis notempty G.in_surj elem5 rep_reduction surjD)
    then show ?thesis
    proof(cases "Rep x \<in> chDom TYPE('fIn)")
      case True
      have "Rep x \<notin> chDom TYPE('fOut)"
        by (metis elemx elem3 g_in_well1 notempty G.rename_in.empty_eq)
      moreover have "Rep x \<notin> chDom TYPE('gOut)"
        using elemx elem4 notempty G.rename_in.empty_eq G.in_well by presburger
      ultimately have "Rep x \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)"
        using True by simp
      then have "y = comp_in (Abs (Rep x))"
        using True apply simp
        apply(subst input_overlap, simp, simp)
        using elemx by (metis abs_rep_id)
      then show ?thesis
        by blast
    next
      case False
      have xin: "Rep x \<in> chDom TYPE('gIn)"
        using elemx chdom_in notempty G.rename_in.empty_eq by blast
      moreover have "Rep x \<notin> chDom TYPE('fOut)"
        by (metis elemx elem3 g_in_well1 notempty G.rename_in.empty_eq)
      moreover have "Rep x \<notin> chDom TYPE('gOut)"
        using elemx elem4 notempty G.rename_in.empty_eq G.in_well by presburger
      ultimately have "Rep x \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut)"
        by simp
      then have "y = comp_in (Abs (Rep x))"
        using xin False apply simp 
        using elemx by (metis abs_rep_id)
      then show ?thesis
        by blast
    qed
  qed
qed


named_theorems named_comp_inverse_decompose

lemma comp_out_inverse_decompose[named_comp_inverse_decompose]: 
  fixes f_in2 ::"'fIn2 \<Rightarrow> 'fWrappedIn2"
assumes "\<And>c. \<not>chDomEmpty TYPE('fIn2) \<longrightarrow> Rep (f_in2 c) \<in> chDom TYPE('fWrappedOut) \<longrightarrow> Rep (f_out (Abs (Rep (f_in2 c)))) = Rep c"
    and "\<And>c. \<not>chDomEmpty TYPE('fIn2) \<longrightarrow> Rep (f_in2 c) \<in> chDom TYPE('gWrappedOut) \<longrightarrow> Rep (g_out (Abs (Rep (f_in2 c)))) = Rep c"
  shows "\<And>c. \<not>chDomEmpty TYPE('fIn2) \<longrightarrow> Rep (f_in2 c) \<in> chDom TYPE('fWrappedOut \<union> 'gWrappedOut) \<longrightarrow> Rep (comp_out (Abs (Rep (f_in2 c)))) = Rep c"
  apply(rule impI)
  apply(case_tac "Rep (f_in2 c) \<in> chDom TYPE('fWrappedOut)")
  apply(subst comp_out_eq1, simp)
  apply(simp add: Abs_union_def Rep_union_def del: chdom_union)
  apply(subst Abs_union_inverse)
  apply(metis Un_iff empty_iff)
  apply(subst assms(1); simp)
  apply(case_tac "Rep (f_in2 c) \<in> chDom TYPE('gWrappedOut)")
  apply(subst comp_out_eq2, simp, simp)
  apply(simp add: Abs_union_def Rep_union_def del: chdom_union)
  apply(subst Abs_union_inverse)
  apply(metis Un_iff empty_iff)
  apply(subst assms(2); simp)
  by simp

lemma comp_in_inverse_decompose[named_comp_inverse_decompose]: 
  fixes f_out2 ::"'fWrappedOut2 \<Rightarrow> 'fOut2"
assumes "\<And>c. \<not>chDomEmpty TYPE('fIn) \<longrightarrow> Rep (f_in c) \<in> chDom TYPE('fWrappedOut2) \<longrightarrow> Rep (f_out2 (Abs (Rep (f_in c)))) = Rep c"
    and "\<And>c. \<not>chDomEmpty TYPE('gIn) \<longrightarrow> Rep (g_in c) \<in> chDom TYPE('fWrappedOut2) \<longrightarrow> Rep (f_out2 (Abs (Rep (g_in c)))) = Rep c"
  shows "\<And>c. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<longrightarrow> Rep (comp_in c) \<in> chDom TYPE('fWrappedOut2) \<longrightarrow> Rep (f_out2 (Abs (Rep (comp_in c)))) = Rep c"
  apply(rule impI)
  apply(rule comp_in_property; (rule impI | simp))
  apply(subst assms(1); simp)
  apply fastforce
  apply(subst assms(2); simp)
  by fastforce

named_theorems named_comp_in_well1_decompose

lemma comp_in_well1_decompose[named_comp_in_well1_decompose]:
assumes "\<And>c. \<not>chDomEmpty TYPE('fIn) \<longrightarrow> Rep c \<in> chDom TYPE('Out) \<longrightarrow> Rep (f_in c) \<in> chDom TYPE('WrappedOut)"
    and "\<And>c. \<not>chDomEmpty TYPE('gIn) \<longrightarrow> Rep c \<in> chDom TYPE('Out) \<longrightarrow> Rep (g_in c) \<in> chDom TYPE('WrappedOut)"
  shows "\<And>c. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<longrightarrow> Rep c \<in> chDom TYPE('Out) \<longrightarrow> Rep (comp_in c) \<in> chDom TYPE('WrappedOut)"
  apply(rule impI)
  apply(rule comp_in_property)
  apply(rule impI)
  apply(subst assms(1)) using minus_notempty apply(blast, simp, simp)
  apply(rule impI)
  apply(subst assms(2)) using minus_notempty apply(blast, simp, simp)
  by simp

named_theorems named_comp_in_well2_decompose

lemma comp_in_well2_decompose[named_comp_in_well2_decompose]:
assumes "\<And>c. \<not>chDomEmpty TYPE('fIn) \<longrightarrow> Rep c \<notin> chDom TYPE('Out) \<longrightarrow> Rep (f_in c) \<notin> chDom TYPE('WrappedOut)"
    and "\<And>c. \<not>chDomEmpty TYPE('gIn) \<longrightarrow> Rep c \<notin> chDom TYPE('Out) \<longrightarrow> Rep (g_in c) \<notin> chDom TYPE('WrappedOut)"
  shows "\<And>c. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<longrightarrow> Rep c \<notin> chDom TYPE('Out) \<longrightarrow> Rep (comp_in c) \<notin> chDom TYPE('WrappedOut)"
  apply(rule impI)
  apply(rule comp_in_property)
  apply(rule impI)
  apply(subst assms(1)) using minus_notempty apply(blast, simp, simp)
  apply(rule impI)
  apply(subst assms(2)) using minus_notempty apply(blast, simp, simp)
  by simp


lemma assumption1: "sbRenameCh comp_out\<cdot>\<bottom> = \<bottom>"
  apply(rule sbrename_strict)
  using comp_out_ctype by blast

lemma assumption2:
assumes "Rep c \<in> chDom TYPE('fWrappedOut)"
  shows "sbRenameCh comp_out\<cdot>(out1 \<uplus> out2)  \<^enum>  c = sbRenameCh f_out\<cdot>out1  \<^enum>\<^sub>\<star>  c"
  apply(subst sbrenamech_getch)
  using comp_out_ctype apply blast
  apply(subst sbrenamech_getch2[OF assms], simp add: F.rename_out.ctype_f)
  apply(simp add: assms)
  apply(subst sbunion_getchl)
  apply(metis Un_iff assms F.rename_out.empty_eq chdom_in chdom_union empty_iff rep_reduction)
  apply(simp add: sbgetch_insert)
  using cnotempty_cdom by blast

lemma assumption3:
assumes "Rep c \<notin> chDom TYPE('fWrappedOut)"
  shows "sbRenameCh comp_out\<cdot>(out1 \<uplus> out2)  \<^enum>  c = sbRenameCh g_out\<cdot>out2  \<^enum>\<^sub>\<star>  c"
  apply(subst sbrenamech_getch)
  using comp_out_ctype apply blast
  apply(case_tac "Rep c \<in> chDom TYPE('gWrappedOut)")
  apply(subst sbrenamech_getch2, simp, simp add: G.rename_out.ctype_f)
  apply(simp add: assms)
  apply(subst sbunion_getchr)
  apply(simp add: Abs_union_def Rep_union_def, subst Abs_union_inverse)
  apply(metis Un_iff chdomnotempty_rangeeq empty_iff repinrange G.rename_out.empty_eq)
  apply(metis Rep_union_def assms output_overlap rep_reduction)
  apply(simp add: sbgetch_insert)
  using cnotempty_cdom apply blast
  apply(subgoal_tac "chDomEmpty TYPE('fOut \<union> 'gOut)", simp)
  apply(subgoal_tac "chDomEmpty TYPE('fWrappedOut \<union> 'gWrappedOut)")
  using comp_out_empty_eq apply force
  using assms union_empty by blast

lemma assumption4:
assumes "\<not>chDomEmpty TYPE('fIn)"
    and "Rep c \<in> chDom TYPE('fOut \<union> 'gOut)"
    and "Rep (f_in c) \<in> chDom TYPE('fWrappedOut \<union> 'gWrappedOut)"
  shows "sbRenameCh f_in\<cdot>(x \<uplus>\<^sub>- sbRenameCh comp_out\<cdot>y\<star>\<^sub>1)  \<^enum>  c = y  \<^enum>\<^sub>\<star>  c"
  apply(subst sbrenamech_getch, simp add: F.rename_in.ctype_f, simp)
  apply(subst sbunion_minus_getchr)
  using assms(1) F.rename_in.empty_eq apply force
  using assms(3) apply force
  apply(subst sbrenamech_getch2)
  using assms(3) apply force
  using comp_out_ctype apply blast
  apply(case_tac "Rep (f_in c) \<in> chDom TYPE('fWrappedOut)"; simp)
  apply(subst F.in_inverse)
  apply(simp add: assms(1))
  using F.in_well assms(1) apply blast
  apply(simp add: sbgetch_insert)
  using assms(2) apply force
  apply(case_tac "Rep (f_in c) \<in> chDom TYPE('gWrappedOut)")
  apply simp
  apply(subst f_in_inverse)
  apply(simp add: assms(1))
  using assms(1) f_in_well2 apply blast
  apply(simp add: sbgetch_insert)
  using assms(2) apply force
  using assms(3) by simp

lemma assumption5:
assumes "\<not>chDomEmpty TYPE('gIn)"
    and "Rep c \<in> chDom TYPE('fOut \<union> 'gOut)"
    and "Rep (g_in c) \<in> chDom TYPE('fWrappedOut \<union> 'gWrappedOut)"
  shows "sbRenameCh g_in\<cdot>(x \<uplus>\<^sub>- sbRenameCh comp_out\<cdot>y\<star>\<^sub>2)  \<^enum>  c = y  \<^enum>\<^sub>\<star>  c"
  apply(subst sbrenamech_getch, simp add: G.rename_in.ctype_f, simp)
  apply(subst sbunion_minus_getchr)
  using assms(1) G.rename_in.empty_eq apply force
  using assms(3) apply force
  apply(subst sbrenamech_getch2)
  using assms(3) apply force
  using comp_out_ctype apply blast
  apply(case_tac "Rep (g_in c) \<in> chDom TYPE('fWrappedOut)"; simp)
  apply(subst g_in_inverse)
  apply(simp add: assms(1))
  using g_in_well2 assms(1) apply blast
  apply(simp add: sbgetch_insert)
  using assms(2) apply force
  apply(case_tac "Rep (g_in c) \<in> chDom TYPE('gWrappedOut)")
  apply simp
  apply(subst G.in_inverse)
  apply(simp add: assms(1))
  using G.in_well assms(1) apply blast
  apply(simp add: sbgetch_insert)
  using assms(2) apply force
  using assms(3) by simp

lemma assumption6:
assumes "\<not>chDomEmpty TYPE('fIn)"
    and "Rep c \<notin> chDom TYPE('fOut \<union> 'gOut)"
    and "Rep (f_in c) \<notin> chDom TYPE('fWrappedOut \<union> 'gWrappedOut)"
  shows "sbRenameCh f_in\<cdot>(x \<uplus>\<^sub>- sbRenameCh comp_out\<cdot>y\<star>\<^sub>1)  \<^enum>  c = sbRenameCh comp_in\<cdot>x  \<^enum>\<^sub>\<star>  c"
  apply(subst sbrenamech_getch, simp add: F.rename_in.ctype_f, simp)
  apply(subst sbunion_minus_getchl)
  using F.rename_in.empty_eq assms(1) assms(3) apply simp
  apply(subst sbrenamech_getch2)
  using assms(1) assms(2) apply simp
  using comp_in_ctype apply simp
  using F.rename_in.empty_eq assms(1) assms(2) apply simp
  using assms(3) by(simp add: sbgetch_insert)

lemma assumption7:
assumes "\<not>chDomEmpty TYPE('gIn)"
    and "Rep c \<notin> chDom TYPE('fOut \<union> 'gOut)"
    and "Rep (g_in c) \<notin> chDom TYPE('fWrappedOut \<union> 'gWrappedOut)"
  shows "sbRenameCh g_in\<cdot>(x \<uplus>\<^sub>- sbRenameCh comp_out\<cdot>y\<star>\<^sub>2)  \<^enum>  c = sbRenameCh comp_in\<cdot>x  \<^enum>\<^sub>\<star>  c"
  apply(subst sbrenamech_getch, simp add: G.rename_in.ctype_f, simp)
  apply(subst sbunion_minus_getchl)
  using G.rename_in.empty_eq assms(1) assms(3) apply simp
  apply(subst sbrenamech_getch2)
  using assms(1) assms(2) apply simp
  using comp_in_ctype apply simp
  using G.rename_in.empty_eq assms(1) assms(2) assms(3) apply simp
  apply(rule conjI) 
  apply(rule impI)
  apply(subst input_overlap, simp, simp)
  by(simp add: sbgetch_insert)+

named_theorems named_sps_comp_eq

lemma sps_comp_eq[named_sps_comp_eq]: "({sbRenameCh f_in} \<then> F \<then> {sbRenameCh f_out}) \<Otimes>
                    ({sbRenameCh g_in} \<then> G \<then> {sbRenameCh g_out}) =
                     {sbRenameCh comp_in} \<then> (F \<Otimes> G) \<then> {sbRenameCh comp_out}"
  apply(rule wrapped_sps_comp_eq)
  apply(rule assumption1)
  apply(rule impI, rule assumption2, simp)
  apply(rule impI, rule assumption3, simp)
  apply(rule impI, rule impI, rule assumption4; simp) using f_in_well apply simp
  apply(rule impI, rule impI, rule assumption5; simp) using g_in_well apply simp
  apply(rule impI, rule impI, rule assumption6; simp) using f_in_well apply force
  apply(rule impI, rule impI, rule assumption7; simp) using g_in_well by force

end

sublocale wrappedSPSComp \<subseteq> wrappedSPS comp_in comp_out
  apply(standard)
  using comp_in_ctype apply blast
  using comp_out_ctype apply blast
  using comp_in_well apply blast
  using comp_in_inverse apply blast
  using comp_in_surj by blast

locale wrappedSPSCompNoOverlap = F: wrappedSPS f_in f_out + G: wrappedSPS g_in g_out
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and g_in::"'gIn \<Rightarrow> 'gWrappedIn"
    and g_out::"'gWrappedOut \<Rightarrow> 'gOut" +
assumes no_output_overlap: "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and no_input_overlap: "chDom TYPE('fIn) \<inter> chDom TYPE('gIn) = {}"
    and f_in_well1_: "\<And>c. \<not>chDomEmpty TYPE('fIn) \<longrightarrow> Rep c \<in> chDom TYPE('gOut) \<longrightarrow> Rep (f_in c) \<in> chDom TYPE('gWrappedOut)"
    and f_in_well2_: "\<And>c. \<not>chDomEmpty TYPE('fIn) \<longrightarrow> Rep c \<notin> chDom TYPE('gOut) \<longrightarrow> Rep (f_in c) \<notin> chDom TYPE('gWrappedOut)"
    and f_in_inverse_: "\<And>c. \<not>chDomEmpty TYPE('fIn) \<longrightarrow> Rep (f_in c) \<in> chDom TYPE('gWrappedOut) \<longrightarrow> Rep (g_out (Abs (Rep (f_in c)))) = Rep c"
    and g_in_well1_: "\<And>c. \<not>chDomEmpty TYPE('gIn) \<longrightarrow> Rep c \<in> chDom TYPE('fOut) \<longrightarrow> Rep (g_in c) \<in> chDom TYPE('fWrappedOut)"
    and g_in_well2_: "\<And>c. \<not>chDomEmpty TYPE('gIn) \<longrightarrow> Rep c \<notin> chDom TYPE('fOut) \<longrightarrow> Rep (g_in c) \<notin> chDom TYPE('fWrappedOut)"
    and g_in_inverse_: "\<And>c. \<not>chDomEmpty TYPE('gIn) \<longrightarrow> Rep (g_in c) \<in> chDom TYPE('fWrappedOut) \<longrightarrow> Rep (f_out (Abs (Rep (g_in c)))) = Rep c"
begin end

sublocale wrappedSPSCompNoOverlap \<subseteq> wrappedSPSComp f_in f_out g_in g_out
  apply(standard)
  using no_output_overlap chdom_in G.rename_out.empty_eq apply blast
  using no_input_overlap cdom_notempty cempty_rule chdomnotempty_rangeeq apply blast
  apply(rule f_in_well1_)
  apply(rule f_in_well2_)
  apply(rule f_in_inverse_)
  apply(rule g_in_well1_)
  apply(rule g_in_well2_)
  by(rule g_in_inverse_)

locale wrappedSPSCompParallel = F: wrappedSPS f_in f_out + G: wrappedSPS g_in g_out
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and g_in::"'gIn \<Rightarrow> 'gWrappedIn"
    and g_out::"'gWrappedOut \<Rightarrow> 'gOut" +
assumes no_output_overlap_: "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
    and no_input_overlap_: "chDom TYPE('fIn) \<inter> chDom TYPE('gIn) = {}"
    and no_feedback1: "chDom TYPE('fIn \<union> 'gIn) \<inter> chDom TYPE('fOut \<union> 'gOut) = {}"
    and no_feedback2: "chDom TYPE('fWrappedIn \<union> 'gWrappedIn) \<inter> chDom TYPE('fWrappedOut \<union> 'gWrappedOut) = {}"
begin end

sublocale wrappedSPSCompParallel \<subseteq> wrappedSPSCompNoOverlap f_in f_out g_in g_out
  apply(standard)
  apply(rule no_output_overlap_)
  apply(rule no_input_overlap_)
  using chdom_in no_feedback1 apply force
  using cdom2cdom no_feedback2 apply force 
  using cdom2cdom no_feedback2 apply force
  using chdom_in no_feedback1 apply force
  using cdom2cdom no_feedback2 apply force
  using cdom2cdom no_feedback2 by force

end

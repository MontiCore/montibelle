theory SBv1
imports bundle.SB "../00.inc/DEPRECATED/CPOFix" spf.SPF

begin

lemma ctype_notempty: "ctype (CH '''' undefined {undefined}) \<noteq> {}"
  by (simp add: ctype_empty_iff)
  
typedef msgchannel = "UNIV-cEmpty"
  using ctype_notempty cEmpty_def by blast

instantiation msgchannel::chan
begin

definition Rep_msgchannel_def: "Rep = Rep_msgchannel"
definition Abs_msgchannel_def:"Abs = Abs_msgchannel"
definition chanDom_msgchannel_def:"chanDom(a::msgchannel myself) = (UNIV-cEmpty)"

instance
  apply(intro_classes)
  apply(simp_all add: chanDom_msgchannel_def Rep_msgchannel_inverse Rep_msgchannel_def Abs_msgchannel_def)
  using type_definition.Rep_range type_definition_msgchannel by fastforce+

end

typedef sbv1 = "{(cs::msgchannel set,sb::msgchannel sb) | cs sb .
  \<forall>c. c \<notin> cs \<longrightarrow> sb \<^enum> c = \<epsilon>}"
  by blast

instantiation sbv1::pcpo
begin
instance
  sorry
end


definition sbv1Least:: "msgchannel set \<Rightarrow> sbv1" where
"sbv1Least A = undefined"

definition sbv1Union:: "msgchannel\<^sup>\<Omega> \<rightarrow> msgchannel\<^sup>\<Omega> \<rightarrow> msgchannel\<^sup>\<Omega>" where
"sbv1Union = undefined"

definition sbv1Combine:: "(msgchannel\<^sup>\<Omega>) list \<Rightarrow> msgchannel\<^sup>\<Omega>" where
"sbv1Combine ls = fold (\<lambda>x y. sbv1Union\<cdot>x\<cdot>y) ls \<bottom>"


definition spfv1Comp::"(sbv1 \<rightarrow> sbv1) set \<Rightarrow>  (sbv1 \<rightarrow> sbv1)" where
"spfv1Comp spfSet = fixg (\<Lambda> _ . sbv1Least undefined)\<cdot>undefined"


definition spfV3toV1::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<rightarrow> (msgchannel\<^sup>\<Omega> \<rightarrow> msgchannel\<^sup>\<Omega>)" where
"spfV3toV1 = spfConvert"

definition spfV1toV3::"(msgchannel\<^sup>\<Omega> \<rightarrow> msgchannel\<^sup>\<Omega>) \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"spfV1toV3 = spfConvert"

lemma msgchan_greatest[simp]: "chDom TYPE('chan) \<subseteq> chDom TYPE(msgchannel)"
  apply (simp add: chDom_def Rep_msgchannel_def)
  by (metis Diff_mono Rep_msgchannel_def chanDom chanDom_msgchannel_def dual_order.refl top_greatest)

lemma "spfV1toV3\<cdot>(spfV3toV1\<cdot>spf) = spf"
  by(simp add: spfV3toV1_def spfV1toV3_def spfConvert_def oo_def) 


definition spfv1Comp_21::"(msgchannel\<^sup>\<Omega> \<rightarrow> msgchannel\<^sup>\<Omega>) list \<Rightarrow>  (msgchannel\<^sup>\<Omega> \<rightarrow> msgchannel\<^sup>\<Omega>)" where
"spfv1Comp_21 spfList = fix\<cdot>(\<Lambda> f sbIn. sbv1Combine (map (\<lambda>spf. spf\<cdot>(sbIn \<uplus>\<^sub>\<star> f\<cdot>sbIn)) spfList))"

                                                                                       
lemma map_fold_cont[cont2cont]: "cont f \<Longrightarrow> cont g \<Longrightarrow> (\<And>x. cont (g x)) \<Longrightarrow> cont (\<lambda>x. foldr g (map (f x) ls))"
  apply(induction ls; simp)
  apply(simp add: o_def)
  apply(intro cont2cont)
proof -
  fix a :: 'b and ls :: "'b list" and y :: 'd
  assume foldr_cont: "cont (\<lambda>x. foldr g (map (f x) ls))"
  assume f_cont: "cont f"
  assume g_cont: "cont g"
  assume gx_cont: "\<And>x. cont (g x)"

  have g_fxa_cont: "cont (\<lambda>x. g (f x a))"
    using gx_cont f_cont cont2cont_fun cont2cont by (metis cont_compose g_cont)

  have foldr_y_cont: "cont (\<lambda>x. foldr g (map (f x) ls) y)"
    using foldr_cont by (rule cont2cont_fun)

  have f1: "\<forall>d. cont (\<lambda>aa. g (f aa a) d)"
      by (metis (no_types) cont2cont_fun g_fxa_cont)

  from g_fxa_cont foldr_y_cont gx_cont
  show "cont (\<lambda>x. g (f x a) (foldr g (map (f x) ls) y))"
    using cont_apply f1 by fastforce
qed

lemma asb_:"cont (\<lambda> sbIn. sbv1Combine (map (\<lambda>spf. spf\<cdot>(sbIn \<uplus>\<^sub>\<star> f\<cdot>sbIn)) spfList))"
  apply(simp add: sbv1Combine_def)
  apply(insert map_fold_cont[where f="(\<lambda>sbIn spf. spf\<cdot>(sbIn \<uplus>\<^sub>\<star> f\<cdot>sbIn))"])
  using cont2cont_fun by fastforce


definition spfv1Comp_2::"(msgchannel\<^sup>\<Omega> \<rightarrow> msgchannel\<^sup>\<Omega>) list \<Rightarrow>  (msgchannel\<^sup>\<Omega> \<rightarrow> msgchannel\<^sup>\<Omega>)" where
"spfv1Comp_2 spfList = fix\<cdot>(\<Lambda> f sb. fold(\<lambda>spf sbPrev. sbv1Union (spf\<cdot>sbPrev) sbPrev) spfList (f\<cdot>sb))"


definition spfv1Comp_3::"(sbv1 \<rightarrow> msgchannel\<^sup>\<Omega>) set \<Rightarrow>  (sbv1 \<rightarrow> msgchannel\<^sup>\<Omega>)" where
"spfv1Comp_3 spfSet = fix\<cdot>undefined"

end
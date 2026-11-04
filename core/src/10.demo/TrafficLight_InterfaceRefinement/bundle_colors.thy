theory bundle_colors

imports bundlelocale.SBGen

begin

default_sort countable

typedef cs = "{(CH ''cButton'' TTLive (range COLOR))}" 
  by auto

definition cButton :: cs where "cButton \<equiv> Abs_cs (CH ''cButton'' TTLive (range COLOR))"

lemma exc_in_cases: "P cButton \<Longrightarrow> P c"
  apply (induct_tac c)
  by (auto simp add: cButton_def)

lemma exc_in_rep_range: shows "(CH ''cButton'' TTLive (range COLOR)) \<in> range Rep_cs"
  apply auto
  using Rep_cs by auto[1]

instance cs::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_cs
        typedef_finite_UNIV by fastforce

instantiation cs::chan
begin
  definition Rep_cs_def: "Rep = Rep_cs"
  definition Abs_cs_def:"Abs = Abs_cs"
  definition ChanDom_cs_def: "chanDom(a::cs myself) = {(CH ''cButton'' TTLive (range COLOR))}"

  lemma rep_in_range[simp]: "range (Rep::cs \<Rightarrow> channel) = {(CH ''cButton'' TTLive (range COLOR))}"
    apply(subst Rep_cs_def)
    using type_definition.Rep_range type_definition_cs by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_cs_def Rep_cs_def Rep_cs_inverse)
     apply(simp add:ChanDom_cs_def insert_Diff_if)
     apply (simp add: cEmpty_def)
     using ctype_empty_iff apply auto[1]
     by (simp add: cEmpty_def)
     
end

instance cs::echan
  apply(intro_classes)
  apply(cases rule: exc_in_cases)
  by(auto simp add: cButton_def Rep_cs_def Abs_cs_inverse)


hide_type (open) cs

end
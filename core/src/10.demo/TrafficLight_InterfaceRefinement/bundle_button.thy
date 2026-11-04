theory bundle_button

imports bundlelocale.SBGen

begin

default_sort countable

typedef cs1 = "{(CH ''cButton'' TTLive {BUTTON Pressed})}" 
  by auto

definition cButton :: cs1 where "cButton \<equiv> Abs_cs1 (CH ''cButton'' TTLive {BUTTON Pressed})"

lemma exc_in_cases: "P cButton \<Longrightarrow> P c"
  apply (induct_tac c)
  by (auto simp add: cButton_def)

lemma exc_in_rep_range: shows "(CH ''cButton'' TTLive {BUTTON Pressed}) \<in> range Rep_cs1"
  apply auto
  using Rep_cs1 by auto[1]

instance cs1::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_cs1
        typedef_finite_UNIV by fastforce

instantiation cs1::chan
begin
  definition Rep_cs1_def: "Rep = Rep_cs1"
  definition Abs_cs1_def:"Abs = Abs_cs1"
  definition ChanDom_cs1_def: "chanDom(a::cs1 myself) = {(CH ''cButton'' TTLive {BUTTON Pressed})}"

  lemma rep_in_range[simp]: "range (Rep::cs1 \<Rightarrow> channel) = {(CH ''cButton'' TTLive {BUTTON Pressed})}"
    apply(subst Rep_cs1_def)
    using type_definition.Rep_range type_definition_cs1 by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_cs1_def Rep_cs1_def Rep_cs1_inverse)
     apply(simp add:ChanDom_cs1_def insert_Diff_if)
     apply (simp add: cEmpty_def)
     using ctype_empty_iff apply auto[1]
     by (simp add: cEmpty_def)
     
end

instance cs1::echan
  apply(intro_classes)
  apply(cases rule: exc_in_cases)
  by(auto simp add: cButton_def Rep_cs1_def Abs_cs1_inverse)


end
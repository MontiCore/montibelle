theory bundle_empty

imports bundlelocale.SBGen

begin

default_sort countable

typedef cs0 = "{(CH '''' TTLive {})}" 
  by auto

instance cs0::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_cs0
        typedef_finite_UNIV by fastforce

instantiation cs0::emptychan
begin
  definition Rep_cs0_def: "Rep = Rep_cs0"
  definition Abs_cs0_def:"Abs = Abs_cs0"
  definition ChanDom_cs0_def: "chanDom(a::cs0 myself) = {}"

  lemma rep_in_range[simp]: "range (Rep::cs0 \<Rightarrow> channel) = {(CH '''' TTLive {})}"
    apply(subst Rep_cs0_def)
    using type_definition.Rep_range type_definition_cs0 by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_cs0_def Rep_cs0_def Rep_cs0_inverse)
     apply(simp add:ChanDom_cs0_def )
     apply (simp add: cEmpty_def)
    apply(simp add: ctype_def)
     using ctype_empty_iff apply auto[1]
     by (simp add: cEmpty_def)
     
end


end
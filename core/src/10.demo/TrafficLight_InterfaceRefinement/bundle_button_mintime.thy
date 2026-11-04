theory bundle_button_mintime

imports bundlelocale.SBGen

begin
default_sort countable

typedef cs3 = "{(CH ''cButton'' TTLive {BUTTON Pressed}),
                (CH ''cMinTime'' TTLive (range NAT)) ::channel}" 
  by auto

definition cButtonIn :: cs3 where "cButtonIn \<equiv> Abs_cs3 (CH ''cButton'' TTLive {BUTTON Pressed})"
definition cMinTimeIn :: cs3 where "cMinTimeIn \<equiv> Abs_cs3 (CH ''cMinTime'' TTLive (range NAT))"

lemma exc_in_inj: "cButtonIn \<noteq> cMinTimeIn"
  by (simp add: cButtonIn_def cMinTimeIn_def Abs_cs3_inject)

lemma exc_in_comp: "\<forall>c :: cs3. c \<noteq> cButtonIn \<longrightarrow> c =cMinTimeIn"
  apply (simp add: cButtonIn_def, simp add: cMinTimeIn_def)
  using Abs_cs3_cases by auto

lemma exc_in_cases: "\<lbrakk>P cButtonIn; P cMinTimeIn\<rbrakk> \<Longrightarrow> P c"
  apply (induct_tac c)
  by (auto simp add: cButtonIn_def cMinTimeIn_def)

lemma exc_in_rep_range: shows "(CH ''cButton'' TTLive {BUTTON Pressed}) \<in> range Rep_cs3"
and "(CH ''cMinTime'' TTLive (range NAT)) \<in> range Rep_cs3"
  apply auto
  using Rep_cs3 apply auto[1]
  using type_definition.Rep_range type_definition_cs3 by fastforce+

lemma silly_in: "Rep_cs3 xb \<in> (\<lambda>x::cs3. Rep_cs3 xb) ` {x::cs3. x \<noteq> cButtonIn}"
  apply (simp add: image_def)
  apply (rule exI [where x="cMinTimeIn"])
  using exc_in_inj by auto

instance cs3::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_cs3
        typedef_finite_UNIV by fastforce

instantiation cs3::chan
begin
  definition Rep_cs3_def: "Rep = Rep_cs3"
  definition Abs_cs3_def:"Abs = Abs_cs3"
  definition ChanDom_cs3_def: "chanDom(a::cs3 myself) = {(CH ''cButton'' TTLive {BUTTON Pressed}),(CH ''cMinTime'' TTLive (range NAT)) ::channel}"

  lemma rep_in_range[simp]: "range (Rep::cs3 \<Rightarrow> channel) = {(CH ''cButton'' TTLive {BUTTON Pressed}),(CH ''cMinTime'' TTLive (range NAT)) ::channel}"
    apply(subst Rep_cs3_def)
    using type_definition.Rep_range type_definition_cs3 by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_cs3_def Rep_cs3_def Rep_cs3_inverse)
     apply(simp add:ChanDom_cs3_def insert_Diff_if)
     apply (simp add: cEmpty_def)
     using ctype_empty_iff apply auto[1]
    apply (simp add: cEmpty_def)
     using ctype_empty_iff  by auto[1]
end

instance cs3::echan
  apply(intro_classes)
  apply(cases rule: exc_in_cases)
  by(auto simp add: cButtonIn_def cMinTimeIn_def Rep_cs3_def Abs_cs3_inverse)

end

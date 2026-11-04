theory WrappedSPSCompConvert

imports WrappedSPSComp

begin

locale wrappedSPSConvert = wrappedSPS f_in f_out
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut" +
  fixes in_type:: "'ConvIn:: chan itself"
    and out_type:: "'ConvOut:: chan itself"
assumes f_in_req1: "\<And>c. \<not>chDomEmpty TYPE('ConvOut) \<Longrightarrow> Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep c \<in> chDom TYPE('ConvIn) \<Longrightarrow> Rep (f_in c) = Rep c"
    and f_in_req2: "\<And>c. \<not>chDomEmpty TYPE('ConvOut) \<Longrightarrow> Rep c \<in> chDom TYPE('fIn) \<Longrightarrow> Rep (f_in c) \<in> chDom TYPE('ConvIn) \<longrightarrow> Rep c \<in> chDom TYPE('ConvIn)"
    and f_out_req1: "\<And>c. \<not>chDomEmpty TYPE('fOut) \<Longrightarrow> Rep c \<in> chDom TYPE('ConvOut) \<Longrightarrow> Rep (f_out c) = Rep c"
    and f_out_req2: "chDom TYPE('ConvOut) \<inter> chDom TYPE('fOut) \<subseteq> chDom TYPE('fWrappedOut)"
begin

named_theorems named_sps_convert_eq

lemma sps_convert_eq[named_sps_convert_eq] : "spsConvert\<cdot>({sbRenameCh f_in} \<then> F \<then> {sbRenameCh f_out}) = (spsConvert\<cdot>F::(('ConvIn\<^sup>\<Omega> \<rightarrow> 'ConvOut\<^sup>\<Omega>) set))"
  apply(rule wrapped_sps_convert_eq)
  using rename_in.ctype_f apply blast
  using f_in_req1 apply blast
  using f_in_req2 apply blast
  using rename_out.ctype_f apply blast
  using f_out_req1 apply blast
  using f_out_req2 chdom_in by blast

end

locale wrappedSPSCompConvert = constraint1: wrappedSPSConvert f_in f_out in_type out_type + 
                               constraint2: wrappedSPSConvert g_in g_out in_type out_type +
                               wrappedSPSComp f_in f_out g_in g_out
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and g_in::"'gIn \<Rightarrow> 'gWrappedIn"
    and g_out::"'gWrappedOut \<Rightarrow> 'gOut"
    and in_type:: "'ConvIn:: chan itself"
    and out_type:: "'ConvOut:: chan itself"
begin 

lemma comp_f_in_req1: "\<And>c::('fIn \<union> 'gIn) - 'fOut \<union> 'gOut. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> \<not>chDomEmpty TYPE('ConvOut) \<longrightarrow> Rep c \<in> chDom TYPE('ConvIn) \<longrightarrow> Rep (comp_in c) = Rep c"
  apply(rule comp_in_property)
  using constraint1.f_in_req1 minus_notempty apply blast
  using constraint2.f_in_req1 minus_notempty apply blast
  by simp

lemma comp_f_in_req2: "\<And>c::('fIn \<union> 'gIn) - 'fOut \<union> 'gOut. \<not>chDomEmpty TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<Longrightarrow> \<not>chDomEmpty TYPE('ConvOut) \<longrightarrow> Rep c \<notin> chDom TYPE('ConvIn) \<longrightarrow> Rep (comp_in c) \<notin> chDom TYPE('ConvIn)"
  apply(rule comp_in_property)
  using constraint1.f_in_req2 minus_notempty apply blast
  using constraint2.f_in_req2 minus_notempty apply blast
  by simp

lemma comp_f_out_req1: "\<And>c::'fWrappedOut \<union> 'gWrappedOut. \<not>chDomEmpty TYPE('fOut \<union> 'gOut) \<longrightarrow> Rep c \<in> chDom TYPE('ConvOut) \<longrightarrow> Rep (comp_out c) = Rep c"
  apply(rule impI, subgoal_tac "\<not>chDomEmpty TYPE('fWrappedOut \<union> 'gWrappedOut)")
  apply(rule comp_out_property)
  using constraint1.f_out_req1 constraint1.rename_out.empty_eq apply presburger
  using constraint2.f_out_req1 constraint2.rename_out.empty_eq apply blast
  using comp_out_empty_eq by auto

lemma comp_f_out_req2: "chDom TYPE('ConvOut) \<inter> chDom TYPE('fOut \<union> 'gOut) \<subseteq> chDom TYPE('fWrappedOut \<union> 'gWrappedOut)"
  using constraint1.f_out_req2 constraint2.f_out_req2 by auto

end

sublocale wrappedSPSCompConvert \<subseteq> wrappedSPSConvert comp_in comp_out
  apply(standard)
  using comp_f_in_req1 apply fastforce
  using comp_f_in_req2 apply fastforce
  using comp_f_out_req1 apply fastforce
  using comp_f_out_req2 by fastforce

locale wrappedSPSCompNoOverlapConvert = constraint1: wrappedSPSConvert f_in f_out in_type out_type + 
                                        constraint2: wrappedSPSConvert g_in g_out in_type out_type + 
                                        wrappedSPSCompNoOverlap f_in f_out g_in g_out
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and g_in::"'gIn \<Rightarrow> 'gWrappedIn"
    and g_out::"'gWrappedOut \<Rightarrow> 'gOut"
    and in_type:: "'ConvIn:: chan itself"
    and out_type:: "'ConvOut:: chan itself"
begin end

sublocale wrappedSPSCompNoOverlapConvert \<subseteq> wrappedSPSCompConvert f_in f_out g_in g_out in_type out_type
  by(standard)

locale wrappedSPSCompParallelConvert = constraint1: wrappedSPSConvert f_in f_out in_type out_type + 
                                       constraint2: wrappedSPSConvert g_in g_out in_type out_type +
                                       wrappedSPSCompParallel f_in f_out g_in g_out
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and g_in::"'gIn \<Rightarrow> 'gWrappedIn"
    and g_out::"'gWrappedOut \<Rightarrow> 'gOut"
    and in_type:: "'ConvIn:: chan itself"
    and out_type:: "'ConvOut:: chan itself"
begin end

sublocale wrappedSPSCompParallelConvert \<subseteq> wrappedSPSCompNoOverlapConvert f_in f_out g_in g_out in_type out_type
  by(standard)

end

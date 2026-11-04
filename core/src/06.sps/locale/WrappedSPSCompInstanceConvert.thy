theory WrappedSPSCompInstanceConvert

imports WrappedSPSComp

begin

locale wrappedSPSInstance = wrappedSPS f_in f_out +
                            instance_rename_in: renameWell i_in +
                            instance_rename_out: renameWell i_out
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and i_in:: "'iIn \<Rightarrow> 'iWrappedIn"
    and i_out:: "'iWrappedOut \<Rightarrow> 'iOut" +
assumes i_out_req1: "\<And> c. Rep c \<in> chDom TYPE('iWrappedOut) \<longrightarrow> Rep c \<in> chDom TYPE('fWrappedOut) \<longrightarrow> Rep (f_out (Abs (Rep c))) = Rep (i_out c)"
    and i_out_req2: "\<And> c. Rep c \<in> chDom TYPE('iWrappedOut) \<longrightarrow> Rep c \<notin> chDom TYPE('fWrappedOut) \<longrightarrow> Rep (i_out c) \<notin> chDom TYPE('fOut)"
    and i_in_req1: "\<And> c. Rep c \<in> chDom TYPE('fIn) \<longrightarrow> Rep c \<in> chDom TYPE('iIn) \<longrightarrow> Rep (i_in (Abs (Rep c))) = Rep (f_in c)"
    and i_in_req2: "\<And> c. Rep c \<in> chDom TYPE('fIn) \<longrightarrow> Rep c \<notin> chDom TYPE('iIn) \<longrightarrow> Rep (f_in c) \<notin> chDom TYPE('iWrappedIn)"
begin

named_theorems named_sbrenamech_spsconv_swap

lemma sbrenamech_spsconv_swap[named_sbrenamech_spsconv_swap]:  "{sbRenameCh i_in} \<then> spsConvert\<cdot>F \<then> {sbRenameCh i_out} = spsConvert\<cdot>({sbRenameCh f_in} \<then> F \<then> {sbRenameCh f_out})"
  apply(rule sbrenamech_spsconv_swap[OF _ _ _ _  i_out_req1 i_out_req2 i_in_req1 i_in_req2])
  by(auto simp add: rename_in.ctype_f rename_out.ctype_f instance_rename_in.ctype_f instance_rename_out.ctype_f)

end

locale wrappedSPSCompInstance = wrappedSPSComp f_in f_out g_in g_out + 
                                constraint1: wrappedSPSInstance f_in f_out i_in i_out  + 
                                constraint2: wrappedSPSInstance g_in g_out i_in i_out 
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and g_in::"'gIn \<Rightarrow> 'gWrappedIn"
    and g_out::"'gWrappedOut \<Rightarrow> 'gOut"
    and i_in:: "'iIn \<Rightarrow> 'iWrappedIn"
    and i_out:: "'iWrappedOut \<Rightarrow> 'iOut"
begin 

lemma comp_i_in_req1: "\<And>c. Rep c \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<longrightarrow> Rep c \<in> chDom TYPE('iIn) \<longrightarrow> Rep (i_in (Abs (Rep c))) = Rep (comp_in c)"
  apply(rule impI)
  apply(rule comp_in_property)
  using constraint1.i_in_req1 minus_notempty apply blast
  using constraint2.i_in_req1 minus_notempty apply blast
  by blast

lemma comp_i_in_req2: "\<And>c. Rep c \<in> chDom TYPE(('fIn \<union> 'gIn) - 'fOut \<union> 'gOut) \<longrightarrow> Rep c \<notin> chDom TYPE('iIn) \<longrightarrow> Rep (comp_in c) \<notin> chDom TYPE('iWrappedIn)"
  apply(rule impI)
  apply(rule comp_in_property)
  using constraint1.i_in_req2 minus_notempty apply blast
  using constraint2.i_in_req2 minus_notempty apply blast
  by blast

lemma comp_i_out_req1: "\<And>c. Rep c \<in> chDom TYPE('iWrappedOut) \<longrightarrow> Rep c \<in> chDom TYPE('fWrappedOut \<union> 'gWrappedOut) \<longrightarrow> Rep (comp_out (Abs (Rep c))) = Rep (i_out c)"
  apply(rule impI, rule impI, subgoal_tac "\<not>chDomEmpty TYPE('fWrappedOut \<union> 'gWrappedOut)")
  apply(case_tac "Rep c \<in> chDom TYPE('fWrappedOut)"; simp)
  apply(subst constraint1.i_out_req1, simp, simp)
  apply(rule rep_reduction)
  apply(metis empty_iff Un_iff chdom_in chdom_union constraint1.i_out_req1 F.rename_out.empty_eq)
  apply(subst constraint2.i_out_req1, simp, simp)
  apply(rule rep_reduction)
  apply(metis empty_iff Un_iff chdom_in chdom_union constraint2.i_out_req1 G.rename_out.empty_eq)
  by auto

lemma comp_i_out_req2: "\<And>c. Rep c \<in> chDom TYPE('iWrappedOut) \<longrightarrow> Rep c \<notin> chDom TYPE('fWrappedOut \<union> 'gWrappedOut) \<longrightarrow> Rep (i_out c) \<notin> chDom TYPE('fOut \<union> 'gOut)"
  using constraint1.i_out_req2 constraint2.i_out_req2 by auto

end

sublocale wrappedSPSCompInstance \<subseteq> wrappedSPSInstance comp_in comp_out
  apply(standard)
  apply(rule comp_i_out_req1)
  apply(rule comp_i_out_req2)
  apply(rule comp_i_in_req1)
  by(rule comp_i_in_req2)

locale wrappedSPSCompNoOverlapInstance = wrappedSPSCompNoOverlap f_in f_out g_in g_out + 
                                         constraint1: wrappedSPSInstance f_in f_out i_in i_out  + 
                                         constraint2: wrappedSPSInstance g_in g_out i_in i_out 
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and g_in::"'gIn \<Rightarrow> 'gWrappedIn"
    and g_out::"'gWrappedOut \<Rightarrow> 'gOut"
    and i_in:: "'iIn \<Rightarrow> 'iWrappedIn"
    and i_out:: "'iWrappedOut \<Rightarrow> 'iOut"
begin end

sublocale wrappedSPSCompNoOverlapInstance \<subseteq> wrappedSPSCompInstance f_in f_out g_in g_out
  by(standard)

locale wrappedSPSCompParallelInstance = wrappedSPSCompParallel f_in f_out g_in g_out + 
                                        constraint1: wrappedSPSInstance f_in f_out i_in i_out  + 
                                        constraint2: wrappedSPSInstance g_in g_out i_in i_out 
    for f_in::"'fIn \<Rightarrow> 'fWrappedIn"
    and f_out::"'fWrappedOut \<Rightarrow> 'fOut"
    and g_in::"'gIn \<Rightarrow> 'gWrappedIn"
    and g_out::"'gWrappedOut \<Rightarrow> 'gOut"
    and i_in:: "'iIn \<Rightarrow> 'iWrappedIn"
    and i_out:: "'iWrappedOut \<Rightarrow> 'iOut"
begin end

sublocale wrappedSPSCompParallelInstance \<subseteq> wrappedSPSCompNoOverlapInstance f_in f_out g_in g_out
  by(standard)

end

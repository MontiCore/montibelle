theory LtlBundle

imports stream.StreamLtl bundlelocale.SBGen

begin
default_sort countable



definition natSet :: "msg set"
  where "natSet = range NAT"

typedef ExCIn = "{(CH ''c1'' TUntimed natSet),(CH ''c2'' TUntimed natSet) ::channel}" 
  by auto

definition c1In :: ExCIn where "c1In \<equiv> Abs_ExCIn (CH ''c1'' TUntimed natSet)"
definition c2In :: ExCIn where "c2In \<equiv> Abs_ExCIn (CH ''c2'' TUntimed natSet)"

lemma exc_in_inj: "c1In \<noteq> c2In"
  by (simp add: c1In_def c2In_def Abs_ExCIn_inject)

lemma exc_in_comp: "\<forall>c :: ExCIn. c \<noteq> c1In \<longrightarrow> c =c2In"
  apply (simp add: c1In_def, simp add: c2In_def)
  using Abs_ExCIn_cases by auto

lemma exc_in_cases: "\<lbrakk>P c1In; P c2In\<rbrakk> \<Longrightarrow> P c"
  apply (induct_tac c)
  by (auto simp add: c1In_def c2In_def)

lemma exc_in_rep_range: shows "(CH ''c1'' TUntimed natSet) \<in> range Rep_ExCIn"
and "(CH ''c2'' TUntimed natSet) \<in> range Rep_ExCIn"
  apply auto
  using Rep_ExCIn apply auto[1]
  using type_definition.Rep_range type_definition_ExCIn by fastforce+

lemma silly_in: "Rep_ExCIn xb \<in> (\<lambda>x::ExCIn. Rep_ExCIn xb) ` {x::ExCIn. x \<noteq> c1In}"
  apply (simp add: image_def)
  apply (rule exI [where x="c2In"])
  using exc_in_inj by auto

lemma natSet_nempty: "\<forall>x. natSet \<noteq> {}"
  by (simp add: natSet_def)

instance ExCIn::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_ExCIn
        typedef_finite_UNIV by fastforce

instantiation ExCIn::chan
begin
  definition Rep_ExCIn_def: "Rep = Rep_ExCIn"
  definition Abs_ExCIn_def:"Abs = Abs_ExCIn"
  definition ChanDom_ExCIn_def: "chanDom(a::ExCIn myself) = {(CH ''c1'' TUntimed natSet),(CH ''c2'' TUntimed natSet) ::channel}"

  lemma rep_in_range[simp]: "range (Rep::ExCIn \<Rightarrow> channel) = {(CH ''c1'' TUntimed natSet),(CH ''c2'' TUntimed natSet) ::channel}"
    apply(subst Rep_ExCIn_def)
    using type_definition.Rep_range type_definition_ExCIn by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_ExCIn_def Rep_ExCIn_def Rep_ExCIn_inverse)
     apply(simp add:ChanDom_ExCIn_def insert_Diff_if)
     apply (simp add: cEmpty_def natSet_def)
     using ctype_empty_iff apply auto[1]
    apply (simp add: cEmpty_def)
     using ctype_empty_iff  by auto[1]
end



definition boolSet :: "msg set"
  where "boolSet = range BOOL"

typedef ExCOut = "{(CH ''c1'' TUntimed boolSet),(CH ''c2'' TUntimed boolSet) ::channel}" 
  by auto

definition c1Out :: ExCOut where "c1Out \<equiv> Abs_ExCOut (CH ''c1'' TUntimed boolSet)"
definition c2Out :: ExCOut where "c2Out \<equiv> Abs_ExCOut (CH ''c2'' TUntimed boolSet)"

lemma exc_out_inj: "c1Out \<noteq> c2Out"
  by (simp add: c1Out_def c2Out_def Abs_ExCOut_inject)

lemma exc_out_comp: "\<forall>c :: ExCOut. c \<noteq> c1Out \<longrightarrow> c =c2Out"
  apply (simp add: c1Out_def, simp add: c2Out_def)
  using Abs_ExCOut_cases by auto

lemma exc_out_cases: "\<lbrakk>P c1Out; P c2Out\<rbrakk> \<Longrightarrow> P c"
  apply (induct_tac c)
  by (auto simp add: c1Out_def c2Out_def)

lemma exc_out_rep_range: shows "(CH ''c1'' TUntimed boolSet) \<in> range Rep_ExCOut"
and "(CH ''c2'' TUntimed boolSet) \<in> range Rep_ExCOut"
  apply auto
  using Rep_ExCOut apply auto[1]
  using type_definition.Rep_range type_definition_ExCOut by fastforce+

lemma silly_out: "Rep_ExCOut xb \<in> (\<lambda>x::ExCOut. Rep_ExCOut xb) ` {x::ExCOut. x \<noteq> c1Out}"
  apply (simp add: image_def)
  apply (rule exI [where x="c2Out"])
  using exc_out_inj by auto

lemma boolSet_nempty: "\<forall>x. boolSet \<noteq> {}"
  by (simp add: boolSet_def)

instance ExCOut::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_ExCOut
        typedef_finite_UNIV by fastforce

instantiation ExCOut::chan
begin
  definition Rep_ExCOut_def: "Rep = Rep_ExCOut"
  definition Abs_ExCOut_def: "Abs = Abs_ExCOut"
  definition ChanDom_ExCOut_def: "chanDom(a::ExCOut myself) = {(CH ''c1'' TUntimed boolSet),(CH ''c2'' TUntimed boolSet) ::channel}"

  lemma rep_out_range[simp]: "range (Rep::ExCOut \<Rightarrow> channel) = {(CH ''c1'' TUntimed boolSet),(CH ''c2'' TUntimed boolSet) ::channel}"
    apply(subst Rep_ExCOut_def)
    using type_definition.Rep_range type_definition_ExCOut by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_ExCOut_def Rep_ExCOut_def Rep_ExCOut_inverse)
     apply(simp add:ChanDom_ExCOut_def insert_Diff_if)
     apply (simp add: cEmpty_def boolSet_def)
     using ctype_empty_iff apply auto[1]
    apply (simp add: cEmpty_def)
     using ctype_empty_iff  by auto[1]
end



definition constrExCIn :: "(nat stream) \<times> (nat stream) \<Rightarrow> ExCIn \<Rightarrow> M stream"
  where "constrExCIn t c = (if c = c1In
                         then smap (\<lambda>x. Untimed (NAT x))\<cdot>(fst t)
                         else smap (\<lambda>x. Untimed (NAT x))\<cdot>(snd t))"

lemma COIN_in: "smap (\<lambda>x. Untimed (NAT x))\<cdot>a = smap (\<lambda>x. Untimed (NAT x))\<cdot>b \<Longrightarrow> a = b"
  by (meson M.inject(1) msg.inject(1) smapnoteq)

lemma constr_in_inj: "inj constrExCIn"
  apply (simp add: inj_on_def constrExCIn_def)
  using exc_in_inj COIN_in apply auto
  apply (metis constrExCIn_def fst_conv)
  by (metis (mono_tags) constrExCIn_def snd_conv)

lemma CSBW3_in: shows "Rep c1In = (CH ''c1'' TUntimed natSet)" and "Rep c2In = (CH ''c2'' TUntimed natSet)"
   apply (simp_all add: c1In_def c2In_def)
  by (simp_all add: Abs_ExCIn_inverse Rep_ExCIn_def)

lemma CSBW2_in: shows "ctype (Rep c1In) = Untimed ` natSet" and "ctype (Rep c2In) = Untimed ` natSet"
   using CSBW3_in apply auto
   using Rep_ExCIn_def Rep_ExCIn_inverse exc_in_inj apply auto
      apply (simp_all add: ctype_def)
   using natSet_nempty by auto

lemma CSBW0_in: "\<forall>c :: ExCIn. ctype (Rep c) = Untimed ` natSet"
  using exc_in_cases [of "\<lambda>c. ctype (Rep c) = Untimed ` natSet"] CSBW2_in  by auto

lemma CSBW1_in: "\<forall>c :: ExCIn. sValues\<cdot>(smap (\<lambda>x::nat. Untimed (NAT x))\<cdot>a) \<subseteq> ctype (Rep c)"
  using CSBW0_in apply auto
  apply (simp add: natSet_def)
  by (metis (no_types, lifting) image_iff rangeI smap_sValues)

lemma constr_in_sb_well: shows "lsb_well (constrExCIn (a:: nat stream, b :: nat stream))"
  apply (simp add: lsb_well_def constrExCIn_def)
  using CSBW1_in by auto

lemma SURJ0_in: "lsb_well f \<Longrightarrow> \<forall>c :: ExCIn. sValues\<cdot>(f c) \<subseteq> Untimed ` natSet"
  apply (simp add: natSet_def lsb_well_def, auto)
  by (metis CSBW0_in subset_iff natSet_def)

lemma SURJ1_1_in: "sValues\<cdot>(f c) \<subseteq> Untimed ` natSet \<Longrightarrow> (\<forall>i. Fin i < #(f c) \<longrightarrow> (\<exists>a. (Untimed (NAT a) = snth i (f c))))"
  by (simp add: sValues_def2 natSet_def, auto)

lemma SURJ1_0_in: "sValues\<cdot>(f c) \<subseteq> Untimed ` natSet \<Longrightarrow> \<exists>a. (#a = #(f c)) \<and> (\<forall>i. Fin i < #(f c) \<longrightarrow> (Untimed (NAT (snth i a)) = snth i (f c)))"
  using SURJ1_1_in [of f c] apply auto
  apply (simp add: sValues_def2 natSet_def)
  apply (rule exI [where x="(smap (inv (\<lambda>x. Untimed (NAT x)))\<cdot>(f c))"])
  apply auto
  by (metis f_inv_into_f rangeI smap_snth_lemma)

lemma SURJ1_in: "\<forall>c. sValues\<cdot>(f c) \<subseteq> Untimed ` natSet \<Longrightarrow> \<forall>c. \<exists>a. (#a = #(f c)) \<and> (\<forall>i. Fin i < #(f c) \<longrightarrow> (Untimed (NAT (snth i a)) = snth i (f c)))"
  using SURJ1_0_in by metis

lemma SURJ2_1_in: "(#a = #(f c)) \<and> (\<forall>i. Fin i < #(f c) \<longrightarrow> (Untimed (NAT (snth i a)) = snth i (f c))) \<Longrightarrow> (c=c1In \<longrightarrow> (\<exists>b. constrExCIn (a, b) c1In = f c1In)) \<and> (c=c2In \<longrightarrow> (\<exists>b. constrExCIn (b, a) c2In = f c2In))"
  using exc_in_inj exc_in_comp apply auto
  by (simp_all add: constrExCIn_def smap_snth_lemma snths_eq)

lemma constr_in_split: "(\<exists>b. constrExCIn (a, b) c1In = f c1In) \<and> (\<exists>a. constrExCIn (a, b) c2In = f c2In) \<Longrightarrow> \<exists>a b. constrExCIn (a, b) = f"
  apply (rule exI [where x=a], rule exI [where x=b])
  apply (subgoal_tac "\<forall>c. constrExCIn (a, b) c = f c")
  apply auto[1]
  apply (simp add: constrExCIn_def)
  using exc_in_inj exc_in_comp by auto

lemma SURJ2_in: "(\<And>c. \<exists>a. (#a = #(f c)) \<and> (\<forall>i. Fin i < #(f c) \<longrightarrow> (Untimed (NAT (snth i a)) = snth i (f c)))) \<Longrightarrow> \<exists>a b. constrExCIn (a, b) = f"
  by (metis SURJ2_1_in[of _ f c1In] SURJ2_1_in[of _ f c2In] constr_in_split)

lemma constr_in_surj: "\<And>f::ExCIn \<Rightarrow> M stream. lsb_well f \<Longrightarrow> \<exists>F. constrExCIn F = f"
  by (metis SURJ0_in SURJ1_in SURJ2_in)

lemma constr_in_lenex: "\<exists>c :: ExCIn. #(a, b) = #(constrExCIn (a, b) c)"
  by (simp add: len_prod_def constrExCIn_def, metis (full_types) exc_in_inj min_def)

lemma constr_in_nbelow_aux: "\<And>x y. (\<forall>c :: ExCIn. (constrExCIn x c \<sqsubseteq> constrExCIn y c)) \<Longrightarrow> (x \<sqsubseteq> y)"
  apply (simp add: below_prod_def)
  apply (subgoal_tac "constrExCIn x c1In \<sqsubseteq> constrExCIn y c1In \<Longrightarrow> fst x \<sqsubseteq> fst y")
   apply (subgoal_tac "constrExCIn x c2In \<sqsubseteq> constrExCIn y c2In \<Longrightarrow> snd x \<sqsubseteq> snd y")
  apply blast
   apply (simp_all add: constrExCIn_def)
  apply (drule spec [where x="c2In"])
  using exc_in_inj apply auto[1]
  by (meson M.inject(1) msg.inject(1) smapnotbelow)+


lemma constr_in_nbelow: "\<And>x y. \<not>(x \<sqsubseteq> y) \<Longrightarrow> 
                             \<not>(constrExCIn x \<sqsubseteq> constrExCIn y)"
  apply (simp add: below_fun_def, auto)
  using constr_in_nbelow_aux constrExCIn_def
  apply auto
  by (metis M.inject(1) msg.inject(1) exc_in_inj smapnotbelow)

 
interpretation exc_in_SB: sbGen constrExCIn
  apply (simp add: sbGen_def, auto)
  using constr_in_sb_well apply auto[1]
  using constr_in_inj apply simp
  using constr_in_surj apply auto[1]
      apply (simp add: constrExCIn_def)
  using constr_in_nbelow apply auto[1]
  using constr_in_nbelow apply auto[1]
   apply (simp add: constrExCIn_def)
   apply (metis (mono_tags, lifting) fstI len_prod_minl len_prod_minr slen_smap sndI)
  using constr_in_lenex by auto[1]



definition constrExCOut :: "(bool stream) \<times> (bool stream) \<Rightarrow> ExCOut \<Rightarrow> M stream"
  where "constrExCOut t c = (if c = c1Out
                         then smap (\<lambda>x. Untimed (BOOL x))\<cdot>(fst t)
                         else smap (\<lambda>x. Untimed (BOOL x))\<cdot>(snd t))"

lemma COIN_out: "smap (\<lambda>x. Untimed (BOOL x))\<cdot>a = smap (\<lambda>x. Untimed (BOOL x))\<cdot>b \<Longrightarrow> a = b"
proof -
  assume a1: "smap (\<lambda>x. Untimed (BOOL x))\<cdot>a = smap (\<lambda>x. Untimed (BOOL x))\<cdot>b"
  have f2: "True \<noteq> False"
    by auto
  have "\<forall>f s sa. (f False::M) \<noteq> f True \<and> s \<noteq> sa \<longrightarrow> smap f\<cdot>s \<noteq> smap f\<cdot>sa"
    by (metis (full_types) smapnoteq)
  then show ?thesis
    using f2 a1 by fastforce
qed

lemma constr_out_inj: "inj constrExCOut"
  apply (simp add: inj_on_def constrExCOut_def)
  using exc_out_inj COIN_out apply auto
  apply (metis constrExCOut_def fst_conv)
  by (metis (mono_tags) constrExCOut_def snd_conv)

lemma CSBW3_out: shows "Rep c1Out = (CH ''c1'' TUntimed boolSet)" and "Rep c2Out = (CH ''c2'' TUntimed boolSet)"
   apply (simp_all add: c1Out_def c2Out_def)
  by (simp_all add: Abs_ExCOut_inverse Rep_ExCOut_def)

lemma CSBW2_out: shows "ctype (Rep c1Out) = Untimed ` boolSet" and "ctype (Rep c2Out) = Untimed ` boolSet"
   using CSBW3_out apply auto
   using Rep_ExCOut_def Rep_ExCOut_inverse exc_out_inj apply auto
      apply (simp_all add: ctype_def)
   using boolSet_nempty by auto

lemma CSBW0_out: "\<forall>c :: ExCOut. ctype (Rep c) = Untimed ` boolSet"
  using exc_out_cases [of "\<lambda>c. ctype (Rep c) = Untimed ` boolSet"] CSBW2_out  by auto

lemma CSBW1_out: "\<forall>c :: ExCOut. sValues\<cdot>(smap (\<lambda>x::bool. Untimed (BOOL x))\<cdot>a) \<subseteq> ctype (Rep c)"
  using CSBW0_out apply auto
  apply (simp add: boolSet_def)
  by (metis (no_types, lifting) image_iff rangeI smap_sValues)

lemma constr_out_sb_well: shows "lsb_well (constrExCOut (a:: bool stream, b :: bool stream))"
  apply (simp add: lsb_well_def constrExCOut_def)
  using CSBW1_out by auto

lemma SURJ0_out: "lsb_well f \<Longrightarrow> \<forall>c :: ExCOut. sValues\<cdot>(f c) \<subseteq> Untimed ` boolSet"
  apply (simp add: boolSet_def lsb_well_def, auto)
  by (metis CSBW0_out subset_iff boolSet_def)

lemma SURJ1_1_out: "sValues\<cdot>(f c) \<subseteq> Untimed ` boolSet \<Longrightarrow> (\<forall>i. Fin i < #(f c) \<longrightarrow> (\<exists>a. (Untimed (BOOL a) = snth i (f c))))"
  by (simp add: sValues_def2 boolSet_def, auto)

lemma SURJ1_0_out: "sValues\<cdot>(f c) \<subseteq> Untimed ` boolSet \<Longrightarrow> \<exists>a. (#a = #(f c)) \<and> (\<forall>i. Fin i < #(f c) \<longrightarrow> (Untimed (BOOL (snth i a)) = snth i (f c)))"
  using SURJ1_1_out [of f c] apply auto
  apply (simp add: sValues_def2 boolSet_def)
  apply (rule exI [where x="(smap (inv (\<lambda>x. Untimed (BOOL x)))\<cdot>(f c))"])
  apply auto
  by (metis f_inv_into_f rangeI smap_snth_lemma)

lemma SURJ1_out: "\<forall>c. sValues\<cdot>(f c) \<subseteq> Untimed ` boolSet \<Longrightarrow> \<forall>c. \<exists>a. (#a = #(f c)) \<and> (\<forall>i. Fin i < #(f c) \<longrightarrow> (Untimed (BOOL (snth i a)) = snth i (f c)))"
  using SURJ1_0_out by metis

lemma SURJ2_1_out: "(#a = #(f c)) \<and> (\<forall>i. Fin i < #(f c) \<longrightarrow> (Untimed (BOOL (snth i a)) = snth i (f c))) \<Longrightarrow> (c=c1Out \<longrightarrow> (\<exists>b. constrExCOut (a, b) c1Out = f c1Out)) \<and> (c=c2Out \<longrightarrow> (\<exists>b. constrExCOut (b, a) c2Out = f c2Out))"
  using exc_out_inj exc_out_comp apply auto
  by (simp_all add: constrExCOut_def smap_snth_lemma snths_eq)

lemma constr_out_split: "(\<exists>b. constrExCOut (a, b) c1Out = f c1Out) \<and> (\<exists>a. constrExCOut (a, b) c2Out = f c2Out) \<Longrightarrow> \<exists>a b. constrExCOut (a, b) = f"
  apply (rule exI [where x=a], rule exI [where x=b])
  apply (subgoal_tac "\<forall>c. constrExCOut (a, b) c = f c")
  apply auto[1]
  apply (simp add: constrExCOut_def)
  using exc_out_inj exc_out_comp by auto

lemma SURJ2_out: "(\<And>c. \<exists>a. (#a = #(f c)) \<and> (\<forall>i. Fin i < #(f c) \<longrightarrow> (Untimed (BOOL (snth i a)) = snth i (f c)))) \<Longrightarrow> \<exists>a b. constrExCOut (a, b) = f"
  by (metis SURJ2_1_out[of _ f c1Out] SURJ2_1_out[of _ f c2Out] constr_out_split)

lemma constr_out_surj: "\<And>f::ExCOut \<Rightarrow> M stream. lsb_well f \<Longrightarrow> \<exists>F. constrExCOut F = f"
  by (metis SURJ0_out SURJ1_out SURJ2_out)

lemma constr_out_lenex: "\<exists>c :: ExCOut. #(a, b) = #(constrExCOut (a, b) c)"
  by (simp add: len_prod_def constrExCOut_def, metis (full_types) exc_out_inj min_def)

lemma constr_out_nbelow_aux: "\<And>x y. (\<forall>c :: ExCOut. (constrExCOut x c \<sqsubseteq> constrExCOut y c)) \<Longrightarrow> (x \<sqsubseteq> y)"
  apply (simp add: below_prod_def)
  apply (subgoal_tac "constrExCOut x c1Out \<sqsubseteq> constrExCOut y c1Out \<Longrightarrow> fst x \<sqsubseteq> fst y")
   apply (subgoal_tac "constrExCOut x c2Out \<sqsubseteq> constrExCOut y c2Out \<Longrightarrow> snd x \<sqsubseteq> snd y")
  apply blast
   apply (simp_all add: constrExCOut_def)
  apply (drule spec [where x="c2Out"])
  using exc_out_inj apply auto[1]
   defer
proof -
  fix x :: "bool stream \<times> bool stream" and y :: "bool stream \<times> bool stream"
  assume a1: "smap (\<lambda>x. Untimed (BOOL x))\<cdot>(fst x) \<sqsubseteq> smap (\<lambda>x. Untimed (BOOL x))\<cdot>(fst y)"
  have f2: "True \<noteq> False"
    by auto
  have "\<forall>f s sa. (f False::M) \<noteq> f True \<and> s \<notsqsubseteq> sa \<longrightarrow> smap f\<cdot>s \<notsqsubseteq> smap f\<cdot>sa"
    by (metis (full_types) smapnotbelow)
  then show "fst x \<sqsubseteq> fst y"
    using f2 a1 by fastforce
next
  fix a :: "bool stream" and b :: "bool stream" and aa :: "bool stream" and ba :: "bool stream"
  assume a1: "smap (\<lambda>x. Untimed (BOOL x))\<cdot>b \<sqsubseteq> smap (\<lambda>x. Untimed (BOOL x))\<cdot>ba"
  have "BOOL False \<noteq> BOOL True"
    by blast
  then show "b \<sqsubseteq> ba"
    using a1 by (metis (full_types) M.inject(1) smapnotbelow)
qed


lemma constr_out_nbelow: "\<And>x y. \<not>(x \<sqsubseteq> y) \<Longrightarrow> 
                             \<not>(constrExCOut x \<sqsubseteq> constrExCOut y)"
  apply (simp add: below_fun_def, auto)
  using constr_out_nbelow_aux constrExCOut_def
   apply auto
  using M.inject(1) msg.inject(2) exc_out_inj smapnotbelow apply auto
proof -
  fix a :: "bool stream" and b :: "bool stream" and aa :: "bool stream" and ba :: "bool stream"
  assume a1: "c1Out \<noteq> c2Out"
  assume a2: "b \<notsqsubseteq> ba"
  assume "\<And>a b aa ba. \<forall>c. (if c = c1Out then smap (\<lambda>x. Untimed (BOOL x))\<cdot>(fst (a, b)) else smap (\<lambda>x. Untimed (BOOL x))\<cdot> (snd (a, b))) \<sqsubseteq> (if c = c1Out then smap (\<lambda>x. Untimed (BOOL x))\<cdot>(fst (aa, ba)) else smap (\<lambda>x. Untimed (BOOL x))\<cdot> (snd (aa, ba))) \<Longrightarrow> a \<sqsubseteq> aa \<and> b \<sqsubseteq> ba"
  then have f3: "\<forall>s sa sb sc. (\<exists>e. (if e = c1Out then smap (\<lambda>b. Untimed (BOOL b))\<cdot>(fst (s, sa)) else smap (\<lambda>b. Untimed (BOOL b))\<cdot> (snd (s, sa))) \<notsqsubseteq> (if e = c1Out then smap (\<lambda>b. Untimed (BOOL b))\<cdot>(fst (sb, sc)) else smap (\<lambda>b. Untimed (BOOL b))\<cdot> (snd (sb, sc)))) \<or> s \<sqsubseteq> sb \<and> sa \<sqsubseteq> sc"
    by fastforce
  obtain ee :: "bool stream \<Rightarrow> bool stream \<Rightarrow> bool stream \<Rightarrow> bool stream \<Rightarrow> ExCOut" where
    "\<forall>x0 x1 x2 x3. (\<exists>v4. (if v4 = c1Out then smap (\<lambda>uu. Untimed (BOOL uu))\<cdot>(fst (x3, x2)) else smap (\<lambda>uu. Untimed (BOOL uu))\<cdot> (snd (x3, x2))) \<notsqsubseteq> (if v4 = c1Out then smap (\<lambda>uu. Untimed (BOOL uu))\<cdot>(fst (x1, x0)) else smap (\<lambda>uu. Untimed (BOOL uu))\<cdot>(snd (x1, x0)))) = ((if ee x0 x1 x2 x3 = c1Out then smap (\<lambda>uu. Untimed (BOOL uu))\<cdot>(fst (x3, x2)) else smap (\<lambda>uu. Untimed (BOOL uu))\<cdot> (snd (x3, x2))) \<notsqsubseteq> (if ee x0 x1 x2 x3 = c1Out then smap (\<lambda>uu. Untimed (BOOL uu))\<cdot>(fst (x1, x0)) else smap (\<lambda>uu. Untimed (BOOL uu))\<cdot>(snd (x1, x0))))"
    by moura
  then have "\<forall>s sa sb sc. \<not> (if ee sc sb sa s = c1Out then smap (\<lambda>b. Untimed (BOOL b))\<cdot> (fst (s, sa)) \<sqsubseteq> smap (\<lambda>b. Untimed (BOOL b))\<cdot>(fst (sb, sc)) else smap (\<lambda>b. Untimed (BOOL b))\<cdot> (snd (s, sa)) \<sqsubseteq> smap (\<lambda>b. Untimed (BOOL b))\<cdot> (snd (sb, sc))) \<or> s \<sqsubseteq> sb \<and> sa \<sqsubseteq> sc"
    using f3 by presburger
  then have "c2Out = c1Out \<or> smap (\<lambda>b. Untimed (BOOL b))\<cdot>b \<notsqsubseteq> smap (\<lambda>b. Untimed (BOOL b))\<cdot>ba"
    using a2 by (metis (no_types) fst_conv snd_conv)
  then show "\<exists>e. (e = c1Out \<longrightarrow> smap (\<lambda>b. Untimed (BOOL b))\<cdot>a \<notsqsubseteq> smap (\<lambda>b. Untimed (BOOL b))\<cdot>aa) \<and> (e \<noteq> c1Out \<longrightarrow> smap (\<lambda>b. Untimed (BOOL b))\<cdot>b \<notsqsubseteq> smap (\<lambda>b. Untimed (BOOL b))\<cdot>ba)"
    using a1 by (metis (full_types))
qed
  

 
interpretation exc_out_SB: sbGen constrExCOut
  apply (simp add: sbGen_def, auto)
  using constr_out_sb_well apply auto[1]
  using constr_out_inj apply simp
  using constr_out_surj apply auto[1]
      apply (simp add: constrExCOut_def)
  using constr_out_nbelow apply auto[1]
  using constr_out_nbelow apply auto[1]
   apply (simp add: constrExCOut_def)
   apply (metis (mono_tags, lifting) fstI len_prod_minl len_prod_minr slen_smap sndI)
  using constr_out_lenex by auto[1]



definition check_greater_nat :: "nat ltl" where
  "check_greater_nat = GloballyLtl( AllPropLtl(\<lambda>x. x > 10))"

definition check_smaller_nat :: "nat ltl" where
  "check_smaller_nat = GloballyLtl( AllPropLtl(\<lambda>x. x < 5))"

text\<open>This formula is true iff the values of the stream are alternating each step. It is the same
formula as in @{term checkAlternating2}\<close>
definition check_alternating :: "bool ltl" where
  "check_alternating = GloballyLtl (HasNextLtl (EqualityLtl (PropLtl (\<lambda>x. x)) (NextLtl (PropLtl (\<lambda>x. \<not> x)))))"

definition specPred :: "nat stream \<Rightarrow> nat stream \<Rightarrow> bool stream \<Rightarrow> bool stream \<Rightarrow> bool"
  where "specPred input1 input2 output1 output2 = (((ltl_semantics input1 check_greater_nat) \<and> (ltl_semantics input2 check_smaller_nat)) \<longrightarrow> ((ltl_semantics output1 (AndLtl (AllPropLtl (\<lambda>x. x)) check_alternating))\<and> (ltl_semantics output2 (AndLtl (AllPropLtl (\<lambda>x. \<not> x)) check_alternating))))"
  
definition bundleSpec :: "(ExCIn\<^sup>\<Omega> \<rightarrow> ExCOut\<^sup>\<Omega>) set"
  where "bundleSpec = {f. \<forall>input :: ExCIn\<^sup>\<Omega>. specPred (fst (exc_in_SB.getter\<cdot>input)) (snd (exc_in_SB.getter\<cdot>input)) (fst (exc_out_SB.getter\<cdot>(f\<cdot>input))) (snd (exc_out_SB.getter\<cdot>(f\<cdot>input)))}"

end
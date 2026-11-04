theory SB
  imports stream.Stream SBElement 
      stream.EventStream stream.TOneStream stream.TsynStream
begin



lemma smap_event_tlen[simp]:
"#\<^sub>\<surd> (smap (Timed \<circ> TLive \<circ> map_event f)\<cdot>aa) = #\<^sub>\<surd>aa"
  apply(induction aa,simp_all)
  apply(simp add: tlen_stream_def; fail)
  by(case_tac a,simp_all)

lemma smap_tsyn_tlen[simp]:
"#\<^sub>\<surd> (smap (Timed \<circ> Tsyn \<circ> map_tsyn constr)\<cdot>aa) = #\<^sub>\<surd> aa"
  apply(induction aa)
  apply(rule adm_eq)
  apply (simp_all,simp add: tlen_stream_def)
  using lnat_suc_plus by blast

lemma smap_to_tlen[simp]:
"#\<^sub>\<surd> (smap (Timed \<circ> TOne)\<cdot>aa) = # aa"
  apply(induction aa)
  apply(rule adm_eq)
  apply (simp_all,simp add: tlen_stream_def)
  using lnat_suc_plus by blast

lemma tlen_smap_tone_mstream[simp]:"#\<^sub>\<surd> (smap (Timed \<circ> TOne \<circ> map_tone f)\<cdot>aa) = #\<^sub>\<surd> aa"
  by (metis slen_smap smap_to_tlen smapsmap2smap tlen_len_eq)


default_sort %invisible chan

                                               text\<open>\label{sec:sb}\<close>

text \<open>Streams are the backbone of this verification
framework and stream bundles are used to model components with
multiple input and output streams. Any
stream in a stream bundle is identifiable through its channel.
Hence, a \gls{sb} is a function from channels to streams.
Since the allowed messages on a channel may be restricted, the
streams of a \gls{sb} only contain streams of elements from the
type of their channel (@{const ctype}). Similar to @{type sbElem}s, we
formulate a predicate to describe the properties of a \gls{sb}.\<close>

definition lsb_well :: "('c::chan \<Rightarrow> M stream) \<Rightarrow> bool" where
"lsb_well f \<equiv> \<forall>c. sValues\<cdot>(f c) \<subseteq> ctype (Rep c)"

text\<open>This definition uses @{const sValues} function defined for
streams in \cref{ssec:sValues_def} to obtain a set, which contains every
element
occurring in a stream. If the values of each stream are a subset of
the allowed messages on their corresponding channels, the function
is a \gls{sb}. Unlike our @{type sbElem} predicate, a
differentiation for the empty domain is not necessary, because every
non-empty stream for bundles with an empty domain would lead to a
contradiction with the @{const lsb_well} predicate.\<close>


lemma lsbwellI:
  assumes"\<And>c. sValues\<cdot>(f c) \<subseteq> ctype (Rep c)"
  shows"lsb_well f"
  by (simp add: assms lsb_well_def)

lemma sbwellD: assumes "lsb_well sb" and "ctype (Rep c) \<subseteq> A"
    shows "sValues\<cdot>(sb c) \<subseteq> A"
  using assms(1) assms(2) lsb_well_def by blast

lemma sbwell_ex[simp]:"lsb_well (\<lambda>c. \<epsilon>)"
  by(simp add: lsb_well_def)

lemma sbwell_adm: "adm lsb_well"
  unfolding lsb_well_def
  apply(rule adm_all, rule admI)
  by (simp add: ch2ch_fun l44 lub_fun)

lemma subsb_well: fixes sb::"'cs1 \<Rightarrow> M stream"
  assumes "chDom TYPE('cs2) \<subseteq> chDom TYPE('cs1)"
  and "lsb_well sb"
  and "chDom TYPE('cs2) \<noteq> {}"
  shows"lsb_well (\<lambda>c. sb (Abs (Rep (c::'cs2))))"
proof(rule lsbwellI)
  fix c::'cs2
  obtain c2 where c_def:"(c2::'cs1) = (Abs (Rep c))"
            and cdom:"Rep c2\<in> chDom TYPE('cs2)"
    by (metis assms(1) assms(3) chdom_in rep_reduction subset_iff)
  have "sValues\<cdot>(sb c2) \<subseteq> ctype (Rep c2)"
    using assms(2) lsb_well_def by blast
  thus "sValues\<cdot>(sb (Abs (Rep c))) \<subseteq> ctype (Rep c)"
    apply (simp add: c_def)
    by (metis (mono_tags, lifting) abs_fail assms(1) assms(3) chdom_in subset_eq)
qed

lemma empty_sbwell[simp]: assumes"chDom TYPE ('chan) = {}"
  and " lsb_well (sb::'chan \<Rightarrow> M stream)"
  shows" sb x = \<epsilon>"
  using assms
  apply(auto simp add: lsb_well_def)[1]
  using sValues_notempty by blast







datatype 'm::countable combinedstream = UNTIMED "'m stream"       |
                          TEVENT   "'m event stream" |
                          TSLICED    "'m list stream"  |
                          TONE    "'m tone stream"  |
                          TSYN    "'m tsyn stream"


instantiation combinedstream::(countable) below
begin
fun below_combinedstream::"'a combinedstream \<Rightarrow> 'a combinedstream \<Rightarrow> bool" where
"below_combinedstream (UNTIMED a) (UNTIMED b) = (a \<sqsubseteq> b)" |
"below_combinedstream (TEVENT a) (TEVENT b) = (a \<sqsubseteq> b)" |
"below_combinedstream (TSLICED a) (TSLICED b) = (a \<sqsubseteq> b)"|
"below_combinedstream (TONE a) (TONE b) = (a \<sqsubseteq> b)"|
"below_combinedstream (TSYN a) (TSYN b) = (a \<sqsubseteq> b)"|
"below_combinedstream _ _ = False"

instance by(intro_classes)
end

fun combGetTime::"'m::countable combinedstream \<Rightarrow> timeType" where
"combGetTime (UNTIMED s) = TUntimed" |
"combGetTime (TEVENT s) =TTLive"   |
"combGetTime (TSLICED s) = TTFin"    |
"combGetTime (TONE s) = TTOne"    |
"combGetTime (TSYN s) = TTsyn"


lemma combgettime_below_eq: "x\<sqsubseteq>y \<Longrightarrow> combGetTime x = combGetTime y"
  by(cases x; cases y; simp)


instance combinedstream::(countable) po
  apply(intro_classes)
    apply(rename_tac x, case_tac x; simp)
   apply(rename_tac x y z, case_tac x; case_tac y; case_tac z; simp only: below_trans below_combinedstream.simps)
  by(rename_tac x y, case_tac x; case_tac y; simp add: below_antisym)

lemma comstreamchainE: assumes "chain S"
  obtains
     SEvent where "chain SEvent" and "S = TEVENT o SEvent"
   | SUntimed where "chain SUntimed" and "S = UNTIMED o SUntimed"
   | SList where "chain SList" and "S = TSLICED o SList"
   | STone where "chain STone" and "S = TONE o STone"
   | STsyn where "chain STsyn" and "S = TSYN o STsyn"
proof (cases "S 0")
  case (UNTIMED _)
  hence in_range: "\<And>n. S n \<in> range UNTIMED"
    by (metis chain_mono[OF assms] below_combinedstream.simps combinedstream.exhaust le0 range_eqI)
  have "chain (\<lambda>n. (inv UNTIMED) (S n))"
    by(rule chainI, metis assms below_combinedstream.simps(1) f_inv_into_f in_range po_class.chainE)
  then show ?thesis
    by (simp add: comp_def f_inv_into_f in_range that(2))
next
  case (TEVENT _)
  hence in_range: "\<And>n. S n \<in> range TEVENT"
    by (metis chain_mono[OF assms] below_combinedstream.simps combinedstream.exhaust le0 range_eqI)
  have "chain (\<lambda>n. (inv TEVENT) (S n))"
    by(rule chainI, metis assms below_combinedstream.simps f_inv_into_f in_range po_class.chainE)
  then show ?thesis
    by (simp add: comp_def f_inv_into_f in_range that)
next
  case (TSLICED _)
  hence in_range: "\<And>n. S n \<in> range TSLICED"
    by (metis chain_mono[OF assms] below_combinedstream.simps combinedstream.exhaust le0 range_eqI)
  have "chain (\<lambda>n. (inv TSLICED) (S n))"
    by(rule chainI, metis assms below_combinedstream.simps f_inv_into_f in_range po_class.chainE)
  then show ?thesis
    by (simp add: comp_def f_inv_into_f in_range that)
next
  case (TONE _)
  hence in_range: "\<And>n. S n \<in> range TONE"
    by (metis chain_mono[OF assms] below_combinedstream.simps combinedstream.exhaust le0 range_eqI)
  have "chain (\<lambda>n. (inv TONE) (S n))"
    by(rule chainI, metis assms below_combinedstream.simps f_inv_into_f in_range po_class.chainE)
  then show ?thesis
    by (simp add: comp_def f_inv_into_f in_range that)
next
  case (TSYN _)
  hence in_range: "\<And>n. S n \<in> range TSYN"
    by (metis chain_mono[OF assms] below_combinedstream.simps combinedstream.exhaust le0 range_eqI)
  have "chain (\<lambda>n. (inv TSYN) (S n))"
    by(rule chainI, metis assms below_combinedstream.simps f_inv_into_f in_range po_class.chainE)
  then show ?thesis
    by (simp add: comp_def f_inv_into_f in_range that)
qed

lemma event_lub: "chain SEvent \<Longrightarrow> range (\<lambda>x::nat. TEVENT (SEvent x)) <<| (TEVENT (\<Squnion>i. SEvent i))"
  apply(intro is_lubI is_ubI)
   apply(rename_tac x; case_tac x, auto simp add: is_ub_thelub)
  apply(rename_tac u; case_tac u; simp)
  by(meson below_combinedstream.simps ub_rangeD is_lub_thelub ub_imageD ub_imageI)+

lemma untimed_lub: "chain SUntimed \<Longrightarrow> range (\<lambda>x::nat. UNTIMED (SUntimed x)) <<| (UNTIMED (\<Squnion>i. SUntimed i))"
  apply(intro is_lubI is_ubI)
   apply(rename_tac x; case_tac x, auto simp add: is_ub_thelub)
  apply(rename_tac u; case_tac u; simp)
  by(meson below_combinedstream.simps ub_rangeD is_lub_thelub ub_imageD ub_imageI)+

lemma list_lub: "chain SUntimed \<Longrightarrow> range (\<lambda>x::nat. TSLICED (SUntimed x)) <<| (TSLICED (\<Squnion>i. SUntimed i))"
  apply(intro is_lubI is_ubI)
   apply(rename_tac x; case_tac x, auto simp add: is_ub_thelub)
  apply(rename_tac u; case_tac u; simp)
  by(meson below_combinedstream.simps ub_rangeD is_lub_thelub ub_imageD ub_imageI)+

lemma tone_lub: "chain SUntimed \<Longrightarrow> range (\<lambda>x::nat. TONE (SUntimed x)) <<| (TONE (\<Squnion>i. SUntimed i))"
  apply(intro is_lubI is_ubI)
   apply(rename_tac x; case_tac x, auto simp add: is_ub_thelub)
  apply(rename_tac u; case_tac u; simp)
  by(meson below_combinedstream.simps ub_rangeD is_lub_thelub ub_imageD ub_imageI)+

lemma tsyn_lub: "chain SUntimed \<Longrightarrow> range (\<lambda>x::nat. TSYN (SUntimed x)) <<| (TSYN (\<Squnion>i. SUntimed i))"
  apply(intro is_lubI is_ubI)
   apply(rename_tac x; case_tac x, auto simp add: is_ub_thelub)
  apply(rename_tac u; case_tac u; simp)
  by(meson below_combinedstream.simps ub_rangeD is_lub_thelub ub_imageD ub_imageI)+

instance combinedstream::(countable) cpo
  apply(intro_classes)
  apply(case_tac S rule: comstreamchainE; simp)
  using event_lub untimed_lub list_lub tsyn_lub tone_lub apply blast+
  done


fun combStreamCases_h::"('m::countable event stream \<rightarrow> 'o::pcpo)
                    \<Rightarrow> ('m tsyn stream \<rightarrow> 'o)
                    \<Rightarrow> ('m tone stream \<rightarrow> 'o)
                    \<Rightarrow> ('m list stream \<rightarrow> 'o)
                    \<Rightarrow> ('m stream \<rightarrow> 'o)
                    \<Rightarrow> 'm combinedstream \<Rightarrow> 'o" where
"combStreamCases_h _ _ _ _ f (UNTIMED s) = f\<cdot>s" |
"combStreamCases_h f _ _ _ _ (TEVENT s) = f\<cdot>s"   |
"combStreamCases_h _ _ _ f _ (TSLICED s) = f\<cdot>s"    |
"combStreamCases_h _ _ f _ _ (TONE s) = f\<cdot>s"    |
"combStreamCases_h _ f _ _ _ (TSYN s) = f\<cdot>s"

definition combStreamCases::"('m::countable event stream \<rightarrow> 'o::pcpo)
                    \<Rightarrow> ('m tsyn stream \<rightarrow> 'o)
                    \<Rightarrow> ('m tone stream \<rightarrow> 'o)
                    \<Rightarrow> ('m list stream \<rightarrow> 'o)
                    \<Rightarrow> ('m stream \<rightarrow> 'o)
                    \<Rightarrow> 'm combinedstream \<rightarrow> 'o" where
"combStreamCases eventF tsynF toneF listF untimedF = (\<Lambda> s. combStreamCases_h eventF tsynF toneF listF untimedF s)"


lemma combstreamcases_insert: "combStreamCases eventF tsynF toneF listF untimedF\<cdot>s
  = combStreamCases_h eventF tsynF toneF listF untimedF s"
  unfolding combStreamCases_def
  apply(subst beta_cfun)
   apply(rule contI)
   apply(rename_tac S; case_tac S rule: comstreamchainE)
        apply simp_all
  using event_lub tone_lub tsyn_lub list_lub untimed_lub
  by (metis ch2ch_Rep_cfunR combStreamCases_h.simps contlub_cfun_arg lub_eqI thelubE)+

definition combValues:: "'m::countable combinedstream \<rightarrow> 'm set" where
"combValues = combStreamCases eValues tsynValues toneValues listValues sValues"


fun combLeast::"timeType \<Rightarrow> 'm::countable combinedstream" where
"combLeast TUntimed = UNTIMED \<epsilon>" |
"combLeast TTOne = TONE \<epsilon> " |
"combLeast TTFin = TSLICED \<epsilon>" |
"combLeast TTLive = TEVENT \<epsilon>"  |
"combLeast TTsyn = TSYN \<epsilon>"

lemma least_time[simp]: "combGetTime (combLeast tt) = tt"
  by(cases tt; simp)


lemma valueleast[simp]: "combValues\<cdot>(combLeast tt) = {}"
  by(cases "tt"; simp add: combValues_def combstreamcases_insert)


lemma combvalues_untimed_insert[simp]:"combValues\<cdot>(UNTIMED (\<up>aa \<Zcat> s)) = insert aa (combValues\<cdot>(UNTIMED s))"
  by(simp add: combValues_def combstreamcases_insert)

lemma combvalues_tone_insert[simp]:"combValues\<cdot>(TONE (\<up>(TOneMsg aa) \<Zcat> s)) = insert aa (combValues\<cdot>(TONE s))"
  by(simp add: combValues_def combstreamcases_insert tonedom_inv_sValues)

lemma combvalues_tfin_insert[simp]:"combValues\<cdot>(TSLICED (\<up>(ls) \<Zcat> s)) = set ls \<union> (combValues\<cdot>(TSLICED s))"
  by(simp add: combValues_def combstreamcases_insert)

lemma combvalues_event_insert[simp]:"combValues\<cdot>(TEVENT (\<up>(EventMsg aa) \<Zcat> s)) = insert aa (combValues\<cdot>(TEVENT s))"
  by(simp add: combValues_def combstreamcases_insert)

lemma combvalues_tick_insert[simp]:"combValues\<cdot>(TEVENT (\<up>(Tick) \<Zcat> s)) = (combValues\<cdot>(TEVENT s))"
  by(simp add: combValues_def combstreamcases_insert)

lemma combvalues_tsyn_insert[simp]:"combValues\<cdot>(TSYN (\<up>(TSynMsg aa) \<Zcat> s)) = insert aa (combValues\<cdot>(TSYN s))"
  by(simp add: combValues_def combstreamcases_insert)

lemma combvalues_eps_insert[simp]:"combValues\<cdot>(TSYN (\<up>(Eps) \<Zcat> s)) = (combValues\<cdot>(TSYN s))"
  by(simp add: combValues_def combstreamcases_insert)
  
definition sb_well :: "('c::chan \<Rightarrow> msg combinedstream) \<Rightarrow> bool" where
"sb_well f \<equiv> (\<forall>c.  combValues\<cdot>(f c) \<subseteq> cMsg (Rep c))
              \<and> (\<forall>c. combGetTime (f c) = (cTime (Rep c)))
              \<and> (\<forall>c. cMsg (Rep c) = {} \<longrightarrow> (f c) = combLeast (cTime (Rep c)))"

lemma newsb_wellI:
  assumes "\<And>c. cMsg (Rep c) \<noteq> {} \<Longrightarrow> combValues\<cdot>(f c) \<subseteq> cMsg (Rep c)"
    and "\<And>c. combGetTime (f c) = (cTime (Rep c))"
    and "\<And>c. cMsg (Rep c) = {} \<longrightarrow> (f c) = combLeast (cTime (Rep c))"
  shows "sb_well f"
  by (metis (no_types, opaque_lifting) assms empty_subsetI sb_well_def valueleast)



lemma newsbwell_adm: "adm sb_well"
  unfolding sb_well_def
  apply(rule adm_conj)
   defer
   apply(rule adm_conj)
    apply(rule adm_all)
    defer
    apply(rule adm_all)
    defer
    apply(rule adm_all)
  apply simp
   apply(rule admI)
   apply (metis combgettime_below_eq fun_chain_iff is_ub_thelub lub_fun)
  apply(rule admI)
  using lub_fun by force

lemma combleast_well: "sb_well (\<lambda>c. combLeast (cTime (Rep c)))"
  apply(rule newsb_wellI)
    apply simp
   apply(simp)
  by simp


cpodef 'c::chan sb("(_\<^sup>\<Omega>)"     [1000] 999     )
         = "{f::('c::chan \<Rightarrow> msg combinedstream). sb_well f}"
  using newsbwell_adm combleast_well by auto


lemma rep_untimed[simp]: "(Rep_sb f) c = UNTIMED x \<Longrightarrow>  cTime (Rep c) = TUntimed"
  using Rep_sb sb_well_def combGetTime.simps by (metis mem_Collect_eq)
lemma rep_tone[simp]: "(Rep_sb f) c = TONE x \<Longrightarrow>  cTime (Rep c) = TTOne"
  using Rep_sb sb_well_def combGetTime.simps by (metis mem_Collect_eq)
lemma rep_list[simp]: "(Rep_sb f) c = TSLICED x \<Longrightarrow>  cTime (Rep c) = TTFin"
  using Rep_sb sb_well_def combGetTime.simps by (metis mem_Collect_eq)
lemma rep_event[simp]: "(Rep_sb f) c = TEVENT x \<Longrightarrow>  cTime (Rep c) = TTLive"
  using Rep_sb sb_well_def combGetTime.simps by (metis mem_Collect_eq)
lemma rep_tsyn[simp]: "(Rep_sb f) c = TSYN x \<Longrightarrow>  cTime (Rep c) = TTsyn"
  using Rep_sb sb_well_def combGetTime.simps by (metis mem_Collect_eq)

definition least_sb :: "'a\<^sup>\<Omega>" where
  "least_sb \<equiv> Abs_sb (\<lambda>c. combLeast (cTime (Rep c)))"

lemma least_sb_bottom: "\<forall>y. least_sb \<sqsubseteq> y"
  apply(simp add: least_sb_def)
  apply rule
  unfolding below_sb_def
  apply(rule fun_belowI)
  apply(subst Abs_sb_inverse, simp add: combleast_well)
  apply(case_tac "Rep_sb y x")
      apply(simp; fail)+
  done


instance sb::(chan) pcpo
  apply(intro_classes)
  by(rule_tac x="least_sb" in exI; simp add: least_sb_bottom)

lemma least_sb_bottom_eq: "\<bottom> = least_sb"
  apply(simp add: bottom_def)
  by (metis bottom_def least_sb_bottom minimal po_eq_conv)




lemma event_cont[simp,cont2cont]: "cont TEVENT"
  apply(rule contI)
  by (simp add: event_lub)

lemma [simp,cont2cont]: "cont UNTIMED"
  apply(rule contI)
  by (simp add: untimed_lub)
lemma [simp,cont2cont]:"cont TONE"
  apply(rule contI)
  by (simp add: tone_lub)
lemma [simp,cont2cont]:"cont TSLICED"
  apply(rule contI)
  by (simp add: list_lub)
lemma [simp,cont2cont]:"cont TSYN"
  apply(rule contI)
  by (simp add: tsyn_lub)

fun mstream2combined::"timeType \<Rightarrow> M stream \<rightarrow> msg combinedstream" where
"mstream2combined TTLive = (\<Lambda> s. TEVENT (smap (inv (Timed o TLive))\<cdot>s))" |
"mstream2combined TUntimed = (\<Lambda> s. UNTIMED (smap (inv Untimed)\<cdot>s))" |
"mstream2combined TTFin = (\<Lambda> s. TSLICED (smap (inv (Timed o TFin))\<cdot>s))" |
"mstream2combined TTOne = (\<Lambda> s. TONE (smap (inv (Timed o TOne))\<cdot>s))" |
"mstream2combined TTsyn = (\<Lambda> s. TSYN (smap (inv (Timed o Tsyn))\<cdot>s))"

definition sblegacy2new::"('c \<Rightarrow> M stream) \<Rightarrow> ('c::chan \<Rightarrow> msg combinedstream)" where
"sblegacy2new f c = mstream2combined (cTime (Rep c))\<cdot>(f c)"

lemma sblegacy2new_cont:
  "cont sblegacy2new"
  by(simp add: sblegacy2new_def)

thm cont_compose
thm cont_compose_mix

lemma combgettime_ctime[simp]:"combGetTime (sblegacy2new f c) = cTime (Rep c)"
  apply(simp add: sblegacy2new_def)
  by(cases "(cTime (Rep c))",simp_all add: cont_compose_mix)

lemma lsb_well_unfold:
  assumes "lsb_well f"
  shows"sValues\<cdot>(f c) \<subseteq> ctype (Rep c)"
  using assms lsb_well_def by blast


lemma mstream2combined_epsilon_least:  "mstream2combined t\<cdot>\<epsilon> = combLeast t"
  by(cases t; simp add: cont_compose_mix)

lemma combValues_empty: "combValues\<cdot>(mstream2combined (cTime (Rep (c :: 'chan :: chan)))\<cdot>\<epsilon>) = {}"
  by (simp add: mstream2combined_epsilon_least)

lemma
  legacy2new_well_ne:
  assumes "lsb_well (f:: 'a \<Rightarrow> M stream)"
    and "\<And>c::'a. cMsg (Rep c) \<noteq> {}"
  shows "combValues\<cdot>(sblegacy2new f c) \<subseteq> cMsg (Rep c)"
proof (cases "cTime (Rep c)")
  case TUntimed
  then have "combValues\<cdot>(sblegacy2new f c) = sValues\<cdot>(smap (inv Untimed)\<cdot>(f c))"
    by(simp add: sblegacy2new_def beta_cfun combValues_def combstreamcases_insert cont_compose_mix)

  then show ?thesis
    by (metis (no_types, lifting)
        TUntimed
        lsb_well_unfold
        assms
        ctype_def
        image_inv_f_f
        inj_untimed
        smap_sValues
        subset_image_iff
        timeType.simps(21)
      )

next
  case TTOne
  then have "combValues\<cdot>(sblegacy2new f c) = toneValues\<cdot>(smap ((inv (Timed o TOne)))\<cdot>(f c))"
    by(simp add: sblegacy2new_def beta_cfun combValues_def combstreamcases_insert cont_compose_mix)

  also have "sValues\<cdot>(f c) \<subseteq> (Timed o TOne) ` (TOneMsg ` cMsg (Rep c))"
    by (metis TTOne lsb_well_unfold assms(1) assms(2) ctype_def timeType.case(2))

  then have "sValues\<cdot>(smap (inv (Timed o TOne))\<cdot>(f c)) \<subseteq> TOneMsg ` cMsg (Rep c)"
    by (metis image_inv_f_f image_mono inj_tonetimed smap_sValues)

  then have "sValues\<cdot>(smap (inv (Timed o TOne))\<cdot>(f c)) \<subseteq> (TOneMsg) ` cMsg (Rep c)"
    by (metis smap_sValues smapsmap2smap subset_image_iff)

  then show ?thesis
    using calculation by (metis TOneDatatype.inj_tone image_inv_f_f image_mono tonedom_inv_sValues)

next
  case TTFin
  then have s1: "combValues\<cdot>(sblegacy2new f c) = listValues\<cdot>(smap (inv (Timed o TFin))\<cdot>(f c))"
    by(simp add: sblegacy2new_def beta_cfun combValues_def combstreamcases_insert cont_compose_mix)

  also have s2: "... = \<Union>(set ` sValues\<cdot>(smap (inv (Timed o TFin))\<cdot>(f c)))"
    by (simp add: listValues_def slisttoevent_evalues)

  also have s3: "sValues\<cdot>(f c) \<subseteq> (Timed o TFin) ` {ls. set ls \<subseteq> (cMsg (Rep c))}"
    by (simp add: TTFin assms(1) ctype_def sbwellD)

  have s4: "sValues\<cdot>(smap (inv (Timed \<circ> TFin))\<cdot>(f c))
             \<subseteq> (inv (Timed \<circ> TFin)) ` {Timed (TFin ls) | ls. set ls \<subseteq> cMsg (Rep c)}"
    using assms(1) Stream.smap_sValues
    using \<open>sValues\<cdot>((f::'a \<Rightarrow> M stream) (c::'a)) \<subseteq> (Timed \<circ> TFin) ` {ls::msg list. set ls \<subseteq> cMsg (Rep c)}\<close> 
    by (metis (no_types, lifting) ext comp_apply image_mono setcompr_eq_image)
  also have s5: "... \<subseteq> {ls. set ls \<subseteq> cMsg (Rep c)}"
    by (auto simp add: inv_into_def)

  then have "sValues\<cdot>(smap (inv (Timed o TFin))\<cdot>(f c)) \<subseteq> {ls. set ls \<subseteq> (cMsg (Rep c))}"
    using s4 by simp
  
  then have "\<Union>(set ` sValues\<cdot>(smap (inv (Timed o TFin))\<cdot>(f c))) \<subseteq> (cMsg (Rep c))"
    by blast

  then show ?thesis
    using calculation s1 s2 by presburger
next
  case TTLive

  then have "combValues\<cdot>(sblegacy2new f c) = eValues\<cdot>(smap (inv (Timed o TLive))\<cdot>(f c))"
    by(simp add: sblegacy2new_def beta_cfun combValues_def combstreamcases_insert cont_compose_mix)

  have "sValues\<cdot>(f c) \<subseteq> (Timed o TLive) ` ({Tick} \<union> (EventMsg ` (cMsg (Rep c))))"
    by (metis TTLive lsb_well_unfold assms(1) assms(2) ctype_def timeType.case(4))

  also have "(inv (Timed o TLive)) ` (Timed o TLive) ` ({Tick} \<union> (EventMsg ` (cMsg (Rep c)))) = ({Tick} \<union> (EventMsg ` (cMsg (Rep c))))"
    by (meson image_mono image_inv_f_f inj_compose inj_timed inj_tlive)

  then have "(inv (Timed o TLive)) ` sValues\<cdot>(f c) \<subseteq> ({Tick} \<union> (EventMsg ` (cMsg (Rep c))))"
    using calculation by (metis image_mono)

  then show ?thesis
    using calculation \<open>combValues\<cdot>(sblegacy2new (f::'a \<Rightarrow> M stream) (c::'a)) = eValues\<cdot>(smap (inv (Timed \<circ> TLive))\<cdot>(f c))\<close>
    by (simp add: eValues_sValues_without_tick_subset smap_sValues)

next
  case TTsyn
  then have 1: "combValues\<cdot>(sblegacy2new f c) = {m | m. (TSynMsg m) \<in> sValues\<cdot>(smap (inv (Timed o Tsyn))\<cdot>(f c))}"
    using tsyndom_insert 
    by(simp add: sblegacy2new_def beta_cfun combValues_def combstreamcases_insert cont_compose_mix)

  also have "sValues\<cdot>(f c) \<subseteq> (Timed o Tsyn) ` ({Eps} \<union> (TSynMsg ` (cMsg (Rep c))))"
    by (metis TTsyn lsb_well_unfold assms(1) assms(2) ctype_def timeType.case(5))

  then have "sValues\<cdot>(smap (inv (Timed o Tsyn))\<cdot>(f c)) \<subseteq> ({Eps} \<union> (TSynMsg ` (cMsg (Rep c))))"
    by (metis image_inv_f_f image_mono inj_compose inj_timed inj_tsyn smap_sValues)

  then have "{m | m. (TSynMsg m) \<in> sValues\<cdot>(smap (inv (Timed o Tsyn))\<cdot>(f c))} \<subseteq> (cMsg (Rep c))"
    by blast

  then have "tsynValues\<cdot>(smap (inv (Timed o Tsyn))\<cdot>(f c)) \<subseteq> (cMsg (Rep c))"
    using calculation by (simp add: tsyndom_insert)

  then show ?thesis
    using 1 \<open>{m |m::msg. TSynMsg m \<in> sValues\<cdot> (smap (inv (Timed \<circ> Tsyn))\<cdot> ((f::'a \<Rightarrow> M stream) (c::'a)))} \<subseteq> cMsg (Rep c)\<close>
    by blast
qed

lemma legacy2new_well:
  assumes "lsb_well f"
  shows "sb_well (sblegacy2new f)"
  apply(rule newsb_wellI)
   prefer 2
   apply simp

  apply(case_tac "cMsg (Rep c) = {}")
  apply (metis
        assms
        sblegacy2new_def
        combValues_empty
        ctype_empty_iff
        dom2ctypenempty
        dual_order.refl
        empty_sbwell
  )
   apply (meson assms ctype_empty_iff dom2ctypeempty dom2ctypenempty legacy2new_well_ne)
  apply(simp add: sblegacy2new_def)
  by (metis
      assms
      ctype_empty_iff
      dom2ctypenempty
      empty_sbwell
      mstream2combined_epsilon_least
  )


definition Abs_lsb::"('c \<Rightarrow> M stream) \<Rightarrow> 'c sb" where
"Abs_lsb f = Abs_sb (sblegacy2new f)"



definition combined2mstream::"msg combinedstream \<rightarrow> M stream" where
"combined2mstream = combStreamCases (smap (Timed o TLive))
                                (smap (Timed o Tsyn))
                                (smap (Timed o TOne))
                                (smap (Timed o TFin))
                                (smap Untimed)"

lemma combined2mstream_combLeast: "combined2mstream\<cdot>(combLeast c) = \<epsilon>"
proof (cases "(combLeast c)")
  case (UNTIMED s)
  then have "s = \<epsilon>"
    by (metis (no_types, lifting) combinedstream.inject(1) combinedstream.simps combLeast.elims)
  then have "combined2mstream\<cdot>(combLeast c) = combined2mstream\<cdot>(UNTIMED \<epsilon>)"
    by (metis UNTIMED combLeast.simps(1) least_time)
  then show ?thesis
    by(simp add: combined2mstream_def combstreamcases_insert)
next
  case (TEVENT s)
  then have "s = \<epsilon>"
    by (metis combGetTime.simps(2) combLeast.simps(4) combinedstream.inject(2) least_time)
  then have "combined2mstream\<cdot>(combLeast c) = combined2mstream\<cdot>(TEVENT \<epsilon>)"
    by (metis TEVENT combLeast.simps(4) least_time)
  then show ?thesis
    by(simp add: combined2mstream_def combstreamcases_insert)
next
  case (TSLICED s)
  then have "s = \<epsilon>"
    by (metis (no_types, lifting) combinedstream.inject(1) combinedstream.simps combLeast.elims)
  then have "combined2mstream\<cdot>(combLeast c) = combined2mstream\<cdot>(TSLICED \<epsilon>)"
    by (metis TSLICED combLeast.simps(3) least_time)
  then show ?thesis
    by(simp add: combined2mstream_def combstreamcases_insert)
next
  case (TONE s)
  then have "s = \<epsilon>"
    by (metis (no_types, lifting) combinedstream.inject(1) combinedstream.simps combLeast.elims)
  then have "combined2mstream\<cdot>(combLeast c) = combined2mstream\<cdot>(TONE \<epsilon>)"
    by (metis TONE combLeast.simps(2) least_time)
  then show ?thesis
    by(simp add: combined2mstream_def combstreamcases_insert)
next
  case (TSYN s)
  then have "s = \<epsilon>"
    by (metis (no_types, lifting) combinedstream.inject(1) combinedstream.simps combLeast.elims)
  then have "combined2mstream\<cdot>(combLeast c) = combined2mstream\<cdot>(TSYN \<epsilon>)"
    by (metis TSYN combLeast.simps(5) least_time)
  then show ?thesis
    by(simp add: combined2mstream_def combstreamcases_insert)
qed


definition sbnew2legacy::"('c::chan \<Rightarrow> msg combinedstream) \<Rightarrow> ('c \<Rightarrow> M stream)" where
"sbnew2legacy f c = combined2mstream\<cdot>(f c)"

lemma sbnew2legacy_cont: "cont sbnew2legacy"
  unfolding sbnew2legacy_def
  by(intro cont2cont)


lemma
  new2legacy_well_h_untimed:
  assumes "sb_well f \<and> cMsg (Rep c) \<noteq> {} \<and> cTime (Rep c) = TUntimed"
  shows "sValues\<cdot>(combined2mstream\<cdot>(f c)) \<subseteq> Untimed ` cMsg (Rep c)"
proof -
  obtain s where s: "f c = UNTIMED s"
    by (metis assms combGetTime.elims sb_well_def timeType.distinct(5) timeType.simps)
  have 1: "combined2mstream\<cdot>(f c) = (smap Untimed)\<cdot>s"
    by (simp add: combined2mstream_def combstreamcases_insert s)
  have 2: "combValues\<cdot>(f c) \<subseteq> cMsg (Rep c)"
    using assms(1) sb_well_def by blast
  have "combValues\<cdot>(f c) = sValues\<cdot>s"
    apply(simp add: combValues_def combstreamcases_insert)
    using s by auto
  then show ?thesis
    by (metis 1 2 inj_image_subset_iff inj_untimed smap_sValues)
qed



lemma
  new2legacy_well_h_ttone:
  assumes "sb_well f \<and> cMsg (Rep c) \<noteq> {} \<and> cTime (Rep c) = TTOne"
  shows "sValues\<cdot>(combined2mstream\<cdot>(f c)) \<subseteq> (\<lambda>x. Timed (TOne x)) ` (TOneMsg ` cMsg (Rep c))"
proof -
  obtain s where s: "f c = TONE s"
    by (metis assms combGetTime.elims sb_well_def timeType.distinct(5) timeType.simps)
  have "combined2mstream\<cdot>(f c) = (smap (Timed o TOne))\<cdot>s"
    by (simp add: combined2mstream_def combstreamcases_insert s)
  also have "combValues\<cdot>(f c) \<subseteq> cMsg (Rep c)"
    using assms(1) sb_well_def by blast
  moreover have "combValues\<cdot>(f c) = (inv TOneMsg) ` sValues\<cdot>s"
    by(simp add: combValues_def combstreamcases_insert s tonedom_inv_sValues)
  ultimately show ?thesis
    by (metis (no_types, lifting) ext UNIV_eq_I comp_apply
        image_inv_into_cancel image_mono rangeI
        smap_sValues  subset_UNIV tone2eventElem.cases)
qed



lemma
  new2legacy_well_h_tfin:
  assumes "sb_well f \<and> cMsg (Rep c) \<noteq> {} \<and> cTime (Rep c) = TTFin"
  shows "sValues\<cdot>(combined2mstream\<cdot>(f c)) \<subseteq> (\<lambda>x. Timed (TFin x)) ` {ls. set ls \<subseteq> cMsg (Rep c)}"
proof -
  obtain s where s: "f c = TSLICED s"
    by (metis assms combGetTime.elims sb_well_def timeType.simps(4,10,16,18))
  have "combined2mstream\<cdot>(f c) = (smap (Timed o TFin))\<cdot>s"
    by (simp add: combined2mstream_def combstreamcases_insert s)
  also have "combValues\<cdot>(f c) \<subseteq> cMsg (Rep c)"
    using assms(1) sb_well_def by blast
  moreover have "combValues\<cdot>(f c) = \<Union>(set ` sValues\<cdot>s)"
    by(simp add: combValues_def combstreamcases_insert s listValues_def slisttoevent_evalues)
 ultimately have "\<forall>ls\<in>sValues\<cdot>s. set ls \<subseteq> cMsg (Rep c)"
    by auto
  hence "sValues\<cdot>s \<subseteq> {ls. set ls \<subseteq> cMsg (Rep c)}"
    by blast
  thus ?thesis 
  proof -
    obtain bb :: "msg list \<Rightarrow> bool" where
      f1: "\<forall>x1. bb x1 = (set x1 \<subseteq> cMsg (Rep c))"
      by moura
    obtain mm :: "msg list \<Rightarrow> M" where
      f2: "\<forall>x1. mm x1 = Timed (TFin x1)"
      by force
    have f3: "\<forall>f s. sValues\<cdot>(smap f\<cdot>(s::msg list stream)::M stream) = f ` sValues\<cdot>s"
      using smap_sValues by blast
    have "sValues\<cdot>s \<subseteq> Collect bb"
      using f1 \<open>sValues\<cdot>(s::msg list stream) \<subseteq> {ls::msg list. set ls \<subseteq> cMsg (Rep (c::'a))}\<close> by blast
    then have "sValues\<cdot>(combined2mstream\<cdot>(f c)) \<subseteq> mm ` Collect bb"
      using f3 f2 \<open>combined2mstream\<cdot>((f::'a \<Rightarrow> msg combinedstream) (c::'a)) = smap (Timed \<circ> TFin)\<cdot>(s::msg list stream)\<close> subset_image_iff by auto
    then show ?thesis
      using f2 f1 by blast
  qed
qed


lemma
  new2legacy_well_h_tlive:
  assumes "sb_well f \<and> cMsg (Rep c) \<noteq> {} \<and> cTime (Rep c) = TTLive"
  shows "sValues\<cdot>(combined2mstream\<cdot>(f c)) \<subseteq> insert (Timed (TLive \<surd>)) ((\<lambda>x. Timed (TLive x)) ` EventMsg ` cMsg (Rep c))"
proof -
  obtain s where s: "f c = TEVENT s"
    by (metis assms combGetTime.elims sb_well_def timeType.simps(6,12,16,20))
  have "combined2mstream\<cdot>(f c) = (smap (Timed o TLive))\<cdot>s"
    by (simp add: combined2mstream_def combstreamcases_insert s)
  also have "combValues\<cdot>(f c) \<subseteq> cMsg (Rep c)"
    using assms(1) sb_well_def by blast
  moreover have "combValues\<cdot>(f c) = eValues\<cdot>s"
    by(simp add: combValues_def combstreamcases_insert s)
  then have "sValues\<cdot>s \<subseteq> EventMsg ` cMsg (Rep c) \<union> {Tick}"
    by (metis calculation(2) sValues_eValues_with_tick_subset)
  ultimately have "sValues\<cdot>(combined2mstream\<cdot>(f c)) \<subseteq> (Timed o TLive) ` (EventMsg ` cMsg (Rep c) \<union> {Tick})"
    by (metis smap_sValues subset_image_iff)
  thus ?thesis
    by auto
qed


lemma
  new2legacy_well_h_tsyn:
  assumes "sb_well f \<and> cMsg (Rep c) \<noteq> {} \<and> cTime (Rep c) = TTsyn"
  shows "sValues\<cdot>(combined2mstream\<cdot>(f c)) \<subseteq> insert (Timed (Tsyn \<sim>)) ((\<lambda>x. Timed (Tsyn x)) ` TSynMsg ` cMsg (Rep c))"
proof -
  obtain s where s: "f c = TSYN s"
    by (metis assms combGetTime.elims sb_well_def timeType.distinct(1) timeType.simps)
  have "sValues\<cdot>(combined2mstream\<cdot>(f c))
      = (Timed \<circ> Tsyn) ` sValues\<cdot>s"
    using s
    by (simp add: combined2mstream_def
                  combstreamcases_insert Stream.smap_sValues)
  also have "... \<subseteq> insert (Timed (Tsyn \<sim>)) ((\<lambda>x. Timed (Tsyn x)) ` TSynMsg ` cMsg (Rep c))"
  proof
    fix x assume "x \<in> (Timed \<circ> Tsyn) ` sValues\<cdot>s"
    then obtain y where y: "y \<in> sValues\<cdot>s" "x = Timed (Tsyn y)"
      by auto
    from assms(1) have "combValues\<cdot>(f c) \<subseteq> cMsg (Rep c)"
      by (simp add: sb_well_def)
    moreover have "combValues\<cdot>(f c) = {m. TSynMsg m \<in> sValues\<cdot>s}"
      by (simp add: combValues_def combstreamcases_insert s tsyndom_insert)
    ultimately have "y = \<sim> \<or> (\<exists>m \<in> cMsg (Rep c). y = TSynMsg m)"
      using y(1) subset_iff by fastforce
    then show "x \<in> insert (Timed (Tsyn \<sim>)) ((\<lambda>x. Timed (Tsyn x)) ` TSynMsg ` cMsg (Rep c))"
      using y by auto
  qed
  finally show ?thesis .
qed

lemma new2legacy_well:
  assumes "sb_well f"
  shows "lsb_well (sbnew2legacy f)"
  unfolding sbnew2legacy_def
  apply(simp add: lsb_well_def ctype_def)
  apply(rule allI,case_tac "cMsg (Rep c) = {}", simp)
   apply (metis assms combined2mstream_combLeast sb_well_def svalues_eps)
  apply(case_tac "cTime (Rep c)"; simp)
  using assms new2legacy_well_h_untimed apply blast
  using assms new2legacy_well_h_ttone apply blast
  using assms new2legacy_well_h_tfin apply blast
  using assms new2legacy_well_h_tlive apply blast
  using assms new2legacy_well_h_tsyn by blast

definition Rep_lsb::"'c sb \<Rightarrow> ('c \<Rightarrow> M stream)" where
"Rep_lsb sb = (sbnew2legacy (Rep_sb sb))"

lemma
  Abs_lsb_inverse_h_h:
  assumes "lsb_well (f::'a \<Rightarrow> M stream)"
  shows "combined2mstream\<cdot>(sblegacy2new f c) = f c"
proof (cases "cTime (Rep (c::'a))")
  case TUntimed
  then have 1: "combined2mstream\<cdot>(sblegacy2new f c) = (smap Untimed)\<cdot>((smap (inv Untimed))\<cdot>(f c))"
    apply(simp add: combined2mstream_def combStreamCases_def sblegacy2new_def cont_compose_mix)
    by (metis combStreamCases_def combStreamCases_h.simps(1) combstreamcases_insert)

  then have 2: "... = smap (Untimed o (inv Untimed))\<cdot>(f c)"
    using smapsmap2smap by blast

  then have "sValues\<cdot>(f c) \<subseteq> range Untimed"
    by (metis
        TUntimed
        lsb_well_unfold
        assms
        bot.extremum
        ctype_def
        sbwellD
        smap_obtainin
        smap_sValues_range
        timeType.case(1)
    )

  then show ?thesis
    by (simp add: 1 2)

next
  case TTOne
  then have 1: "combined2mstream\<cdot>(sblegacy2new f c) = (smap (Timed o TOne))\<cdot>(smap ( (inv (Timed o TOne)))\<cdot>(f c))"
    apply(simp add: combined2mstream_def combStreamCases_def sblegacy2new_def cont_compose_mix)
    by (metis combStreamCases_def combStreamCases_h.simps(4) combstreamcases_insert)

  then have 2: "... = smap (Timed o TOne  o ((inv (Timed o TOne))))\<cdot>(f c)"
    using smapsmap2smap by blast

  then have "sValues\<cdot>(f c) \<subseteq> range (Timed o TOne)"
    by (simp add: TTOne assms ctype_def image_subsetI sbwellD)

  then show ?thesis
    by (simp add: 1 2)

next
  case TTFin
  then have 1: "combined2mstream\<cdot>(sblegacy2new f c) = (smap (Timed o TFin))\<cdot>(smap (inv (Timed o TFin))\<cdot>(f c))"
    apply(simp add: combined2mstream_def combStreamCases_def sblegacy2new_def cont_compose_mix)
    by (metis combStreamCases_def combStreamCases_h.simps(3) combstreamcases_insert)

  then have 2: "... = smap (Timed o TFin o (inv (Timed o TFin)))\<cdot>(f c)"
    using smapsmap2smap by blast

  then have "sValues\<cdot>(f c) \<subseteq> range (Timed o TFin)"
    by (simp add: TTFin assms ctype_def image_subsetI sbwellD)

  then show ?thesis
    by (simp add: 1 2)

next
  case TTLive
  then have 1: "combined2mstream\<cdot>(sblegacy2new f c) = (smap (Timed o TLive))\<cdot>(smap (inv (Timed o TLive))\<cdot>(f c))"
    apply(simp add: combined2mstream_def combStreamCases_def sblegacy2new_def cont_compose_mix)
    by (metis combStreamCases_def combStreamCases_h.simps(2) combstreamcases_insert)

  then have 2: "... = smap (Timed o TLive o (inv (Timed o TLive)))\<cdot>(f c)"
    using smapsmap2smap by blast

  then have "sValues\<cdot>(f c) \<subseteq> range (Timed o TLive)"
    by (simp add: TTLive assms ctype_def image_subsetI sbwellD)

  then show ?thesis
    by (simp add: 1 2)
next
  case TTsyn
  then have 1: "combined2mstream\<cdot>(sblegacy2new f c) = (smap (Timed o Tsyn))\<cdot>(smap (inv (Timed o Tsyn))\<cdot>(f c))"
    apply(simp add: combined2mstream_def combStreamCases_def sblegacy2new_def cont_compose_mix)
    by (metis combStreamCases_def combStreamCases_h.simps(5) combstreamcases_insert)

  then have 2: "... = smap (Timed o Tsyn o (inv (Timed o Tsyn)))\<cdot>(f c)"
    using smapsmap2smap by blast

  then have "sValues\<cdot>(f c) \<subseteq> range (Timed o Tsyn)"
    by (simp add: TTsyn assms ctype_def image_subsetI sbwellD)

  then show ?thesis
    by (simp add: 1 2)
qed

lemma
  Abs_lsb_inverse_h:
  assumes "lsb_well f"
  shows "Rep_lsb (Abs_lsb f) = f"
  apply(simp add: Rep_lsb_def Abs_lsb_def Abs_sb_inverse assms legacy2new_well)
  unfolding sbnew2legacy_def
  using Abs_lsb_inverse_h_h assms by blast

lemma rep_lsb_cont: "cont Rep_lsb"
  unfolding Rep_lsb_def sbnew2legacy_def
  apply(intro cont2cont)
  by (simp add: cont2cont_fun cont_Rep_sb)


lemma
  below_lsb_def_h1:
  assumes "Rep_sb x \<sqsubseteq> Rep_sb y"
  shows "Rep_lsb x \<sqsubseteq> Rep_lsb y"
  by (simp add: Rep_lsb_def assms cont2monofunE sbnew2legacy_cont)

lemma
  below_lsb_def_h2_h:
  assumes "Rep_lsb x \<sqsubseteq> Rep_lsb y"
  shows "Rep_sb x c \<sqsubseteq> Rep_sb y c"
proof -
  have exp_assms: "combined2mstream\<cdot>((Rep_sb x) c) \<sqsubseteq> combined2mstream\<cdot>((Rep_sb y) c)"
    by (metis Rep_lsb_def assms fun_belowD sbnew2legacy_def)

  show ?thesis
  proof (cases "Rep_sb x c")
    case (UNTIMED a)

    obtain b where b: "(Rep_sb y) c = UNTIMED b"
      apply (cases "(Rep_sb y) c"; simp add: combined2mstream_def combstreamcases_insert)
         apply (metis UNTIMED rep_event rep_untimed timeType.case(1) timeType.case(4))
        apply (metis UNTIMED rep_list rep_untimed timeType.case(1) timeType.case(3))
       apply (metis UNTIMED rep_tone rep_untimed timeType.case(1) timeType.case(2))
      by (metis UNTIMED rep_tsyn rep_untimed timeType.case(1) timeType.case(5))

    have "smap Untimed\<cdot>a \<sqsubseteq> smap Untimed\<cdot>b"
      by (metis UNTIMED b combined2mstream_def combStreamCases_h.simps(1) combstreamcases_insert exp_assms)
    then have "smap ((inv Untimed) o Untimed)\<cdot>a \<sqsubseteq> smap ((inv Untimed) o Untimed)\<cdot>b"
      by (metis monofun_cfun_arg smapsmap2smap)
    then show "Rep_sb x c \<sqsubseteq> Rep_sb y c"
      by (simp add: UNTIMED b)
  next
    case (TEVENT a)

    obtain b where b: "(Rep_sb y) c = TEVENT b"
      apply (cases "(Rep_sb y) c"; simp add: combined2mstream_def combstreamcases_insert)
         apply (metis TEVENT rep_untimed rep_event timeType.case(1) timeType.case(4))
        apply (metis TEVENT rep_list rep_event timeType.case(4) timeType.case(3))
       apply (metis TEVENT rep_tone rep_event timeType.case(4) timeType.case(2))
      by (metis TEVENT rep_tsyn rep_event timeType.case(4) timeType.case(5))

    have "smap (Timed o TLive)\<cdot>a \<sqsubseteq> smap (Timed o TLive)\<cdot>b"
      by (metis TEVENT b combined2mstream_def combStreamCases_h.simps(2) combstreamcases_insert exp_assms)
    then have "smap ((inv (Timed o TLive)) o (Timed o TLive))\<cdot>a \<sqsubseteq> smap ((inv (Timed o TLive)) o (Timed o TLive))\<cdot>b"
      by (metis monofun_cfun_arg smapsmap2smap)
    then show "Rep_sb x c \<sqsubseteq> Rep_sb y c"
      by (simp add: TEVENT b inj_compose)
  next
    case (TSLICED a)
    obtain b where b: "(Rep_sb y) c = TSLICED b"
      apply (cases "(Rep_sb y) c"; simp add: combined2mstream_def combstreamcases_insert)
         apply (metis TSLICED rep_list rep_untimed timeType.distinct(3))
        apply (metis TSLICED rep_event rep_list timeType.distinct(15))
       apply (metis TSLICED rep_list rep_tone timeType.distinct(9))
      by (metis TSLICED rep_list rep_tsyn timeType.distinct(17))

    have "smap (Timed o TFin)\<cdot>a \<sqsubseteq> smap (Timed o TFin)\<cdot>b"
      by (metis TSLICED b combined2mstream_def combStreamCases_h.simps(3) combstreamcases_insert exp_assms)
    then have "smap ((inv (Timed o TFin)) o (Timed o TFin))\<cdot>a \<sqsubseteq> smap ((inv (Timed o TFin)) o (Timed o TFin))\<cdot>b"
      by (metis monofun_cfun_arg smapsmap2smap)
    then show "Rep_sb x c \<sqsubseteq> Rep_sb y c"
      by (simp add: TSLICED b inj_compose)
  next
    case (TONE a)
    obtain b where b: "(Rep_sb y) c = TONE b"
      apply (cases "(Rep_sb y) c"; simp add: combined2mstream_def combstreamcases_insert)
         apply (metis TONE rep_tone rep_untimed timeType.distinct(1))
        apply (metis TONE rep_event rep_tone timeType.distinct(11))
       apply (metis TONE rep_list rep_tone timeType.simps(10))
      by (metis TONE rep_tone rep_tsyn timeType.distinct(13))

    have "smap (Timed o TOne )\<cdot>a \<sqsubseteq> smap (Timed o TOne )\<cdot>b"
      by (metis TONE b combined2mstream_def combStreamCases_h.simps(4) combstreamcases_insert exp_assms)
    then have "smap ((inv (Timed o TOne)) o (Timed o TOne ))\<cdot>a
          \<sqsubseteq> smap ((inv (Timed o TOne)) o (Timed o TOne ))\<cdot>b"
      by (metis monofun_cfun_arg smapsmap2smap)
    also have "(inv (Timed o TOne )) o (Timed o TOne ) = id"
      by auto
    finally show "Rep_sb x c \<sqsubseteq> Rep_sb y c"
      by (simp add: TONE b inj_compose)
  next
    case (TSYN a)

    obtain b where b: "(Rep_sb y) c = TSYN b"
      apply (cases "(Rep_sb y) c"; simp add: combined2mstream_def combstreamcases_insert)
         apply (metis TSYN rep_tsyn rep_untimed timeType.distinct(7))
        apply (metis TSYN rep_event rep_tsyn timeType.distinct(19))
       apply (metis TSYN rep_list rep_tsyn timeType.distinct(17))
      by (metis TSYN rep_tone rep_tsyn timeType.simps(14))

    have "smap (Timed o Tsyn)\<cdot>a \<sqsubseteq> smap (Timed o Tsyn)\<cdot>b"
      by (metis TSYN b combined2mstream_def combStreamCases_h.simps(5) combstreamcases_insert exp_assms)
    then have "smap ((inv (Timed o Tsyn)) o (Timed o Tsyn))\<cdot>a \<sqsubseteq> smap ((inv (Timed o Tsyn)) o (Timed o Tsyn))\<cdot>b"
      by (metis monofun_cfun_arg smapsmap2smap)
    then show "Rep_sb x c \<sqsubseteq> Rep_sb y c"
      by (simp add: TSYN b inj_compose)
  qed
qed

lemma below_lsb_def_h2:
  assumes "Rep_lsb x \<sqsubseteq> Rep_lsb y"
  shows "Rep_sb x \<sqsubseteq> Rep_sb y"
  by (simp add: assms below_lsb_def_h2_h fun_belowI)

lemma below_lsb_def_h: "(Rep_sb x \<sqsubseteq> Rep_sb y) = (Rep_lsb x \<sqsubseteq> Rep_lsb y)"
  using below_lsb_def_h1 below_lsb_def_h2 by blast

lemma below_lsb_def: "(\<sqsubseteq>) \<equiv> \<lambda>x y. Rep_lsb x \<sqsubseteq> Rep_lsb y"
  by(simp add: below_sb_def below_lsb_def_h)

lemma
  Abs_lsb_cases_h:
  assumes "(\<And>y. x = Abs_lsb y \<Longrightarrow> y \<in> {f. lsb_well f} \<Longrightarrow> P)"
  shows "(\<And>y. x = Abs_sb y \<Longrightarrow> y \<in> {f. sb_well f} \<Longrightarrow> P)"
  by (metis
      Abs_lsb_def
      Abs_lsb_inverse_h
      Abs_sb_inverse
      Rep_lsb_def
      assms
      below_antisym
      below_lsb_def_h2
      below_refl
      legacy2new_well
      mem_Collect_eq
      new2legacy_well
  )

lemma Abs_lsb_cases: "(\<And>y. x = Abs_lsb y \<Longrightarrow> y \<in> {f. lsb_well f} \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis Abs_lsb_cases_h Abs_sb_cases)

lemma Abs_lsb_induct: "(\<And>y. y \<in> {f. lsb_well f} \<Longrightarrow> (P) (Abs_lsb y)) \<Longrightarrow> P x"
  by (metis Abs_lsb_cases)

lemma Abs_lsb_strict: "Abs_lsb \<bottom> = \<bottom>"
  by (metis
      Abs_cfun_inverse2
      Abs_lsb_cases
      Abs_lsb_inverse_h
      lambda_strict
      mem_Collect_eq
      rep_lsb_cont
      sbwell_ex
      strictI
  )

lemma Rep_lsb: "Rep_lsb (x) \<in> {f. lsb_well f}"
  by (metis Abs_lsb_cases Abs_lsb_inverse_h mem_Collect_eq)

lemma Abs_lsb_inject:"
    (x) \<in> {f. lsb_well f} \<Longrightarrow>
    (y) \<in> {f. lsb_well f} \<Longrightarrow> (Abs_lsb x = Abs_lsb y) = (x = y)"
  by (metis Abs_lsb_inverse_h mem_Collect_eq)

lemma Abs_lsb_inverse[simp]: "(y) \<in> {f. lsb_well f} \<Longrightarrow> Rep_lsb (Abs_lsb y) = y"
  by (simp add: Abs_lsb_inverse_h)

lemma Rep_lsb_cases:
    "(y) \<in> {f. lsb_well f} \<Longrightarrow> (\<And>x. y = Rep_lsb x \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis Abs_lsb_inverse)

lemma Rep_lsb_induct:
    "(y) \<in> {f. lsb_well f} \<Longrightarrow>
    (\<And>x. (P) (Rep_lsb x)) \<Longrightarrow> P y"
  by (metis Rep_lsb_cases)

lemma Rep_lsb_inject: "(Rep_lsb (x) = Rep_lsb (y)) = (x = y)"
  by (metis Abs_lsb_cases Abs_lsb_inverse)

lemma Rep_lsb_inverse: "Abs_lsb (Rep_lsb (x)) = x"
  using Abs_lsb_inverse Rep_lsb Rep_lsb_inject by blast

lemma adm_lsb: "adm (\<lambda>x. x \<in> {f. lsb_well f})"
  using sbwell_adm by auto

lemma compact_lsb: "compact (Rep_lsb (k)) \<Longrightarrow> compact k"
  oops

lemma Abs_lsb_bottom_iff: "(x) \<in> {f. lsb_well f} \<Longrightarrow> (Abs_lsb x = \<bottom>) = (x = \<bottom>)"
  by (metis Abs_lsb_inverse Abs_lsb_inverse_h Abs_lsb_strict lambda_strict sbwell_ex)

lemma Rep_lsb_bottom_iff: "(Rep_lsb (x) = \<bottom>) = (x = \<bottom>)"
  by (metis Abs_lsb_bottom_iff Rep_lsb Rep_lsb_inverse)

lemma Rep_lsb_strict: "Rep_lsb \<bottom> = \<bottom>"
  by (simp add: Rep_lsb_bottom_iff)

lemma cont_Abs_lsb:
  assumes "(\<And>x. (f) x \<in> {f. lsb_well f})"
    and "cont f"
  shows "cont (\<lambda>x. Abs_lsb (f x))"
  apply(simp add: Abs_lsb_def)
  apply(rule cont_Abs_sb)
  using assms(1) legacy2new_well apply blast
  using assms(2) cont_compose sblegacy2new_cont by blast

lemma cont_Rep_lsb: "cont (f) \<Longrightarrow> cont (\<lambda>x. Rep_lsb (f x))"
  using cont_compose rep_lsb_cont by blast

lemma lub_lsb: "chain (S) \<Longrightarrow> Lub S = Abs_lsb (\<Squnion>i::nat. Rep_lsb (S i))"
  by (metis (full_types) Rep_lsb_inverse cont2contlubE rep_lsb_cont)

lemma type_definition_lsb: "type_definition Rep_lsb Abs_lsb {f. lsb_well f}"
  apply(auto simp add: type_definition_def)
  using Rep_lsb apply blast
  using Rep_lsb_inverse by auto

setup_lifting %invisible type_definition_lsb

declare %invisible Abs_sb_inverse [simp]


paragraph \<open>SB Type Properties \\\<close>


theorem bot_sb: "\<bottom> = Abs_lsb (\<lambda>c. \<epsilon>)"
  by (simp add: Abs_lsb_strict lambda_strict)

lemma rep_sb_well[simp]:"lsb_well(Rep_lsb sb)"
  using Rep_lsb by auto

lemma abs_rep_sb_sb[simp]:"Abs_lsb(Rep_lsb sb) = sb"
  using Rep_lsb_inverse by auto

lemma sbrep_cont[simp, cont2cont]: "cont Rep_lsb"
  using cont_Rep_lsb cont_id by blast

lemma sb_rep_abs: "lsb_well sb \<Longrightarrow> Rep_lsb(Abs_lsb sb) = sb"
  by (metis Abs_lsb_inverse mem_Collect_eq)

lemma sb_abs_cont2cont [cont2cont]: 
  assumes "cont h" 
  and "\<And>x. lsb_well (h x)"
  shows "cont (\<lambda>x. Abs_lsb (h x))"
  by (simp add: assms(1) assms(2) cont_Abs_lsb)

lemma comp_abs_cont[cont2cont]:
  assumes"\<And>x. lsb_well (f2 x)"
  and "cont f2"
  shows "cont (Abs_lsb \<circ> f2)"
  apply(rule Cpo.contI,simp)
  using assms cont_Abs_lsb cont_def by force

lemma sb_rep_eqI:assumes"\<And>c. (Rep_lsb sb1) c = (Rep_lsb sb2) c"
  shows "sb1 = sb2"
  by(simp add: po_eq_conv below_lsb_def fun_belowI assms)


theorem sbtypeepmpty_sbbot[simp]:
  fixes sb::"'cs\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE ('cs)" 
  shows "sb = \<bottom>"
  apply(rule sb_rep_eqI)
  unfolding bot_sb
  apply(insert lsb_well_def[of "Rep_lsb sb"],auto)
  using strict_sValues_rev assms by fastforce

lemma sbwell2fwell[simp]:"Rep_lsb sb = f \<Longrightarrow> lsb_well f"
  using Rep_lsb by auto

                                                    text\<open>\label{sub:sbfun}\<close>



text\<open>First we construct a converter from @{type sbElem}s to 
\Gls{sb}. This is rather straight forward, since we either have a 
function from channels to messages, which we can easily convert to a
function from channels to streams. This consists only of streams 
with the exact message from the @{type sbElem}. In the case of an 
empty domain, we map @{const None} to the \<open>\<bottom>\<close> element of \Gls{sb}.\<close> 

lift_definition sbe2sb::"'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega>" is
"\<lambda> sbe. case (Rep_sbElem sbe) of Some f \<Rightarrow> \<lambda>c. \<up>(f c)
                                | None  \<Rightarrow> \<bottom>"
  apply(rule lsbwellI, auto)
  apply(case_tac "Rep_sbElem sbElem = None")
  apply auto[2]
  apply(subgoal_tac "sbElem_well (Some y)",simp)
  by(simp only: sbelemwell2fwell)



text\<open>The direct access to a stream on a specific channel is one of
the most important functions in the framework and also 
often used for verifying properties. Intuitively, the signature of
such a function should be \<open>'cs \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> M stream \<close>, but we use a 
slightly more general signature. Two domain types could contain
exactly the same channels, but we could not obtain the streams of a
\gls{sb} with the intuitive signature, when the type of the \gls{sb}
is different (see \cref{sec:interdom}). To avoid this, we can use the
@{const Rep} and @{const Abs} functions of our domain types to 
convert between the them by representation and abstraction via the
global channel type. This also facilitates later function
definitions and reduces the total framework size by using
abbreviations of one general function that only restrict the
signature.\<close>

lift_definition sbGetCh :: "'cs1 \<Rightarrow> 'cs2\<^sup>\<Omega> \<rightarrow> M stream" is
"\<lambda>c sb. if Rep c\<in>chDom TYPE('cs2) 
            then Rep_lsb sb (Abs(Rep c)) 
            else \<epsilon>"
  by(intro cont2cont,simp add: cont2cont_fun)

text\<open>Our general signature allows the input of any channel from the
@{type channel} type. If the channel is in the domain of the input
\gls{sb}, we obtain the corresponding channel by converting the
channel to an element of our domain type with the nesting of \<open>Abs\<close> 
and \<open>Rep\<close>. Is the channel not in the domain, the empty stream \<open>\<epsilon>\<close> 
is returned. The continuity of this function is also immediately
proven.\<close> 

lemmas sbgetch_insert = sbGetCh.rep_eq

text\<open>The next abbreviations are defined to differentiate between the
intuitive and the expanded signature of @{const sbGetCh}. The first 
abbreviation is an abbreviation for the general signature, the 
second restricts to the intuitive signature.\<close>

abbreviation sbgetch_magic_abbr :: "'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2 \<Rightarrow> M stream"
(infix " \<^enum>\<^sub>\<star> " 65) where "sb \<^enum>\<^sub>\<star> c \<equiv> sbGetCh c\<cdot>sb"


abbreviation sbgetch_abbr :: "'cs\<^sup>\<Omega> \<Rightarrow> 'cs \<Rightarrow> M stream"
(infix " \<^enum> " 65) where "sb \<^enum> c \<equiv> sbGetCh c\<cdot>sb"

text \<open>Obtaining a @{type sbElem} from a \gls{sb} is not always 
possible. If the domain of a bundle is not empty but there is an 
empty stream on a channel, the resulting @{type sbElem} could not 
map that channel to a message from the stream. Hence, no slice of 
such a \gls{sb} can be translated to a @{type sbElem}. The following
predicate states, that the first slice of an \gls{sb} with a 
non-empty domain can be transformed to a @{type sbElem}, because it 
checks, if all streams in the bundle are not empty.\<close>

definition sbHdElemWell::"'c\<^sup>\<Omega> \<Rightarrow> bool" where
"sbHdElemWell  \<equiv> \<lambda> sb. (\<forall>c. sb  \<^enum>  c \<noteq> \<epsilon>)"  


abbreviation sbIsLeast::"'cs\<^sup>\<Omega> \<Rightarrow> bool" where
"sbIsLeast sb \<equiv> \<not>sbHdElemWell sb"

text\<open>The negation of this property is called @{const sbIsLeast}, 
because these \Gls{sb} do not contain any complete slices.\<close>


text\<open>When using the intuitive variant of @{const sbGetCh}, it
obtains a stream from a channel. It should never be able to do
anything else. This behavior is verified by the following theorem.
Obtaining a stream from its \gls{sb} is the same as obtaining the 
output from the function realizing the \gls{sb}.\<close>

theorem sbgetch_insert2:"sb \<^enum> c = (Rep_lsb sb) c"
  apply(simp add: sbgetch_insert)
  by (metis (full_types)Rep_lsb_strict app_strict cnotempty_cdom 
      sbtypeepmpty_sbbot)

lemma sbgetch_empty[simp]: fixes sb::"'cs\<^sup>\<Omega>"
    assumes "Rep c \<notin> chDom TYPE('cs)"
    shows "sb \<^enum>\<^sub>\<star> c = \<epsilon>"
  by(simp add: sbgetch_insert assms)

lemma sbhdelemchain[simp]:
  "sbHdElemWell x \<Longrightarrow>  x \<sqsubseteq> y \<Longrightarrow> sbHdElemWell y"
  apply(simp add: sbHdElemWell_def sbgetch_insert2)
  by (metis below_antisym below_lsb_def fun_belowD minimal)

lemma sbgetch_ctypewell[simp]:"sValues\<cdot>(sb \<^enum>\<^sub>\<star> c) \<subseteq> ctype (Rep c)"
  apply(simp add: sbgetch_insert)
  by (simp add: sbwellD)


lemma sbmap_well:assumes"\<And>s. sValues\<cdot>(f s) \<subseteq> sValues\<cdot>s" 
                 shows"lsb_well (\<lambda>c. f (b \<^enum>\<^sub>\<star> c))"
  apply(rule lsbwellI)
  using assms sbgetch_ctypewell by fastforce

lemma sbgetch_ctype_notempty:"sb  \<^enum>\<^sub>\<star>  c \<noteq> \<epsilon> \<Longrightarrow> ctype (Rep c) \<noteq> {}"
proof-
  assume a1: "sb  \<^enum>\<^sub>\<star>  c \<noteq> \<epsilon>"
  then have "\<exists>e. e\<in> sValues\<cdot>(sb  \<^enum>\<^sub>\<star>  c)"
    by (simp add: sValues_notempty strict_sValues_rev neq_emptyD)
  then show "ctype (Rep c) \<noteq> {}"
    using sbgetch_ctypewell by blast
qed

lemma sbgetch_well[simp]:"lsb_well (( \<^enum>\<^sub>\<star> ) sb)"
  apply(rule lsbwellI)
  by(simp)

lemma sbhdelemnotempty:
  "sbHdElemWell (sb::'cs\<^sup>\<Omega>) \<Longrightarrow>  \<not> chDomEmpty TYPE('cs)"
  by(auto simp add: sbHdElemWell_def chDom_def cEmpty_def)

lemma sbgetch_empty2: fixes sb::"'cs\<^sup>\<Omega>"
  assumes "chDomEmpty (TYPE ('cs))"
  shows "sb \<^enum>\<^sub>\<star> c = \<epsilon>"
  by(simp add: sbgetch_insert assms)

lemma sbempt2least: fixes sb::"'cs\<^sup>\<Omega>"
  assumes "chDomEmpty (TYPE ('cs))"
  shows  "sbIsLeast sb"
  unfolding sbHdElemWell_def
  apply simp
  by(rule exI [where x="undefined"], simp add: assms)

lemma sbbot_getch: "sb \<noteq> \<bottom> \<longleftrightarrow> (\<exists>c. sb \<^enum> c \<noteq> \<epsilon>)"
  apply (rule iffI)
  apply (metis sb_rep_eqI sbgetch_insert2 strictI)
  by (metis Rep_lsb_strict app_strict sbgetch_insert2)

lemma sbleast2bot[simp]:
  fixes sb::"'cs\<^sup>\<Omega>"
  assumes"is_singleton(chDom TYPE('cs))"
  and "sbIsLeast sb"
shows "sb = \<bottom>"
proof(rule ccontr)
  assume "sb \<noteq> \<bottom>"
  hence "\<exists>c. sb \<^enum> c \<noteq> \<epsilon>"
    using sbbot_getch by blast
  moreover have "\<exists>c. sb \<^enum> c = \<epsilon>"
    using assms(2) by (simp add: sbHdElemWell_def)
  moreover have "\<And>c1 c2::'cs. c1 = c2"
    by(rule chan_single_eq, simp add: assms(1))
  thus False
    by (metis(full_types) calculation(1) calculation(2)) 
qed


theorem sbgetch_sbelow[simp]:"sb1 \<sqsubseteq> sb2 \<Longrightarrow> sb1 \<^enum> c \<sqsubseteq> sb2 \<^enum> c"
  by (simp add: mono_slen monofun_cfun_arg)

lemma sbgetch_below_slen[simp]:
  "sb1 \<sqsubseteq> sb2 \<Longrightarrow> #(sb1 \<^enum>\<^sub>\<star> c) \<le> #(sb2 \<^enum>\<^sub>\<star> c)"
  by (simp add: mono_slen monofun_cfun_arg)

lemma sbgetch_bot[simp]:"\<bottom> \<^enum>\<^sub>\<star> c = \<epsilon>"
  by(simp add: sbGetCh.rep_eq bot_sb)

lemma echan_svalues:
  fixes sb :: "('a::echan)\<^sup>\<Omega>"
  shows "\<And>c. Rep c \<in> chDom TYPE('a) \<Longrightarrow> sValues\<cdot>(sb \<^enum> c) \<subseteq> range (Timed \<circ> TLive)"
  by (metis ctype_echan_def emptyE sbgetch_ctypewell subset_UNIV subset_image_iff)


theorem sb_belowI:
  fixes   sb1 sb2::"'cs\<^sup>\<Omega>"
  assumes "\<And> c. Rep c\<in>chDom TYPE('cs) \<Longrightarrow>  sb1 \<^enum> c \<sqsubseteq> sb2 \<^enum> c"
  shows   "sb1 \<sqsubseteq> sb2"
  apply(subst below_lsb_def)
  apply(rule fun_belowI)
  by (metis (full_types) assms  po_eq_conv sbGetCh.rep_eq 
      sbgetch_insert2)

lemma sb_belowI2:
  fixes   sb1 sb2::"'cs\<^sup>\<Omega>"
  assumes "\<And>c. chDom TYPE('cs) \<noteq> {} \<Longrightarrow> c\<in>Abs`chDom TYPE('cs) \<Longrightarrow> sb1 \<^enum> c \<sqsubseteq> sb2 \<^enum> c"
  shows   "sb1 \<sqsubseteq> sb2"
  apply(rule sb_belowI)
  using assms by fastforce

lemma monofun_spf_arg: 
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
assumes "\<And>c. Rep c \<in> chDom TYPE('cs) \<Longrightarrow> sb1 \<^enum> c \<sqsubseteq> sb2 \<^enum> c"
  shows "f\<cdot>sb1  \<^enum>\<^sub>\<star>  c \<sqsubseteq> f\<cdot>sb2  \<^enum>\<^sub>\<star>  c"
  using assms by (meson monofun_cfun_arg sb_belowI)

lemma sbgetch_iterate_below_fix: "iterate n\<cdot>F\<cdot>\<bottom>  \<^enum>\<^sub>\<star>  c \<sqsubseteq> fix\<cdot>F  \<^enum>\<^sub>\<star>  c"
  by (simp add: iterate_below_fix monofun_cfun_arg)


theorem sb_eqI:
  fixes   sb1 sb2::"'cs\<^sup>\<Omega>"
  assumes "\<And>c. Rep c\<in>chDom TYPE('cs) \<Longrightarrow> sb1 \<^enum> c = sb2 \<^enum> c"
  shows   "sb1 = sb2"
  apply(cases "chDom TYPE('cs) \<noteq> {}")
  apply(metis Diff_eq_empty_iff Diff_triv assms chDom_def 
        chan_botsingle rangeI sb_rep_eqI sbgetch_insert2)
  by (metis (full_types) sbtypeepmpty_sbbot)

lemma sb_eqI2:
  fixes   sb1 sb2::"'cs\<^sup>\<Omega>"
  assumes "\<And>c. chDom TYPE('cs) \<noteq> {} \<Longrightarrow> c\<in>Abs`chDom TYPE('cs) \<Longrightarrow> sb1 \<^enum> c = sb2 \<^enum> c"
  shows   "sb1 = sb2"
  apply(rule sb_eqI)
  using assms by fastforce

lemma shd2sbe[simp]:"chDom TYPE('cs) \<noteq> {} \<Longrightarrow> 
        Some (\<lambda>c::'cs. shd ((sbe2sb sbe  \<^enum>  c) \<Zcat> (sb \<^enum> c))) = Rep_sbElem sbe"
  apply(rule some_eqI,simp)
  apply(simp add: sbgetch_insert2 sbe2sb.rep_eq)
  by(subst option.case_eq_if,simp)

lemma shd2sbe2[simp]:"chDom TYPE('cs) \<noteq> {} \<Longrightarrow> 
        Some (\<lambda>c::'cs. shd ((sbe2sb sbe  \<^enum>  c))) = Rep_sbElem sbe"
  using shd2sbe[of sbe \<bottom>] by simp


lemma sb_empty_eq[simp]: fixes sb1 sb2::"'cs\<^sup>\<Omega>"
  assumes  "chDomEmpty TYPE('cs)"
  shows "sb1 = sb2"
  by(rule sb_eqI, simp add: assms)

lemma slen_empty_eq:  assumes"chDomEmpty(TYPE('c))"
  shows " #(sb \<^enum> (c::'c)) =0"
  using assms chDom_def cEmpty_def sbgetch_ctype_notempty 
  by fastforce

text\<open>Lastly, the conversion from a @{type sbElem} to a \gls{sb}
should never result in a \gls{sb} which maps its domain to \<open>\<epsilon>\<close>.\<close>

theorem sbgetch_sbe2sb_nempty:
  fixes   sbe::"'cs\<^sup>\<surd>"
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows   "sbe2sb sbe  \<^enum>  c \<noteq> \<epsilon>"
  apply (simp add: sbe2sb.rep_eq sbgetch_insert2)
  apply (simp split: option.split) 
  using assms chDom_def sbElem_well.simps(1) sbelemwell2fwell 
  by blast
 
lemma sbe2sb_getch: 
  fixes   sbe :: "'a\<^sup>\<surd>"
  assumes "Rep c \<in> chDom TYPE('a)"
  shows "(sbe2sb sbe)  \<^enum>\<^sub>\<star>  c = \<up>(sbegetch c sbe)"
  apply (simp add: sbgetch_insert sbe2sb.rep_eq)
  apply (subst option.case_eq_if)
  apply (simp add: sbe_emptyiff sbegetch_insert assms)
  using assms by blast

lemma botsbleast[simp]:"sbIsLeast \<bottom>"
  by(simp add: sbHdElemWell_def)

lemma sbleast_mono[simp]:"x \<sqsubseteq> y \<Longrightarrow> \<not>sbIsLeast x \<Longrightarrow> \<not> sbIsLeast y"
  by simp

lemma sbnleast_mex:"\<not>sbIsLeast x \<Longrightarrow> x \<^enum> c \<noteq> \<epsilon>"
  by(simp add: sbHdElemWell_def)

lemma sbnleast_mexs[simp]:"\<not>sbIsLeast x \<Longrightarrow> \<exists>a s. x \<^enum> c = \<up>a \<Zcat> s"
  using sbnleast_mex scases by blast

lemma sbnleast_hdctype[simp]:
"\<not>sbIsLeast x \<Longrightarrow> \<forall>c. shd (x \<^enum> c) \<in> ctype (Rep c)"
  apply auto[1]
  apply(subgoal_tac "shd (x \<^enum> c) \<in> sValues\<cdot>(x \<^enum> c)")
  using sbgetch_ctypewell apply blast
  by(case_tac "x \<^enum> c";simp_all add: sbHdElemWell_def)

lemma sbgetchid[simp]:"Abs_lsb (( \<^enum> ) (x)) = x"
  by(simp add: sbgetch_insert2)


paragraph\<open>Bundle Equality \\\<close> text\<open>\label{par:bundleeq}\<close>


definition sbEQ::"'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> bool" where 
"sbEQ sb1 sb2 \<equiv> chDom TYPE('cs1) = chDom TYPE('cs2) \<and>
                (\<forall>c. sb1 \<^enum> c = sb2 \<^enum>\<^sub>\<star> c)"


abbreviation sbeq_abbr :: "'cs1\<^sup>\<Omega>  \<Rightarrow>  'cs2\<^sup>\<Omega> \<Rightarrow>  bool"
(infixr "\<triangleq>" 70) where "sb1 \<triangleq> sb2 \<equiv> sbEQ sb1 sb2"

lemma sbeq_refl: "sb \<triangleq> sb" by(simp add: sbEQ_def)

lemma sbeq_symmetric:
  fixes   sb1::"'cs1\<^sup>\<Omega>"
  fixes   sb2::"'cs2\<^sup>\<Omega>"
  assumes "sb1 \<triangleq> sb2"
  shows "sb2 \<triangleq> sb1"
  apply(simp add: sbEQ_def)
proof
  show "chDom TYPE('cs2) = chDom TYPE('cs1)" using assms by (simp add: sbEQ_def)
next
  show "\<forall>c::'cs2. sb2  \<^enum>  c = sb1  \<^enum>\<^sub>\<star>  c" using assms
    apply(auto simp add: sbEQ_def)[1]
    by (metis (mono_tags, lifting) rep_reduction sbgetch_insert)
qed

lemma sbeq_trans:
  fixes   sb1::"'cs1\<^sup>\<Omega>"
  fixes   sb2::"'cs2\<^sup>\<Omega>"
  fixes   sb3::"'cs3\<^sup>\<Omega>"
  assumes "sb1 \<triangleq> sb2" and "sb2 \<triangleq> sb3"
  shows "sb1 \<triangleq> sb3"
  using assms apply(auto simp add: sbEQ_def assms)[1]
proof -
  fix c :: 'cs1
  assume a1: "chDom (TYPE('cs2)::'cs2 itself) = chDom (TYPE('cs3)::'cs3 itself)"
  assume "\<forall>c. sb2 \<^enum> c = sb3 \<^enum>\<^sub>\<star> c"
  then have "\<forall>c. Rep_lsb sb3 (Abs c) = Rep_lsb sb2 (Abs c) \<or> c \<notin> chDom (TYPE('cs3)::'cs3 itself)"
    using a1 by (metis (full_types) rep_reduction sbgetch_insert)
  then have "Rep c \<in> chDom (TYPE('cs3)::'cs3 itself) \<longrightarrow> sb2 \<^enum>\<^sub>\<star> c = sb3 \<^enum>\<^sub>\<star> c"
    using a1 by (metis (full_types) sbgetch_insert)
  then show "sb2 \<^enum>\<^sub>\<star> c = sb3 \<^enum>\<^sub>\<star> c"
    using a1 by (metis sbgetch_insert)
qed

lemma sbeq_smallest:
  fixes   sb1::"'cs1\<^sup>\<Omega>"
  fixes   sb2::"'cs2\<^sup>\<Omega>"
  shows "\<not>(chDom TYPE('cs1) = chDom TYPE('cs2)) \<or> \<not>(\<forall>c. sb1 \<^enum> c = sb2 \<^enum>\<^sub>\<star> c) \<Longrightarrow> \<not>(sb1 \<triangleq> sb2)"
  by (simp add: sbEQ_def)

lemma sbeq_getch: assumes "sb1 \<triangleq> sb2"
  shows "sb1 \<^enum>\<^sub>\<star> c = sb2 \<^enum>\<^sub>\<star> c"
  apply(auto simp add: sbGetCh.rep_eq)[1]
  using assms apply(auto simp add: sbEQ_def)[3]
  by (metis(mono_tags) rep_reduction sbgetch_insert)

                                           text\<open>\label{subsub:sbconc}\<close>

text\<open>Concatenating two \Gls{sb} is equivalent to concatenating their 
streams whilst minding the channels. The output is also a \gls{sb},
because the values of both streams are in @{const ctype}, therefore,
the same holds for the union. The compatibility of the input bundles
is ensured by the signature of the function.\<close>

lemma sbconc_well[simp]:"lsb_well (\<lambda>c. (sb1 \<^enum> c) \<Zcat> (sb2 \<^enum> c))"
  apply(rule lsbwellI)
  by (metis (no_types, opaque_lifting) Un_subset_iff dual_order.trans 
      sbgetch_ctypewell sconc_sValues)

lift_definition sbConc:: "'cs\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" is
"\<lambda>sb1 sb2. Abs_lsb(\<lambda>c. (sb1 \<^enum> c) \<Zcat> (sb2 \<^enum> c))"
  by(intro cont2cont, simp)

lemmas sbconc_insert = sbConc.rep_eq


abbreviation sbConc_abbr :: "'cs\<^sup>\<Omega>  \<Rightarrow>  'cs\<^sup>\<Omega> \<Rightarrow>  'cs\<^sup>\<Omega>"
(infixr "\<Zcat>\<^sup>\<Omega>" 70) where "sb1 \<Zcat>\<^sup>\<Omega> sb2 \<equiv> sbConc sb1\<cdot>sb2"


theorem sbconc_getch [simp]: 
  shows "(sb1 \<Zcat>\<^sup>\<Omega> sb2)  \<^enum>\<^sub>\<star> c = (sb1 \<^enum>\<^sub>\<star> c) \<Zcat> (sb2 \<^enum>\<^sub>\<star> c)"
  unfolding sbgetch_insert sbconc_insert
  apply(subst Abs_lsb_inverse,simp)
  apply(rule lsbwellI)
  apply auto[2]
  by (metis (no_types, lifting) UnE in_mono sbgetch_ctypewell sbgetch_insert2 sconc_sValues)

text\<open>It works the same way with @{const Rep_lsb}.\<close>
lemma repsb_sbconc:"Rep_lsb (x \<Zcat>\<^sup>\<Omega> y) z = (Rep_lsb x z) \<Zcat> (Rep_lsb y z)"
  by (metis sbconc_getch sbgetch_insert2)


theorem sbconc_bot_r[simp]: "sb \<Zcat>\<^sup>\<Omega> \<bottom> = sb"
  by(rule sb_eqI, simp)

theorem sbconc_bot_l[simp]: "\<bottom> \<Zcat>\<^sup>\<Omega> sb = sb"
  by(rule sb_eqI, simp)

lemma sbconc_asso: "(sb1 \<Zcat>\<^sup>\<Omega> sb2) \<Zcat>\<^sup>\<Omega> sb3 = sb1 \<Zcat>\<^sup>\<Omega> (sb2 \<Zcat>\<^sup>\<Omega> sb3)"
  apply (rule sb_eqI)
  by simp
 
                                           text\<open>\label{subsub:sblen}\<close>

text\<open>We define the length of a \gls{sb} as
follows:
  \<^item> A \gls{sb} with an empty domain is infinitely long
  \<^item> A \gls{sb} with an non-empty domain is as long as its shortest 
    stream

The definition for the empty domain was designed with the timed case in mind.
This definition can be used to define causality.\<close>

definition sbLen::"'cs\<^sup>\<Omega> \<Rightarrow> lnat"where
"sbLen sb \<equiv> if chDomEmpty TYPE('cs) then \<infinity> 
                else LEAST n . n\<in>{#(sb \<^enum> c) | c. True}"

text\<open>Our @{const sbLen} function works exactly as described. It 
returns \<open>\<infinity>\<close>, if the domain is empty. Else it chooses the minimal 
length of all the bundles streams.\<close>


lemma sblen_empty'[simp]:
  fixes   sb::"'cs\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs)"
  shows   "sbLen sb = \<infinity>"
  by(simp add: sbLen_def assms slen_empty_eq)

lemma sblenleq': assumes "\<not> chDomEmpty TYPE('a)" and
 "\<exists>c::'a. #(sb\<^enum>c) \<le> k"
  shows "sbLen sb \<le> k" 
  apply(simp add: sbLen_def assms)
  apply(subgoal_tac "\<And>c::'a. Rep c \<notin> cEmpty") 
  apply auto[2]
  apply (metis (mono_tags, lifting) Least_le assms(2) 
         dual_order.trans)
  using assms(1) by simp

lemma sblengeq': 
  fixes sb::"'cs\<^sup>\<Omega>"
    assumes "\<And>c. (Rep c)\<in>chDom TYPE('cs) \<Longrightarrow> k\<le> #(sb\<^enum>c)"
  shows "k \<le> sbLen sb" 
  apply(cases  "chDomEmpty(TYPE('cs))",simp add: assms)
  apply(subgoal_tac "\<And>c.  k\<le> #(sb\<^enum>c)")
   apply(simp add: sbLen_def)
  apply(rule LeastI2_wellorder_ex)
  using assms chdom_in by blast+

lemma sblen_mono:"monofun sbLen"
  apply(rule monofunI,simp)
  apply(cases "chDomEmpty TYPE('a)",simp)
  apply(rule sblengeq')
  apply(rule sblenleq')
  using sbgetch_below_slen by auto

instantiation sb :: (chan) len
begin
definition len_sb::"'cs\<^sup>\<Omega> \<Rightarrow> lnat" where
"len_sb = sbLen"

instance
  apply(intro_classes)
  by (simp add: len_sb_def sblen_mono)

end

text \<open>The abbreviation \emph{\#} is a shortcut for @{const sbLen}.\<close>


lemma sblen_empty[simp]:
  fixes   sb::"'cs\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs)"
  shows   "#sb = \<infinity>"
  by(simp add: len_sb_def assms)

lemma sblenleq:
  assumes "\<not> chDomEmpty TYPE('a)" 
      and "\<exists>c::'a. #(sb\<^enum>c) \<le> k"
    shows "#sb \<le> k"
  by(simp add: len_sb_def assms sblenleq')

lemma sblengeq: assumes "\<And>c. k\<le> #(sb\<^enum>c)"
  shows "k \<le> #sb" 
  by(simp add: len_sb_def assms sblengeq')

lemma sblen_min_len [simp]:
  assumes"\<not>chDomEmpty(TYPE('c))"
  shows"# (sb :: 'c\<^sup>\<Omega>) \<le> #(sb \<^enum> c)"
  apply(simp add: len_sb_def sbLen_def assms)
  by (metis (mono_tags, lifting) Least_le)

lemma sblen_min_len2: fixes sb::"'cs\<^sup>\<Omega>"
  assumes "(Rep c)\<in>chDom TYPE('cs)"
  shows "#sb \<le> # (sb\<^enum>c)"
  apply(rule sblen_min_len)
  using assms by blast



theorem sblen_sbconc: "#sb1 + #sb2 \<le> #(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  apply(cases  "chDomEmpty(TYPE('a))",simp)
  apply(rule sblengeq)
  by (metis lessequal_addition sbconc_getch sblen_min_len 
      sconc_slen2)


lemma sblen_monosimp[simp]:"x \<sqsubseteq> y \<Longrightarrow> # x \<le> # y"
  by (simp add: len_class.mono_len)

text\<open>This rule captures all necessary assumptions to obtain the 
exact length of a \gls{sb} with a non-empty domain:
  \<^item> All streams must be at least equally long to the length of the 
    \gls{sb}
  \<^item> There exists a stream with length equal to the length of the 
    \gls{sb}\<close>

theorem sblen_rule:
  fixes sb::"'cs\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)" 
      and "\<And>c. k \<le> #(sb \<^enum> c)"
      and "\<exists>c. #(sb \<^enum> c) = k"
  shows   "#sb = k"
  by (metis assms(1) assms(2) assms(3) dual_order.antisym 
      sblen_min_len sblengeq)


theorem sblen_sbeqI:
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
  assumes "sb1\<sqsubseteq>sb2" and "#sb1 =\<infinity>"
  shows   "sb1 = sb2"
  apply(cases "chDomEmpty TYPE('cs)")
  apply (metis (full_types)sbtypeepmpty_sbbot)
using assms proof(simp add: len_sb_def sbLen_def)
  assume a1: "sb1 \<sqsubseteq> sb2"
  assume a2: "(LEAST n::lnat. \<exists>c::'cs. n = #(sb1  \<^enum>  c)) = \<infinity>"
  assume a3: "chDom TYPE('a) \<noteq> {}"
  then have "\<And>c. #(sb1 \<^enum> c) = \<infinity>"
    by (metis (mono_tags, lifting) Least_le a2 inf_less_eq)
  moreover have "\<And>c. #(sb2 \<^enum> c) = \<infinity>"
    using a1 calculation cont_pref_eq1I mono_fst_infD by blast
  then show ?thesis 
    apply(subst sb_eqI[of sb1 sb2],auto)
    by (simp add: a1 calculation cont_pref_eq1I eq_less_and_fst_inf)
qed

instance sb :: (chan) len_max
  apply(intro_classes)
  using sblen_sbeqI by auto

lemma sblen_leadm:
   fixes sb::"'cs\<^sup>\<Omega>"
   shows "adm (\<lambda>sb. k \<le> #sb)"
  apply(rule admI)
  using is_ub_thelub mono_len order_trans by blast


lemma sblen2slen_h:
  fixes "c1"
  assumes"\<not>chDomEmpty(TYPE('c))"
  and "\<forall>c2. #((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) \<le> #(sb \<^enum> c2)"
  shows "#((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) = #sb"
  apply(simp add: sbLen_def len_sb_def)
  apply(subst Least_equality)
  apply(simp_all add: assms)
   apply auto[1]
  using assms(2) by auto

lemma sb_minstream_exists:
  assumes "\<not>chDomEmpty(TYPE('c))"
  shows "\<exists>c1. \<forall>c2. #((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) \<le> #(sb \<^enum> c2)"
  using  assms
proof -
  { fix cc :: "'c \<Rightarrow> 'c"
    have ff1: "\<forall>s c l. l \<le> #(s \<^enum> (c::'c)) \<or> \<not> l \<le> #s"
      by (meson assms sblen_min_len trans_lnle)
    { assume "\<exists>c l. \<not> l \<le> #(sb \<^enum> c)"
      then have "\<not> \<infinity> \<le> #sb"
        using ff1 by (meson inf_ub trans_lnle)
      then have "\<exists>c. #(sb \<^enum> c) \<le> #(sb \<^enum> cc c)"
        using ff1 by (metis less_le_not_le ln_less 
                Orderings.linorder_class.linear lnle2le sblengeq) }
    then have "\<exists>c. #(sb \<^enum> c) \<le> #(sb \<^enum> cc c)"
      by meson }
  then show ?thesis
    by metis
qed


theorem sblen2slen:
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows "\<exists>c. #(sb :: 'cs\<^sup>\<Omega>) = #(sb \<^enum> c)"
proof -
  obtain min_c where "\<forall>c2. #((sb :: 'cs\<^sup>\<Omega>) \<^enum> min_c) \<le> #(sb \<^enum> c2)"
    using sb_minstream_exists assms by blast
  then have "#(sb :: 'cs\<^sup>\<Omega>) = #(sb \<^enum> min_c)" using sblen2slen_h
    using assms by fastforce
  then show ?thesis
    by auto 
qed

lemma sbconc_len_upper:
  assumes "chDom TYPE('cs) \<noteq> {}"
  assumes"\<And>c::'cs. #(sb1 \<^enum> c) \<le> l1"
  and "\<And>c. #(sb2 \<^enum> c) \<le> l2"
shows"#(sb1 \<Zcat>\<^sup>\<Omega> sb2) \<le> l1 + l2"
proof-
  obtain c where c_def:"#(sb1 \<Zcat>\<^sup>\<Omega> sb2) = #((sb1 \<^enum> c) \<Zcat> (sb2 \<^enum> c))"
    apply(subst(asm) sbconc_getch[symmetric])
    using sblen2slen[where sb="sb1 \<Zcat>\<^sup>\<Omega> sb2"] assms(1)by blast
  thus ?thesis
    apply(simp add: assms sconc_slen2) using assms(2,3)
    using lessequal_addition by blast
qed

lemma sbconc_len_finite:
assumes "chDom TYPE('cs) \<noteq> {}"
  assumes"\<And>c::'cs. #(sb1 \<^enum> c) <\<infinity>"
  and "\<And>c::'cs. #(sb2 \<^enum> c) < \<infinity>"
shows"#(sb1 \<Zcat>\<^sup>\<Omega> sb2) < \<infinity>"
proof-
  obtain c where c_def:"#(sb1 \<Zcat>\<^sup>\<Omega> sb2) = #((sb1 \<^enum> c) \<Zcat> (sb2 \<^enum> c))"
    apply(subst(asm) sbconc_getch[symmetric])
    using sblen2slen[where sb="sb1 \<Zcat>\<^sup>\<Omega> sb2"] assms(1) by blast
  thus ?thesis
    apply(simp add: assms sconc_slen2) using assms(2,3)
    by (metis c_def sconc_slen)
qed


lemma sbconc_chan_len:"#(sb1 \<Zcat>\<^sup>\<Omega> sb2 \<^enum> c) = #(sb1 \<^enum> c)+ #(sb2 \<^enum> c)"
  by (simp add: sconc_slen2)

lemma sblen_sbconc_eq: 
  assumes "\<And>c.#(sb1 \<^enum> c) = k" 
  shows "(#(sb1 \<Zcat>\<^sup>\<Omega> sb2)) = (#sb2) + k"
  apply(cases  "chDomEmpty(TYPE('a))",simp)
  apply(subgoal_tac "#sb1 = k")
  apply(rule sblen_rule,simp)
  apply (metis add.commute dual_order.trans sblen_min_len 
        sblen_sbconc)
  apply (metis assms lnat_plus_commu sbconc_chan_len sblen2slen)  
  by(rule sblen_rule,simp_all add: assms)

lemma sblen_sbconc_rule: 
  assumes "\<And>c.#(sb1 \<^enum> c) \<ge> k" 
  shows "(#(sb1 \<Zcat>\<^sup>\<Omega> sb2)) \<ge> (#sb2) + k"
  by (metis (full_types) add.commute assms dual_order.trans 
      lessequal_addition order_refl sblen_sbconc sblengeq)

text\<open>The length of a @{type sbElem} is 1, if the domain is not 
empty\<close>

theorem sbelen_one[simp]:
  fixes   sbe::"'cs\<^sup>\<surd>"
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows   " #(sbe2sb sbe) = 1"
proof-
  have "\<And>c. #(sbe2sb (sbe::'cs\<^sup>\<surd>) \<^enum> (c :: 'cs )) = 1"
    apply(simp add: sbe2sb_def)
    apply(subgoal_tac "Rep_sbElem sbe \<noteq> None")
    apply auto[1]
    apply(simp add: sbgetch_insert2)
    apply(subst Abs_lsb_inverse,auto)
    apply (metis (full_types) option.simps(5) sbe2sb.rep_eq 
          sbwell2fwell)
    apply (simp add: one_lnat_def; fail)
    by(simp add: assms)
  then show ?thesis
    apply(subst sblen_rule)
    by(simp_all add: assms)
qed

lemma sbe2slen_1:  assumes"\<not>chDomEmpty(TYPE('a))"
  shows  "\<And>c::'a. #(sbe2sb sbe  \<^enum>  c) = (1::lnat)"
    apply(simp add: sbe2sb_def)
    apply(subgoal_tac "Rep_sbElem sbe \<noteq> None")
    apply auto[1]
    apply(simp add: sbgetch_insert2)
    apply(subst Abs_lsb_inverse,auto)
    apply (metis (full_types) option.simps(5) sbe2sb.rep_eq 
           sbwell2fwell)
    apply (simp add: one_lnat_def; fail)
    by(simp add: assms)
 
lemma sbnleast_len[simp]:"\<not>sbIsLeast x \<Longrightarrow> #x \<noteq> 0"
  apply(rule ccontr,auto)
  apply(simp add: sbHdElemWell_def)
  apply(cases "chDomEmpty TYPE('a)",simp)
  by (metis Stream.slen_empty_eq sblen2slen)

lemma sblen_eqI2:
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
  assumes "sb1 \<sqsubseteq> sb2"
  and "\<And>c. Rep c\<in>chDom TYPE('cs) \<Longrightarrow> #(sb1 \<^enum> c) = #(sb2 \<^enum> c)"
  shows "sb1 = sb2"
  by (simp add: assms(1) assms(2) eq_slen_eq_and_less 
      monofun_cfun_arg sb_eqI)

lemma sbnleast_dom[simp]:
  "\<not>sbIsLeast (x::'cs\<^sup>\<Omega>) \<Longrightarrow> \<not>chDomEmpty TYPE('cs)"
  using sbhdelemnotempty by blast

lemma sbleast2sblenempty[simp]:
"sbIsLeast (x::'cs\<^sup>\<Omega>) \<Longrightarrow> chDomEmpty TYPE('cs) \<or> # x = 0"
  apply(simp only: sbLen_def len_sb_def sbHdElemWell_def,auto)
  by (metis (mono_tags, lifting) Least_le below_bottom_iff lnle_conv lnzero_def slen_zero)


lemma sblen_finite:
  fixes sb::"'cs::{chan,finite}\<^sup>\<Omega>"
    assumes "chDom TYPE('cs) \<noteq> {}"
    shows "#sb = (MIN c .  # (sb \<^enum> c))"
  apply(rule sblen_rule)
    apply(auto simp add: assms)[2]
  by (metis (no_types, lifting) Min_in empty_is_image empty_not_UNIV finite_UNIV finite_imageI rangeE) 

lemma sblen_finite2:
  fixes sb::"'cs::{chan,finite}\<^sup>\<Omega>"
    assumes "chDom TYPE('cs) \<noteq> {}"
    shows "#sb = Min  {# (sb \<^enum> c) | c. True}"
  apply(subst sblen_finite,simp add: assms)
  by (simp add: full_SetCompr_eq)

lemma sblen_singleton:
  fixes sb::"'cs::{chan}\<^sup>\<Omega>"
    assumes "chDom TYPE('cs) = {c}"
    shows "#sb =  # (sb \<^enum> Abs c)"
  by (metis(full_types) abs_eqI(1) assms chdom_in insert_not_empty sblen2slen singletonD)

lemma sbe2sb_len: "1 \<le> #(sbe2sb (sbe::'a::{chan,finite}\<^sup>\<surd>))"
  apply(cases "chDomEmpty TYPE('a)")
  by simp+

lemma sbe2sb_len_ex: "\<exists>outSBE. out = sbe2sb outSBE \<Longrightarrow> #out \<ge> 1"
  apply (cases "chDomEmpty TYPE('a)")
  apply (simp; fail)
  by force

lemma sbe2sb_cont[simp]: "cont (\<lambda> sbe. case (Rep_sbElem sbe) of Some f \<Rightarrow> \<lambda>c. \<up>(f c)
                                | None  \<Rightarrow> \<bottom> )"
  by simp

                                               text\<open>\label{subsub:sbdrop}\<close>


lemma sbdrop_well[simp]:"lsb_well (\<lambda>c. sdrop n\<cdot>(b \<^enum>\<^sub>\<star> c))"
  apply(rule lsbwellI)
  by (meson dual_order.trans sbgetch_ctypewell sdrop_sValues)

lift_definition sbDrop::"nat \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>"is
"\<lambda> n sb. Abs_lsb (\<lambda>c. sdrop n\<cdot>(sb \<^enum> c))"
  apply(intro cont2cont)
  by(simp add: sValues_def)

lemmas sbdrop_insert = sbDrop.rep_eq

text\<open>A special case of @{const sbDrop} is to drop only the first
element of the \gls{sb}. It is the rest operator on \Gls{sb}.\<close>

abbreviation sbRt :: "'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>"  where 
"sbRt \<equiv> sbDrop 1"

lemma sbdrop_bot[simp]:"sbDrop n\<cdot>\<bottom> = \<bottom>"
  apply(simp add: sbdrop_insert)
  by (simp add: bot_sb)

lemma sbdrop_eq[simp]:"sbDrop 0\<cdot>sb = sb"
  by(simp add: sbdrop_insert sbgetch_insert2)

lemma sbdrop_plus: "sbDrop (k+x)\<cdot>xs = sbDrop k\<cdot>(sbDrop x\<cdot>xs)"
  apply (simp add: sbDrop_def sbgetch_insert2 sdrop_plus)
  apply (subst(3) beta_cfun)
  apply (intro cont2cont)
  apply (simp add: cont2cont_fun; fail)
  apply (meson order.trans rep_sb_well lsb_well_def sdrop_sValues)
  apply (subst(2) beta_cfun)
  apply (intro cont2cont)
  apply (simp add: cont2cont_fun; fail)
  apply (metis Abs_lsb_inverse mem_Collect_eq sbdrop_well sbgetch_well sbgetchid)
  apply (subst Abs_lsb_inverse)
  apply (metis Abs_lsb_inverse mem_Collect_eq sbdrop_well sbgetchid sbgetch_well)
  apply (subst beta_cfun)
  apply (intro cont2cont)
  apply (simp add: cont2cont_fun; fail)
  apply (meson order_trans rep_sb_well lsb_well_def sdrop_sValues)
  by blast
 
lemma sbdrop_forw_rt: "sbDrop (Suc n)\<cdot>s = sbDrop n\<cdot>(sbRt\<cdot>s)"
  by (simp add: sbdrop_plus [symmetric])

                                             text\<open>\label{subsub:sbtake}\<close>


lemma sbtake_well[simp]:"lsb_well (\<lambda>c. stake n\<cdot>(sb  \<^enum>\<^sub>\<star>  c))"
  by(simp add: sbmap_well)

lift_definition sbTake::"nat \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow>  'cs\<^sup>\<Omega>"is
"\<lambda> n sb. Abs_lsb (\<lambda>c. stake n\<cdot>(sb \<^enum> c))"
  by(intro cont2cont, simp)

lemmas sbtake_insert = sbTake.rep_eq

text\<open>A special case of @{const sbTake} is to take only the first
element of the \gls{sb}.\<close>

abbreviation sbHd :: "'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>"  where 
"sbHd \<equiv> sbTake 1"

text\<open>Obtaining some stream form a \gls{sb} after applying 
@{const sbTake}, is the same as applying  @{const stake} after
obtaining the stream from the \gls{sb}.\<close>

theorem sbtake_getch[simp]:"sbTake n\<cdot>sb \<^enum> c = stake n\<cdot>(sb \<^enum> c)"
  apply(simp add: sbgetch_insert sbTake.rep_eq)
  apply(subst Abs_lsb_inverse,auto simp add: lsb_well_def)
  by (metis sValues_sconc sbgetch_ctypewell sbgetch_insert2 
      split_streaml1 subsetD)

text\<open>The output of @{const sbTake} is always @{const below} the
input.\<close>

theorem sbtake_below[simp]: "sbTake i\<cdot>sb \<sqsubseteq> sb"
  by (simp add: sb_belowI)

lemma sbTakezero[simp]:"sbTake 0\<cdot>sb = \<bottom>"
  by(rule sb_eqI,simp)

lemma sbTakebot[simp]:"sbTake k\<cdot>\<bottom> = \<bottom>"
  using sbtake_below below_bottom_iff by blast

lemma sbtake_idem[simp]:
  assumes "n \<ge> i"
  shows"sbTake n\<cdot>(sbTake i\<cdot>sb) = (sbTake i\<cdot>sb)"
  by (simp add: sb_eqI assms min_absorb2)

lemma sbmap_stake_eq:"
  Abs_lsb (\<lambda>c::'a. stake n\<cdot>(sb \<^enum> c)) \<^enum> c = stake n\<cdot>(sb \<^enum> c)"
  apply(simp add: sbgetch_insert2)
  apply(subst Abs_lsb_inverse)
  apply simp
  apply(rule lsbwellI)
  apply (metis sbgetch_insert2 sbgetch_ctypewell dual_order.trans 
         sValues_sconc split_streaml1)
  by simp

lemma sbtake_max_len [simp]:"#(sbTake n\<cdot>sb  \<^enum>  c) \<le> Fin n"
  by simp

lemma abs_sb_eta:
  assumes "lsb_well  (\<lambda>c::'cs. f\<cdot>(sb \<^enum> c))"
  and "\<not>chDomEmpty TYPE('cs)"
  shows "(Abs_lsb (\<lambda>c::'cs. f\<cdot>(sb  \<^enum>  c))  \<^enum>  c) = f\<cdot>(sb  \<^enum>  c)"
  by (metis Abs_lsb_inverse assms(1) mem_Collect_eq sbgetch_insert2)

lemma sbconc_sconc:
  assumes  "lsb_well  (\<lambda>c::'cs. f\<cdot>(sb \<^enum> c))"
  and  "lsb_well  (\<lambda>c. g\<cdot>( sb \<^enum> c))"
  and "\<not>chDomEmpty TYPE('cs)"
  shows "Abs_lsb (\<lambda>c. f\<cdot>(sb  \<^enum>  c)) \<Zcat>\<^sup>\<Omega> Abs_lsb (\<lambda>c. g\<cdot>(sb  \<^enum>  c)) =
        Abs_lsb (\<lambda>c. f\<cdot>(sb  \<^enum>  c) \<Zcat> g\<cdot>(sb  \<^enum>  c))"
  by (simp add: assms abs_sb_eta sbconc_insert)


theorem sbconctakedrop[simp]:"sbConc (sbTake n\<cdot>sb)\<cdot>(sbDrop n\<cdot>sb) = sb"
  apply(cases "chDomEmpty TYPE('a)")
  apply (metis (full_types) sbtypeepmpty_sbbot)
  apply (simp add: sbtake_insert sbdrop_insert)
  by (subst sbconc_sconc,simp_all)

lemma sbcons [simp]:"sbConc (sbHd\<cdot>sb)\<cdot>(sbRt\<cdot>sb) = sb"
  by simp


lemma sbtakesuc:"sbTake (Suc n)\<cdot>sb = sbHd\<cdot>sb \<Zcat>\<^sup>\<Omega> sbTake n\<cdot>(sbRt\<cdot>sb)"
  apply(rule sb_eqI)
  apply(case_tac "sb  \<^enum>  c = \<epsilon>",simp)
  apply (metis sbconc_bot_l sbconc_bot_r sbconc_getch 
         sbconctakedrop sbdrop_bot sbgetch_bot sbtake_getch)
  apply simp
proof -
  fix c :: 'a
  assume a1: "sb \<^enum> c \<noteq> \<epsilon>"
  have "sb = sbHd\<cdot>sb \<Zcat>\<^sup>\<Omega> sbDrop (Suc 0)\<cdot>sb"
    by auto
  then show "stake (Suc n)\<cdot>(sb \<^enum> c) = stake (Suc 0)\<cdot> (sb \<^enum> c) \<Zcat> 
                                    stake n\<cdot>(sbDrop (Suc 0)\<cdot>sb \<^enum> c)"
    using a1 by (metis One_nat_def sbconc_getch sbtake_getch 
                  stake2shd stake_Suc)
qed

lemma botlen[simp]:
  assumes "chDom TYPE('cs) \<noteq> {}"
  shows"#(\<bottom>::'cs\<^sup>\<Omega>) = 0"
  using botsbleast sbleast2sblenempty assms by blast

lemma sbtake_len:
  assumes "\<not>chDomEmpty TYPE('b)"
    and "Fin i \<le> #(sb::'b\<^sup>\<Omega>)"
  shows "#(sbTake i\<cdot>sb) = Fin i"
  using assms
  apply (induction i)
  apply (simp add: sbLen_def len_sb_def)
   apply (metis (mono_tags, lifting) LeastI)
  apply(rule sblen_rule, auto simp add: assms)
   apply (auto simp add: sbLen_def len_sb_def)[2]
proof -
  fix ia :: nat
  assume "Fin (Suc ia) \<le> (if chDomEmpty (TYPE('b)::'b itself) then \<infinity> else LEAST n. n \<in> {#(sb \<^enum> c) |c. True})"
  then have "Fin (Suc ia) \<le> #sb"
    by (simp add: len_sb_def sbLen_def)
  then show "\<exists>b. #(stake (Suc ia)\<cdot>(sb \<^enum> b)) = Fin (Suc ia)"
    by (metis (no_types) assms(1) sblen2slen slen_stake)
next
  fix ia :: nat and c :: 'b
  assume "Fin (Suc ia) \<le> (if chDomEmpty (TYPE('b)::'b itself) then \<infinity> else LEAST n. n \<in> {#(sb \<^enum> c) |c. True})"
  then have "Fin (Suc ia) \<le> #sb"
    by (simp add: len_sb_def sbLen_def)
  then show "Fin (Suc ia) \<le> #(stake (Suc ia)\<cdot>(sb \<^enum> c))"
    by (metis (no_types) assms(1) refl_lnle sblen_min_len slen_stake trans_lnle)
qed


definition sbValues :: "('cs::chan) sb \<rightarrow> ('cs \<times> M) set" where
"sbValues = (\<Lambda> sb. \<Union>{Pair c ` sValues\<cdot>(sb \<^enum> c) | c. Rep c \<in> chDom TYPE('cs)})"

lemma sbvalues_cont [cont2cont]: "cont (\<lambda>x::'cs\<^sup>\<Omega>. \<Union>{Pair c ` sValues\<cdot>(x \<^enum> c) | c. Rep c \<in> chDom TYPE('cs::chan)})"
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: set_cpo_simps)
  apply (subgoal_tac "\<And>c. Rep c \<in> chDom TYPE('cs) \<Longrightarrow> sValues\<cdot>(x \<^enum> c) \<subseteq> sValues\<cdot>(y \<^enum> c)")
  apply blast
  using sValues_prefix sbgetch_sbelow apply blast
  apply (simp add: set_cpo_simps)
  apply (subst contlub_cfun_arg)
  apply (simp; fail)
  apply (subst contlub_cfun_arg)
  apply (rule chainI)
  apply (meson po_class.chainE sbgetch_sbelow)
  apply (simp add: set_cpo_simps)
  apply (rule subsetI)
  by blast

lemma sbvalues_insert:
  "sbValues\<cdot>sb = \<Union>{Pair c ` sValues\<cdot>(sb \<^enum> c) | c::'cs. Rep c \<in> chDom TYPE('cs::chan)}"
  by (simp add: sbValues_def)

lemma sbValues_bot[simp]:
  "sbValues\<cdot>\<bottom> = \<bottom>"
  by (simp add: sbValues_def UU_eq_empty)

lemma sbValues_empty[simp]:
  assumes "chDomEmpty TYPE('cs::chan)"
  shows "sbValues\<cdot>(sb::'cs\<^sup>\<Omega>) = {}"
  apply (simp add: sbValues_def)
  by (simp add: sbgetch_insert assms)

lemma sbValues_sbconc_subset_union:
  "sbValues\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2) \<subseteq> sbValues\<cdot>sb1 \<union> sbValues\<cdot>sb2"
proof -
  have svals_conc_subset:"\<And> c. sValues\<cdot>((sb1 \<^enum> c) \<Zcat> sb2  \<^enum> c) \<subseteq>
    (sValues\<cdot>(sb1 \<^enum> c) \<union> sValues\<cdot>(sb2 \<^enum> c))"
    by(simp add:sconc_sValues)

  show ?thesis
  apply(simp add:sbValues_def)
  proof
    fix x assume x_def:
      "x \<in> \<Union> {Pair c ` sValues\<cdot>((sb1  \<^enum>  c) \<Zcat> sb2  \<^enum>  c)
        |c::'a. Rep c \<in> chDom TYPE('a)}"
    obtain c m where x_insert:"x = (c, m)" 
      by fastforce
    with x_def have "m \<in> sValues\<cdot>((sb1  \<^enum>  c) \<Zcat> sb2  \<^enum>  c)"
      by fastforce
    with svals_conc_subset have m_in_union:
      "m \<in> (sValues\<cdot>(sb1 \<^enum> c) \<union> sValues\<cdot>(sb2 \<^enum> c))"
      using sconc_sValues by blast
  
    show "x \<in> \<Union> {Pair c ` sValues\<cdot>(sb1  \<^enum>  c) 
                |c::'a. Rep c \<in> chDom TYPE('a)} \<union>
   \<Union> {Pair c ` sValues\<cdot>(sb2  \<^enum>  c) |c::'a. Rep c \<in> chDom TYPE('a)}"
      proof (cases "m \<in> (sValues\<cdot>(sb1 \<^enum> c))")
        case True
        hence "(c, m) \<in> Pair c ` sValues\<cdot>(sb1  \<^enum>  c)" by auto
        hence "(c, m) \<in> \<Union> {Pair c ` sValues\<cdot>(sb1  \<^enum>  c) 
                          |c::'a. Rep c \<in> chDom TYPE('a)}"
          using x_def x_insert by blast
        then show ?thesis using x_insert by simp
      next
        case False
        with m_in_union have "m \<in> (sValues\<cdot>(sb2 \<^enum> c))" by blast
        hence "(c, m) \<in> Pair c ` sValues\<cdot>(sb2  \<^enum>  c)" by auto
        hence "(c, m) \<in> \<Union> {Pair c ` sValues\<cdot>(sb2  \<^enum>  c) |c::'a. Rep c \<in> chDom TYPE('a)}"
          using x_def x_insert by blast
        then show ?thesis using x_insert by simp
      qed
  qed
qed

lemma sbValues_sbconc2un:
  assumes "\<And>c. #(sb1 \<^enum> c) = Fin k"
  shows "sbValues\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2) = sbValues\<cdot>sb1 \<union> sbValues\<cdot>sb2"
  apply (simp add: sbValues_def)
  by (auto simp add: assms sValues_sconc2un [where k="k"])

lemma sbValues_sbe2sb:
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows "sbValues\<cdot>(sbe2sb (sbe::'cs\<^sup>\<surd>)) = {(c, sbegetch c sbe) | c::'cs. Rep c \<in> chDom TYPE('cs::chan) }"
proof (rule antisym; rule subsetI)
  fix x 
  assume x_in_sbvalues: "x \<in> sbValues\<cdot>(sbe2sb sbe)"
  have c_in_dom: "Rep (fst x) \<in> chDom TYPE('cs)"
    using assms chdom_in by blast
  have "snd x \<in> sValues\<cdot>(sbe2sb sbe \<^enum> (fst x))"
    apply (insert x_in_sbvalues)
    by (auto simp add: sbValues_def)
  hence x_sbegetch: "snd x = sbegetch (fst x) sbe"
    by (simp add: c_in_dom sbe2sb_getch)
  thus "x \<in> {(c, sbegetch c sbe) |c::'cs. Rep c \<in> chDom TYPE('cs)}"
    by (metis (mono_tags, lifting) c_in_dom mem_Collect_eq prod.collapse)
next
  fix x
  assume "x \<in> {(c, sbegetch c sbe) |c::'cs. Rep c \<in> chDom TYPE('cs)}"
  hence "snd x \<in> sValues\<cdot>(sbe2sb sbe \<^enum> (fst x))"
    using sbe2sb_getch by force
  thus "x \<in> sbValues\<cdot>(sbe2sb sbe)"
    apply (simp add: sbValues_def)
    apply (rule_tac x="Pair (fst x) ` sValues\<cdot>(sbe2sb sbe \<^enum> (fst x))" in exI)
    apply (rule conjI)
    apply (rule_tac x="fst x" in exI)
    apply simp
    using assms chdom_in apply blast
    by (metis image_iff prod.collapse)
qed

lemma sbvalues_ctypewell2:
  assumes "x \<in> sbValues\<cdot>(sb::'cs::chan\<^sup>\<Omega>)"
  shows "(snd x) \<in> ctype (Rep (fst x))"  and "Rep (fst x) \<in> chDom TYPE('cs)"
  apply (insert assms)
  apply (auto simp add: sbValues_def)[2]
  using sbgetch_ctypewell by blast


text\<open>Converting a \gls{sb} to a @{type sbElem} is rather complex. 
The main goal is to obtain the first slice of a \gls{sb} as a 
@{type sbElem}. This is not possible, if there is an empty stream in
the bundles domain. Hence, the @{type sbElem} can only be obtained,
if the domain is: 
  \<^item> empty, then the head element is @{const None}
  \<^item> non-empty and contains no empty stream, the head element is some
    function that maps to the head of the corresponding bundle 
    streams

For defining the sbHdElem function we use a helper that has always a
defined output. For this, the output is extended by \<open>\<bottom>\<close>. In the case
of an non-empty domain and an empty stream in the bundle, \<open>\<bottom>\<close> is 
returned. In \cref{subsub:sbhdelemc} we will also show the helpers 
continuity for finite bundles.\<close>

lemma sbhdelem_mono:
"monofun (\<lambda>sb::'c\<^sup>\<Omega>. 
          if chDomEmpty TYPE('c) 
             then Iup (Abs_sbElem None)
             else if sbIsLeast sb 
                     then \<bottom> 
                     else Iup (Abs_sbElem 
                          (Some (\<lambda>c::'c. shd (sb  \<^enum>\<^sub>\<star>  c)))))"
  apply(rule monofunI)
  apply(cases "chDomEmpty TYPE('c)")
  apply auto[2]
  by (metis below_shd_alt monofun_cfun_arg sbnleast_mex)
 

definition sbHdElem_h::"'cs\<^sup>\<Omega> \<Rightarrow> ('cs\<^sup>\<surd>) u"where
"sbHdElem_h sb = 
       (if chDomEmpty TYPE('cs) 
          then Iup(Abs_sbElem None) 
          else if sbIsLeast sb 
                  then \<bottom> 
                  else Iup(Abs_sbElem (Some (\<lambda>c. shd((sb) \<^enum> c)))))"

text\<open>The final @{type sbElem} obtaining function then uses 
@{const sbHdElem_h} to obtain only the @{type sbElem} outputs, if 
the helper returns \<open>\<bottom>\<close> the output is @{const undefined}.\<close>

definition sbHdElem::"'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>"where
"sbHdElem sb = (case (sbHdElem_h sb) of 
                      Iup sbElem \<Rightarrow> sbElem     | 
                      _          \<Rightarrow> undefined)"
                      

text\<open> The @{const sbHdElem} function checks if the output of
@{const sbHdElem_h} is a @{type sbElem}. And then returns it. If the
helper returns \<open>\<bottom>\<close> our converter maps to \<open>undefined\<close> as mentioned 
above.\<close>
abbreviation sbHdElem_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>" ( "\<lfloor>_" 70) where
"\<lfloor>sb \<equiv> sbHdElem sb"

paragraph \<open>sbHdElem Properties \\\<close>

text\<open>Our \<open>sbHdElem\<close> operator maps each \gls{sb} to a 
corresponding @{type sbElem} exactly as intended. If the domain of 
the \gls{sb} is empty, it results in the @{const None} 
@{type sbElem} and if the input bundle contains no empty stream, the
resulting @{type sbElem} maps to the head of the corresponding 
streams.\<close>  

theorem sbhdelem_none[simp]:
  fixes   sb::"'cs\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs)"
  shows   "sbHdElem sb = Abs_sbElem None"
  by(simp add: sbHdElem_def assms sbHdElem_h_def)


theorem sbhdelem_some:
  fixes   sb::"'cs\<^sup>\<Omega>"
  assumes "sbHdElemWell sb" 
  shows   "sbHdElem sb = Abs_sbElem(Some(\<lambda>c. shd(sb \<^enum> c)))"
  using assms
  by(simp add: sbHdElem_def sbHdElem_h_def)

text\<open>Another interesting property is that two bundles which contain
no empty stream in their domain, but are in order, will be mapped to 
the same @{type sbElem}.\<close>

theorem sbhdelem_mono_eq[simp]:
  fixes   sb1::"'cs\<^sup>\<Omega>"
  assumes "sbHdElemWell sb1"
  and     "sb1 \<sqsubseteq> sb2"
  shows   "sbHdElem sb1 = sbHdElem sb2"
  apply(cases "chDomEmpty TYPE('cs)",simp)
  apply(simp_all add: sbhdelem_some assms)
  apply(subst sbhdelem_some)
  using assms sbleast_mono apply blast
  by (metis below_shd_alt monofun_cfun_arg assms sbnleast_mex)


theorem sbhdelem_mono_empty[simp]:
  fixes   sb1::"'cs\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs)"
  shows   "sbHdElem sb1 = sbHdElem sb2"
  by (simp add: assms)

text\<open>Given a @{type sbElem} and a \gls{sb}, we can append the 
@{type sbElem}to the \gls{sb}. Of course we also have to consider the 
domain when appending the bundle:
  \<^item> If the domain is empty, the output \gls{sb} is \<open>\<bottom>\<close>
  \<^item> If the domain is not empty, the output \gls{sb} has the input
    @{type sbElem} as its first element.


Using only this operator allows us to construct all \glspl{sb} where
every stream has the same length. But since there is no restriction
for the input bundle, we can map to any \gls{sb} with a length
greater 0.\<close>

abbreviation sbECons::"'cs\<^sup>\<surd> \<Rightarrow> 'cs\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<Omega>"(infixr "\<Zcat>\<^sup>\<surd>" 100) 
where "sbe \<Zcat>\<^sup>\<surd> sb \<equiv> sbe2sb sbe \<Zcat>\<^sup>\<Omega> sb"

text\<open>Because we already constructed a converter from @{type sbElem}s
to \glspl{sb} in \cref{subsub:sbe2sb} and the concatenation 
in \cref{subsub:sbconc}, @{const sbECons} is just another 
abbreviation.\<close>



theorem sbtypeempty_sbecons_bot:
  fixes   sbe::"'cs\<^sup>\<surd>"
  assumes "chDomEmpty TYPE ('cs)"
  shows   "sbe \<Zcat>\<^sup>\<surd> sb = \<bottom>"
  by (simp add: assms)

lemma sb_empty_unfold: fixes sb::"'cs\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs)"
  shows "sb = (Abs_sbElem None) \<Zcat>\<^sup>\<surd> sb"
  by(rule sb_empty_eq, simp add: assms)

lemma exchange_bot_sbecons:
"chDomEmpty TYPE ('cs) \<Longrightarrow> P sb \<Longrightarrow> P((sbe::'cs\<^sup>\<surd>) \<Zcat>\<^sup>\<surd> sb)"
  by (metis (full_types) sbtypeepmpty_sbbot)

lemma sbecons_sbvalues:
  assumes "\<not>chDomEmpty TYPE('cs::chan)"
  shows "sbValues\<cdot>(sbe \<Zcat>\<^sup>\<surd> (sb::'cs\<^sup>\<Omega>)) = sbValues\<cdot>(sbe2sb sbe) \<union> sbValues\<cdot>sb"
  apply (rule sbValues_sbconc2un)
  by (auto simp add: assms one_lnat_def sbe2slen_1)

text\<open>It also holds, that the rest operator (\cref{subsub:sbtake}) of a
with @{const sbECons} constructed \gls{sb} is a destructor.\<close>


lemma sbehdleme_well[simp]:
      "chDom TYPE('cs) \<noteq> {} \<Longrightarrow> sbHdElemWell ((sbe \<Zcat>\<^sup>\<surd> sb)::'cs\<^sup>\<Omega>)"
  apply(subst sbHdElemWell_def,simp)
  by (metis sbgetch_sbe2sb_nempty sconc_snd_empty strictI)

theorem sbrt_sbecons: "sbRt\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = sb"
  apply (cases "chDomEmpty(TYPE('a))", simp)
  apply (simp add: sbDrop.rep_eq)
  apply (subst sdropl6)
  apply(simp add: sbe2sb.rep_eq sbgetch_insert2 option.case_eq_if)
  using sbgetchid by blast

lemma sbhdelem_h_sbe:" sbHdElem_h (sbe \<Zcat>\<^sup>\<surd> sb) = up\<cdot>sbe"
  apply(cases "chDom TYPE('a) = {}")
  apply (simp_all add: sbHdElem_def sbHdElem_h_def up_def)
  apply (metis sbtypeepmpty_sbenone) 
  by (simp add: Rep_sbElem_inverse)
 


lemma sbhdelem_sbecons: "sbHdElem (sbe  \<Zcat>\<^sup>\<surd> sb) = sbe"
  by(simp add: sbHdElem_def sbhdelem_h_sbe up_def)

theorem sbh_sbecons: "sbHd\<cdot>(sbe  \<Zcat>\<^sup>\<surd> sb) = sbe2sb sbe"
  apply(rule sb_eqI, auto)
  apply(auto simp add: sbe2sb.rep_eq sbgetch_insert2)[1]
  apply(cases "Rep_sbElem sbe = None")
  apply auto[2]
  using sbtypefull_none by blast

text\<open>Constructing a \gls{sb} with @{const sbECons} increases its 
length by exactly 1. This also holds for empty domains, because we 
interpret the length of those \Gls{sb} as \<open>\<infinity>\<close>.\<close>

theorem sbecons_len[simp]:
  shows "#(sbe \<Zcat>\<^sup>\<surd> sb) = lnsuc\<cdot>(# sb)"
  apply(cases "chDomEmpty(TYPE('a))",simp)
  apply(subst sblen_sbconc_eq[where k="1"])
  apply (simp add: sbe2slen_1; fail)
  using lnat_plus_suc by blast

lemma sbHdElem:
"# (sb::'cs\<^sup>\<Omega>) \<noteq> (0::lnat) \<Longrightarrow> sbe2sb (sbHdElem sb) = sbHd\<cdot>sb"
  apply (case_tac "chDomEmpty (TYPE ('cs))")
  apply (metis (full_types) sbtypeepmpty_sbbot)
  apply (rule sb_rep_eqI)
  apply (simp add: sbHdElem_def sbHdElem_h_def)
  apply (intro conjI)
  using sbleast2sblenempty apply blast
  apply(simp add:sbtake_insert stake2shd sbe2sb.abs_eq 
        sbe2sb.rep_eq Abs_sbElem_inverse lsb_well_def)
  by (metis (no_types) sbgetch_insert2 sbmap_stake_eq sbnleast_mex 
      stake2shd)

lemma sbdrop_sbe[simp]: "sbDrop (Suc n)\<cdot>(a \<Zcat>\<^sup>\<surd> as) = sbDrop n\<cdot>as"
  apply (subst sbdrop_forw_rt)
  by (simp only: sbrt_sbecons)

lemma sbtake_sbe[simp]:"sbTake (Suc n)\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = sbe \<Zcat>\<^sup>\<surd> sbTake n\<cdot>sb"
  by (metis sbh_sbecons sbrt_sbecons sbtakesuc)


lemma sbtake_chain:"chain (\<lambda>i::nat. sbTake i\<cdot>x)"
  apply (rule chainI)
  apply(simp add: below_lsb_def)
  apply(rule fun_belowI)
  apply(simp add: sbtake_insert)
  by (metis (no_types) Suc_leD le_refl sbgetch_insert2 stake_mono)

lemma sblen_sbtake:
"\<not>chDomEmpty TYPE ('c) \<Longrightarrow> # (sbTake n\<cdot>(x :: 'c\<^sup>\<Omega>)) \<le> Fin (n)"
proof- 
assume a0:"\<not>chDomEmpty TYPE ('c)"
  have h0:"\<And>c. # (sbTake n\<cdot>x) \<le> #((sbTake n\<cdot>x) \<^enum> (c::'c))"
    by(rule sblen_min_len, simp add: a0)
  have h1:"\<And>c. #((sbTake n\<cdot>x) \<^enum> (c::'c)) \<le> Fin (n)"
   by simp 
  then show ?thesis
    using dual_order.trans h0 by blast
qed

lemma sbtake_lub:"(\<Squnion>i::nat. sbTake i\<cdot>x) = x"
  apply(rule sb_eqI)
  apply(subst contlub_cfun_arg)
  apply(simp add: sbtake_chain; fail)
  by(simp add: sbtake_insert sbmap_stake_eq reach_stream)

lemma sbECons_sbLen:"# (sb::'cs\<^sup>\<Omega>) \<noteq> (0::lnat) \<Longrightarrow>
 \<not> chDomEmpty TYPE('cs) \<Longrightarrow> \<exists> sbe sb'. sb = sbe \<Zcat>\<^sup>\<surd> sb'"
  by (metis sbHdElem sbcons)


lemma sbecons_sbhdelemwell: "sbHdElemWell (sbe2sb sbe) \<Longrightarrow> 
                             sbHdElemWell (sbe \<Zcat>\<^sup>\<surd> sb)"
  by (metis monofun_cfun_arg sbTakezero sbconc_bot_r 
      sbleast_mono sbtake_below)

lemma sb_eqI3 : 
  fixes sb1 and sb2 :: "'cs\<^sup>\<Omega>"
  assumes "\<And> n. (sbTake n\<cdot>(sb1) = (sbTake n\<cdot>(sb2)))"
  shows "sb1=sb2"
proof -
  have sb_lub1: "(\<Squnion>i::nat. sbTake i\<cdot>sb1) = sb1"
    using sbtake_lub by blast
  have sb_lub2: "(\<Squnion>i::nat. sbTake i\<cdot>sb2) = sb2"
    using sbtake_lub by blast
  then show ?thesis
    by (metis (no_types, lifting) assms lub_eq sb_lub1)
qed


lemma sbHd_reduce : 
  fixes sb :: "'cs\<^sup>\<Omega>"
  assumes "sb = sb_fst \<Zcat>\<^sup>\<Omega> sb_snd"
  and "0 < #sb_fst"
  shows "sbHd\<cdot>sb = sbHd\<cdot>sb_fst"
  apply(cases "chDomEmpty(TYPE('cs))")
  using sb_empty_eq apply blast
 apply(simp add: sbtake_insert assms)
    apply(rule sb_eqI)
   apply(simp add: sbgetch_insert2)
proof -
  fix c :: 'cs
  assume a1: "\<not> chDomEmpty(TYPE('cs))"
  obtain fst where
    f_def : "fst = stake (Suc (0::nat))\<cdot>(Rep_lsb sb_fst c)"
    by blast           
  then have fst_ex: "fst\<noteq>\<epsilon>"
    apply(insert assms(2))
  proof (rule ccontr)
    assume a2:  "\<not> fst \<noteq> \<epsilon>"
    have "#(sb_fst) = 0"
      apply(subgoal_tac "\<not> chDomEmpty(TYPE('cs))")
      apply (metis One_nat_def a2 f_def lnle_Fin_0 one_lnat_def sbHdElem sbelen_one sbgetch_insert2 sblen_min_len sbtake_getch slen_zero zero_neq_one)
      by(simp add: a1)
  then show "False"
      using assms(2) by auto
  qed
  then have sreduce : "stake (Suc (0::nat))\<cdot>(Rep_lsb sb_fst c \<Zcat> Rep_lsb sb_snd c) = stake (Suc (0::nat))\<cdot>(Rep_lsb sb_fst c)"
    by (metis One_nat_def assoc_sconc f_def fst_ex one_def one_lnat_def only_empty_has_length_0 sconc_snd_empty slen_scons split_streaml1 stake2shd stake_prefix2 stream.take_strict)
  then obtain snd where
    f2_def : "stake (Suc (0::nat))\<cdot>(Rep_lsb sb_fst c \<Zcat> Rep_lsb sb_snd c) = snd"
    by blast
  then have "fst=snd"
    by (simp add: f_def sreduce)
  then have reduce_abstract_one: "Rep_lsb (Abs_lsb (\<lambda>c::'cs. stake n\<cdot>(Rep_lsb sb c))) c = stake n\<cdot>(Rep_lsb sb c)"
    by (metis Abs_lsb_inverse mem_Collect_eq sbgetch_ctypewell sbgetch_insert2 sbtake_getch lsbwellI)
  then have reduce_abstraact_two: "Rep_lsb (Abs_lsb (\<lambda>c::'cs. stake (Suc 0)\<cdot>(Rep_lsb sb_fst c \<Zcat> Rep_lsb sb_snd c))) c = stake (Suc 0)\<cdot>(Rep_lsb sb_fst c \<Zcat> Rep_lsb sb_snd c)"
    apply(subst Abs_lsb_inverse)
     apply(auto)[2]
    apply(rule lsbwellI)
    apply(subgoal_tac "\<And> ca. sValues\<cdot>(Rep_lsb sb_fst ca) \<subseteq> ctype (Rep ca)")
     apply (metis (no_types, opaque_lifting) sbconc_getch sbgetch_ctypewell sbgetch_insert2 sbtake_getch)
    apply(subgoal_tac "\<And> ca. sValues\<cdot>(Rep_lsb sb_snd ca) \<subseteq> ctype (Rep ca)")
     apply (simp add: sbwellD; fail)
    by (simp add: sbwellD)
  then show " Rep_lsb (Abs_lsb (\<lambda>c::'cs. stake (Suc (0::nat))\<cdot>(Rep_lsb sb_fst c \<Zcat> Rep_lsb sb_snd c))) c = Rep_lsb (Abs_lsb (\<lambda>c::'cs. stake (Suc (0::nat))\<cdot>(Rep_lsb sb_fst c))) c"
    by (metis (no_types, lifting) Abs_lsb_inverse mem_Collect_eq lsb_well_def sbgetch_ctypewell sbgetch_insert2 sbtake_getch sreduce)
qed


lemma sbHd_eq :
  fixes sb1 and sb2 :: "'cs\<^sup>\<Omega>"
  assumes "0 < #sb_eq"
  and "sb1 = sb_eq \<Zcat>\<^sup>\<Omega> sb1_snd"
  and "sb2 = sb_eq \<Zcat>\<^sup>\<Omega> sb2_snd"
  shows "sbHd\<cdot>sb1 = sbHd\<cdot>sb2"
  by (metis assms(1) assms(2) assms(3) sbHd_reduce)


paragraph \<open>SB induction and case rules \\\<close>

text\<open>This framework also offers proof methods using the 
@{type sbElem} constructor, that offer an easy proof process when 
applied correctly. The first method is a case distinction for 
\glspl{sb}. It differentiates between the short \glspl{sb} where an 
empty stream exists and all other \glspl{sb}. The configuration of
the lemma splits the goal into the cases \<open>least\<close> and \<open>sbeCons\<close>. Its 
third case checks the truth of an predicate for empty \glspl{sb}. It 
also causes the automatic usage of this case tactic for variables of
type \gls{sb}.\<close>


theorem sb_cases [case_names least sbeCons]:
  assumes "chDomEmpty TYPE('cs) \<Longrightarrow> P"
  and "#(sb'::'cs\<^sup>\<Omega>) = 0 \<Longrightarrow> P" 
  and     "\<And>sbe sb. sb' = sbe \<Zcat>\<^sup>\<surd> sb \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) 
           \<Longrightarrow> P" 
  shows   "P"
  by (meson assms sbECons_sbLen sbnleast_dom sbnleast_len)

lemma sb_cases2 [case_names least sbeCons]: 
  assumes "# (sb'::'cs\<^sup>\<Omega>) = 0 \<Longrightarrow> P" 
  and     "\<And>sbe sb. sb' = sbe \<Zcat>\<^sup>\<surd> sb \<Longrightarrow> P"
  shows   "P"
  by (metis assms(1) assms(2) sbHdElem sbconctakedrop)

lemma sb_cases3 [case_names least sbeCons empty,cases type: sb]: 
  assumes "# (sb'::'cs\<^sup>\<Omega>) = 0 \<Longrightarrow> P" 
  and     "\<And>sbe sb. chDom TYPE('cs) \<noteq> {} \<Longrightarrow> sb' = sbe \<Zcat>\<^sup>\<surd> sb \<Longrightarrow> P" 
  and "chDomEmpty TYPE('cs) \<Longrightarrow> P"
  shows   "P"
  using assms(1) assms(2) assms(3) sbECons_sbLen by blast

lemma sb_finind1:
    fixes x::"'cs\<^sup>\<Omega>"
    shows "# x = Fin k
          \<Longrightarrow> (\<And>sb. sbIsLeast sb \<Longrightarrow> P sb) 
          \<Longrightarrow> (\<And>sbe sb. P sb 
          \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<Zcat>\<^sup>\<surd> sb))
          \<Longrightarrow>P x"
  apply(induction k  arbitrary:x)
  using sbnleast_len apply fastforce
  by (metis Fin_Suc inject_lnsuc sbECons_sbLen sbecons_len 
      sbnleast_dom sbnleast_len)

lemma sb_finind:
  fixes x::"'cs\<^sup>\<Omega>"
  assumes "# x < \<infinity>"
  and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
  and "\<And>sbe sb. P sb \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<Zcat>\<^sup>\<surd> sb)"
  shows "P x"
  by (metis assms(1) assms(2) assms(3) lnat_well_h2 sb_finind1)



theorem sb_ind[case_names adm empty least sbeCons, induct type: sb]:
  fixes   x::"'cs\<^sup>\<Omega>"
  assumes "adm P" 
  and     "\<And>sb. chDomEmpty TYPE('cs) \<Longrightarrow> P sb"
  and     "\<And>sb. #sb=0 \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P sb"
  and     "\<And>sbe sb. P sb \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) 
           \<Longrightarrow> P (sbe \<Zcat>\<^sup>\<surd> sb)"   
  shows   "P x"
  using assms(1) assms(2) assms(3) 
  apply(unfold adm_def)
  apply(erule_tac x="\<lambda>i. sbTake i\<cdot>x" in allE,auto)
  apply(simp add: sbtake_chain; fail)
  apply (metis antisym_conv2 assms(4) inf_ub notinfI3 sb_finind 
      sbleast2sblenempty sblen_sbtake)
  by(simp add: sbtake_lub)

theorem sb_ind2[case_names adm empty least sbeCons]:
  fixes   x::"'cs\<^sup>\<Omega>"
  assumes "adm P" 
  and "\<And>sb. chDomEmpty TYPE('cs) \<Longrightarrow> P sb"
  and     "\<And>sb.  #sb=0 \<Longrightarrow> P sb"
  and     "\<And>sbe sb. P sb \<Longrightarrow> P (sbe \<Zcat>\<^sup>\<surd> sb)"   
  shows   "P x"
  by(induction x,simp_all add: assms)


theorem sbecons_eq:
  assumes "# sb \<noteq> 0" 
  shows "sbHdElem sb \<Zcat>\<^sup>\<surd> sbRt\<cdot>sb = sb"
proof %visible(cases sb)
  case least
  then show ?thesis 
    using assms by(simp only: assms sbHdElem sbcons)
next
  case (sbeCons sbe sb)
  then show ?thesis
    using assms by(simp only: assms sbhdelem_sbecons sbrt_sbecons)
next
  case empty
  then show ?thesis
    by simp
qed


lemma len2sbe_ex:"(\<And>c. #(sb \<^enum> c) = 1) \<Longrightarrow> \<exists>sbe. sbe2sb sbe = sb"
  apply(cases sb,simp_all)
  apply (metis less2eq less_lnsuc lnsuc_neq_0_rev one_def order_refl
      sblengeq)
  apply(subgoal_tac "sba=\<bottom>")
  apply auto[1]
proof(rule ccontr)
  fix sbe sba
  assume a1:"(\<And>c::'a. #((sbe2sb sbe  \<^enum>  c) \<Zcat> sba  \<^enum>  c) = (1::lnat))"
  assume a2:"sba \<noteq> \<bottom>"
  assume a3:"chDom TYPE('a) \<noteq> {}"
  from a2 obtain c where c_def:"sba \<^enum> c \<noteq> \<epsilon>" 
    using sbbot_getch by blast
  moreover have "#(sbe2sb sbe  \<^enum>  c) = 1"
    by(simp add: a3 sbe2slen_1)
  ultimately have "1< #((sbe2sb sbe  \<^enum>  c) \<Zcat> sba  \<^enum>  c)"
    apply(simp add: sconc_slen2)
    by (metis (no_types, lifting) a1 add.commute leneq2strict 
        lnat_1_inf plus_unique_l sconc_slen2 sconc_snd_empty)
  thus "False"
    by(simp add: a1)
qed


text\<open>The second subgoals assumes \<open>sb = sbe \<Zcat>\<^sup>\<surd> sb'\<close>. This alows splitting the \gls{sb} in
      two parts, where the first part is a @{type sbElem}. This 
      helps if a function works element wise on its input.\<close>



theorem shows "sbTake n\<cdot>sb \<sqsubseteq> sb "
proof %visible(induction sb)
  case adm
  then show ?case
    by simp
next
  case (empty sb)
  then show ?case 
    by simp
next
  case (least sb)
  then show ?case 
    by simp
next
  case (sbeCons sbe sb)
  then show ?case 
    by simp
qed


lemma sbtypecast_well:"lsb_well (\<lambda>c. sb \<^enum>\<^sub>\<star> c)"
  by(rule lsbwellI, simp)

lift_definition sbTypeCast::"'cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>"is
"(\<lambda> sb. Abs_lsb (\<lambda>c.  sb \<^enum>\<^sub>\<star> c ))"
  by(intro cont2cont, simp)


lemmas sbtypecast_insert = sbTypeCast.rep_eq

abbreviation sbTypeCast_abbr :: "'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega>"
 ( "_\<star>" 200)  where "sb\<star> \<equiv> sbTypeCast\<cdot>sb"

text\<open>Without the general signature of @{const sbTypeCast}, the
following abbreviations would need own definitions and could not
share properties dirctly among themselves.\<close>

abbreviation sbrestrict_abbr_fst :: "('cs1 \<union> 'cs2)\<^sup>\<Omega> \<Rightarrow> 'cs1\<^sup>\<Omega>"
 ( "_\<star>\<^sub>1" 200) where "sb\<star>\<^sub>1 \<equiv> sbTypeCast\<cdot>sb"


abbreviation sbrestrict_abbr_snd :: "('cs1\<union>'cs2)\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega>"
 ( "_\<star>\<^sub>2" 200) where "sb\<star>\<^sub>2 \<equiv> sbTypeCast\<cdot>sb"

abbreviation sbrestrict_abbr_commu :: "('cs1 \<union>'cs2)\<^sup>\<Omega> \<Rightarrow> ('cs2 \<union> 'cs1)\<^sup>\<Omega>"
 ( "_\<star>\<^sub>\<rightleftharpoons>" 200) where "sb\<star>\<^sub>\<rightleftharpoons> \<equiv> sbTypeCast\<cdot>sb"

abbreviation sbrestrict_abbr_minus :: "'cs1\<^sup>\<Omega> \<Rightarrow> ('cs1-'cs2)\<^sup>\<Omega>"
 ( "_\<star>\<^sub>-" 200) where "sb\<star>\<^sub>- \<equiv> sbTypeCast\<cdot>sb"

abbreviation sbTypeCast_abbr_fixed :: "'cs1\<^sup>\<Omega> \<Rightarrow> 'cs3 itself \<Rightarrow> 'cs3\<^sup>\<Omega>"
 ( "_\<bar>_" 201) where "sb \<bar> _ \<equiv> sbTypeCast\<cdot>sb"


lemma sbtypecast_rep[simp]: "Rep_lsb(sb\<star>) = (\<lambda>c. sb \<^enum>\<^sub>\<star> c)"
  by (simp add: sbtypecast_insert)


lemma sb_well_union_snd:"chDom TYPE('cs2) \<noteq> {} 
\<Longrightarrow> lsb_well (sb::'cs1\<union>'cs2 \<Rightarrow> M stream) 
\<Longrightarrow> lsb_well (\<lambda>c::'cs2. sb (Abs (Rep c)))"
  apply(subgoal_tac "(\<lambda>c::'cs2. sb (Abs (Rep c))) = Rep_lsb(Abs_lsb sb \<star>)",simp)
  by(simp add: sbgetch_insert)

lemma sb_well_union_fst:"chDom TYPE('cs1) \<noteq> {} 
\<Longrightarrow> lsb_well (sb::'cs1\<union>'cs2 \<Rightarrow> M stream) 
\<Longrightarrow> lsb_well (\<lambda>c::'cs1. sb (Abs (Rep c)))"
  apply(subgoal_tac "(\<lambda>c::'cs1. sb (Abs (Rep c))) = Rep_lsb(Abs_lsb sb \<star>)",simp)
  by(simp add: sbgetch_insert)

lemma sbconv_eq[simp]:"sb\<star> = sb"
  apply(rule sb_eqI)
  by (metis (no_types) Abs_lsb_inverse mem_Collect_eq 
        sbtypecast_insert sbtypecast_well sbgetch_insert2)

text\<open>@{const sbTypeCast} is self inverse\<close>
lemma sbtypecast_id[simp]: fixes x::"'cs1\<^sup>\<Omega>"
  assumes "chDom TYPE('cs1) \<subseteq> chDom TYPE('cs2)"
  shows "(x\<star>::'cs2\<^sup>\<Omega>)\<star> = x"
  apply(rule sb_eqI)
  apply(simp add: sbGetCh.rep_eq)
  using assms by blast

lemma sbtypecast_symmetric: fixes x::"'cs1\<^sup>\<Omega>" and y::"'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE('cs1) = chDom TYPE('cs2)"
  and "x = (y\<star>)"
shows "y = (x\<star>)"
  apply(rule sb_eqI)
  using assms by (simp add: sbgetch_insert)

lemma sbtypecast_closed[simp]:
  assumes "chDom TYPE('cs1) = chDom TYPE('cs2)"
  and "chDom TYPE('cs1) = chDom TYPE('cs3)"
shows "(sbTypeCast::'cs2\<^sup>\<Omega> \<rightarrow> 'cs3\<^sup>\<Omega>)\<cdot>((sbTypeCast::'cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>)\<cdot>sb) = (sbTypeCast::'cs1\<^sup>\<Omega> \<rightarrow> 'cs3\<^sup>\<Omega>)\<cdot>sb"
  apply(rule sb_eqI)
  by (simp add: sbgetch_insert assms)

text\<open>@{const sbTypeCast} is strict\<close>
lemma sbtypecast_strict[simp]: "\<bottom>\<star> = \<bottom>"
  apply(simp add: sbtypecast_insert)
  by (simp add: bot_sb)

lemma sbtypecast_empty:
  fixes sb:: "'a\<^sup>\<Omega>"
  assumes "chDom TYPE('b) = {}"
  shows "(sb\<star>::'b\<^sup>\<Omega>) = \<bottom>"
  using assms by simp

lemma sbtypecast_empty2:
  fixes sb::" 'in1\<^sup>\<Omega>"
  assumes "chDom TYPE('out1) \<inter> chDom TYPE('in1) = {}"
  shows "(((sb)\<star>)::'out1\<^sup>\<Omega>) = \<bottom>"
  apply (rule sb_rep_eqI)
  apply auto[1]
  using assms cdom_notempty notcdom_empty by (auto simp add: sbgetch_insert Rep_lsb_strict)

lemma sbtypecast_reduce: 
  fixes sb::"'a\<^sup>\<Omega>"
  assumes "chDom TYPE('a) \<subseteq> chDom TYPE('b)"
  shows "((sb\<star>)::'b\<^sup>\<Omega>)\<star> = (sb\<star>)"
  apply (rule sb_eqI)
  apply (simp add: sbGetCh.rep_eq)
  using assms by blast

lemma sbtypecast_reduce1:"sb\<star> \<star>\<^sub>1 = (sb\<star>)"
  apply(rule sb_eqI)
  by(simp add: sbGetCh.rep_eq)

lemma sbtypecast_reduce2:"sb\<star> \<star>\<^sub>2 = (sb\<star>)"
  apply(rule sb_eqI)
  by(simp add: sbGetCh.rep_eq)

lemma sbtypecast_surj: assumes "chDom TYPE ('cs1) \<subseteq> chDom TYPE('cs2)"
  shows "\<exists>sb2::'cs2\<^sup>\<Omega>. (sb2\<star>) = (sb1::'cs1\<^sup>\<Omega>)"
  apply(rule_tac x="sb1\<star>" in exI)
  by(rule sb_eqI,simp add: assms)

text\<open>Obtaining a stream from a converted \gls{sb} is the same as
not converting it but using the general @{const sbGetCh} operator to
convert the channels type. Thus, converting the domain of a bundle 
is equivalent to converting the type of all its channels.\<close>
 
theorem sbtypecast_getch [simp]: "sb\<star> \<^enum> c = sb \<^enum>\<^sub>\<star> c"
  by (simp add: sbgetch_insert2)

lemma sbtypecast_getch2 [simp]: 
  "Rep c \<in> chDom TYPE('cs) \<Longrightarrow> (sb\<star>::'cs\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c = sb \<^enum>\<^sub>\<star> c"
  by (simp add: sbGetCh.rep_eq)

lemma sbtypecast_getch3:
  fixes sb::"'a\<^sup>\<Omega>"
assumes "chDom TYPE('a) \<subseteq> chDom TYPE('b)"
  shows "(sb\<star>::'b\<^sup>\<Omega>)  \<^enum>\<^sub>\<star>  c = sb  \<^enum>\<^sub>\<star>  c"
  apply(simp add: sbgetch_insert)
  using assms(1) by fastforce

lemma sbtypecast_len:
  assumes "chDom TYPE('cs2) \<subseteq> chDom TYPE('cs1)"
  shows "#sb \<le> #((sbTypeCast_abbr :: 'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega>) sb)"
proof (cases "chDomEmpty TYPE('cs2)")
  case True
  then show ?thesis
    by simp
next
  case cs2_typenempty: False
  obtain least_ch where least_ch1_def: "#sb = #(sb \<^enum> least_ch)"
    by (metis cs2_typenempty assms empty_subsetI equalityI
        order.trans sblen2slen)
  have cs2_sbtypecast_getch: "\<And>c::'cs2. sb\<star> \<^enum> c = sb \<^enum>\<^sub>\<star> c"
    by simp
  thus ?thesis
  proof (cases "Rep least_ch \<in> chDom TYPE('cs2)")
    case least_ch_in_cs2: True
    then show ?thesis
      by (metis Un_iff assms chdom_in cs2_sbtypecast_getch
          cs2_typenempty least_ch1_def order_refl sbgetch_empty2
          sbgetch_insert sbgetch_insert2 sblen_min_len sblengeq
          slen_zero sup.absorb_iff1)
  next
    case least_ch_nin_cs2: False
    then show ?thesis
      by (metis Un_iff assms chdom_in cs2_sbtypecast_getch
          cs2_typenempty least_ch1_def refl_lnle sbgetch_empty2
          sbgetch_insert sbgetch_insert2 sblen_min_len sblengeq
          slen_zero sup.absorb_iff1)
  qed
qed

lemma sb_star21general:
  fixes sb::"'cs0\<^sup>\<Omega>"
  assumes "chDom TYPE('cs0) \<inter> chDom TYPE('cs2 - 'cs1) = {}" 
    shows "((sb \<bar> TYPE('cs1)) \<bar> TYPE ('cs2)) = (sb \<bar> TYPE('cs2))"
  apply(rule sb_eqI)
  apply(simp add: sbgetch_insert)
  using assms by auto

lemma sb_star21:
  fixes sb::"'cs0\<^sup>\<Omega>"
  assumes "chDom TYPE('cs2) \<subseteq> chDom TYPE('cs1)" 
    shows "((sb \<bar> TYPE('cs1)) \<bar> TYPE ('cs2)) = (sb \<bar> TYPE('cs2))"
  apply(rule sb_star21general)
  using assms by auto

lemma sbtypecast2sbeq:
  fixes sb1::"'c1\<^sup>\<Omega>"
  and sb2::"'c2\<^sup>\<Omega>"
  assumes "chDom TYPE ('c1) = chDom TYPE('c2)"
  and "sb1 = (sb2\<star>)"
  shows "sb1 \<triangleq> sb2"
  by (simp add: sbEQ_def assms)

lemma sbtypecast_fix:
  fixes f :: "'a\<^sup>\<Omega> \<rightarrow> 'a\<^sup>\<Omega>"
  assumes "chDom TYPE('b) = chDom TYPE('a)"
  shows "(sbTypeCast::'a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>)\<cdot>(\<mu> x. f\<cdot>x) = (\<mu> x. (f\<cdot>(x\<star>)\<star>))"
  apply(induction rule: parallel_fix_ind)
  by (auto simp add: assms)

lemma sbtypecast_fix_cont:
  fixes f :: "'a\<^sup>\<Omega> \<Rightarrow> 'a\<^sup>\<Omega>"
  assumes "cont f"
  and "chDom TYPE('a) \<subseteq> chDom TYPE('b)"
  shows "(sbTypeCast::'a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>)\<cdot>(\<mu> x. f x) = (\<mu> x. (f (x\<star>)\<star>))"
  apply(induction rule: cont_parallel_fix_ind)
  by (auto simp add: assms cont_compose) 

lemma sbtypecast_sbconc: 
  fixes sb1::"'cs1\<^sup>\<Omega>"
  shows"(((sb1 \<Zcat>\<^sup>\<Omega> sb2)\<star>)::'cs2\<^sup>\<Omega>) = (sb1\<star>) \<Zcat>\<^sup>\<Omega> (sb2\<star>)"
  apply(rule sb_eqI)
  by (simp add: sbgetch_insert repsb_sbconc)

lemma typecast_arg_cong: "x=w \<Longrightarrow> (x\<star>) = (w\<star>)"
  by blast



definition sbUnion::"'cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega> \<rightarrow> ('cs1 \<union> 'cs2)\<^sup>\<Omega>" where
"sbUnion \<equiv> \<Lambda> sb1 sb2. Abs_lsb (\<lambda> c. 
                  if Rep c \<in> chDom TYPE('cs1) 
                  then sb1 \<^enum>\<^sub>\<star> c 
                  else sb2 \<^enum>\<^sub>\<star> c)"

lemma sbunion_sbwell[simp]: "lsb_well ((\<lambda> (c::'e). 
                  if (Rep c \<in> chDom TYPE('c)) then 
                  (sb1::'c\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c else  (sb2::'d\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c))"
  apply(rule lsbwellI)
  by simp

lemma sbunion_cont[simp]: "cont (\<lambda> sb1 sb2. Abs_lsb (\<lambda> c. 
                  if Rep c \<in> chDom TYPE('cs1) 
                  then sb1 \<^enum>\<^sub>\<star> c 
                  else sb2 \<^enum>\<^sub>\<star> c))"
  apply(intro cont2cont)
  apply(rule lsbwellI)
  by simp

lemma sbunion_insert:"(sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2) = Abs_lsb (\<lambda> c. if 
                  (Rep c \<in> chDom TYPE('c)) then 
                  sb1 \<^enum>\<^sub>\<star> c else  sb2 \<^enum>\<^sub>\<star> c)"
  unfolding sbUnion_def
  apply(subst beta_cfun, intro cont2cont, simp)+
  ..

lemma sbunionm_insert:"(sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2)\<star> = Abs_lsb (\<lambda> c. if 
                  (Rep c \<in> chDom TYPE('c)) then 
                  sb1 \<^enum>\<^sub>\<star> c else  sb2 \<^enum>\<^sub>\<star> c)"
  unfolding sbUnion_def
  apply(subst beta_cfun, intro cont2cont, simp)+
  apply(simp add: sbtypecast_insert)
  apply(rule sb_rep_eqI)
  apply(subst Abs_lsb_inverse,simp)
  apply(subst Abs_lsb_inverse,simp)
  apply(subst sbgetch_insert)
  apply(subst Abs_lsb_inverse,simp)
  by(auto simp add: sbgetch_insert) 

lemma sbunion_rep_eq:"Rep_lsb (sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2) = 
 (\<lambda> c. if (Rep c \<in> chDom TYPE('c))
         then sb1 \<^enum>\<^sub>\<star> c 
         else  sb2 \<^enum>\<^sub>\<star> c)"
  by (simp add: sbunion_insert sbgetch_insert)

lemma sbunionm_rep_eq:"Rep_lsb ((sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2) \<star>) = 
 (\<lambda> c. if (Rep c \<in> chDom TYPE('c))
         then sb1 \<^enum>\<^sub>\<star> c 
         else  sb2 \<^enum>\<^sub>\<star> c)"
  by (simp add: sbunionm_insert sbgetch_insert)


abbreviation sbUnion_abbr :: "'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> ('cs1 \<union> 'cs2)\<^sup>\<Omega>"
(infixr "\<uplus>" 100) where "sb1 \<uplus> sb2 \<equiv> sbUnion\<cdot>sb1\<cdot>sb2"

text\<open>The following abbreviations restrict the input and output
domains of @{const sbUnion} to specific cases. These are displayed 
by its signature. Abbreviation \<open>\<uplus>\<^sub>\<star>\<close> is the composed function of 
@{const sbUnion} and @{const sbTypeCast}, thus, it converts the 
output domain.\<close>

abbreviation sbUnion_magic_abbr :: "'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> 'cs3\<^sup>\<Omega>"
(infixr "\<uplus>\<^sub>\<star>" 100) where "sb1 \<uplus>\<^sub>\<star> sb2 \<equiv> (sb1 \<uplus> sb2)\<star>"


abbreviation sbUnion_minus_abbr :: "('cs1 - 'cs2)\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> 'cs1\<^sup>\<Omega>"
(infixr "\<uplus>\<^sub>-" 500) where "sb1 \<uplus>\<^sub>- sb2 \<equiv> sb1 \<uplus>\<^sub>\<star> sb2"



paragraph \<open>sbUnion Properties \\\<close>


lemma sbunion_getch[simp]:fixes c::"'a"
      assumes"Rep c \<in> chDom TYPE('c)"
      shows  "(sbUnion_magic_abbr::'a\<^sup>\<Omega>\<Rightarrow> 'b\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>)cb db \<^enum>\<^sub>\<star> c = cb \<^enum> c"
  apply(simp add: sbunionm_insert)
  apply(simp add: sbgetch_insert)
  apply (auto simp add: sbgetch_insert assms)[1]
  using assms cdom_notempty notcdom_empty apply blast
  done

lemma sbunion_eq [simp]: "sb1 \<uplus>\<^sub>\<star> sb2 = sb1"
  apply(rule sb_eqI)
  apply simp
  by (metis sbtypecast_rep sbunionm_rep_eq) 

lemma sbunion_sbtypecast_eq[simp]:"cb \<uplus>\<^sub>\<star> cb = (cb\<star>)"
  apply(rule sb_eqI,simp)
  by (metis sbtypecast_rep sbunionm_rep_eq)

lemma sbunion_sbtypecast_idemp:"cb \<uplus> cb = (cb\<star>)"
  apply(rule sb_eqI,simp)
  by (metis (no_types) sbtypecast_getch sbunion_sbtypecast_eq)


theorem ubunion_commu:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE ('cs1) \<inter> chDom TYPE ('cs2) = {}"
  shows   "sb1 \<uplus>\<^sub>\<star> sb2 = sb2 \<uplus>\<^sub>\<star> sb1"
  apply(rule sb_rep_eqI)
  apply(simp add: sbunion_rep_eq sbgetch_insert assms)
  using assms cdom_notempty cempty_rule cnotempty_cdom by blast

lemma ubunion_fst[simp]:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE ('cs2) \<inter> chDom TYPE ('cs3) = {}"
  shows   "sb1 \<uplus>\<^sub>\<star> sb2 = (sb1\<star> :: 'cs3\<^sup>\<Omega>)"
  apply(rule sb_rep_eqI)
  apply(simp add: sbunion_rep_eq sbgetch_insert assms)
  using assms cdom_notempty cempty_rule cnotempty_cdom by blast

lemma ubunion_fst2:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE ('cs2) \<inter> chDom TYPE ('cs3) = {}"
  shows   "sb1 \<uplus>\<^sub>\<star> (sb2\<star>) = (sb1\<star> :: 'cs3\<^sup>\<Omega>)"
  apply(rule sb_rep_eqI)
  apply(simp add: sbunion_rep_eq sbgetch_insert assms)
  using assms cdom_notempty cempty_rule cnotempty_cdom by blast

lemma ubunion_id[simp]: "out\<star>\<^sub>1 \<uplus> (out\<star>\<^sub>2) = out"
proof(rule sb_eqI)
  fix c::"'a \<union> 'b"
  assume as:"Rep c \<in> chDom TYPE('a \<union> 'b)"
  have "Rep c \<in> chDom (TYPE ('a)) \<Longrightarrow> out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c"
    by (metis sbgetch_insert2 sbunion_getch sbunion_rep_eq 
        sbunion_sbtypecast_eq)
  moreover have "Rep c \<in> chDom (TYPE ('b)) 
                 \<Longrightarrow> out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c"
    by (metis sbgetch_insert2 sbunion_getch sbunion_rep_eq 
        sbunion_sbtypecast_eq)
  moreover have "Rep c \<in> chDom TYPE ('a) \<or> Rep c \<in> chDom TYPE ('b)"
    using as chdom_in by fastforce
  ultimately show  "out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c" by fastforce
qed

lemma uplus_arg_cong2: "x=y \<Longrightarrow> z=w \<Longrightarrow> x\<uplus>z = y\<uplus>w"
  apply(rule cfun_arg_cong2)
  .
lemma uplusm_arg_cong2: "x=y \<Longrightarrow> z=w \<Longrightarrow> x\<uplus>\<^sub>\<star>z = y\<uplus>\<^sub>\<star>w"
  by blast


theorem sbunion_getchl[simp]:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<in> chDom TYPE('cs1)"
  shows   "(sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c = sb1 \<^enum>\<^sub>\<star> c"
  by(auto simp add: sbgetch_insert sbunion_rep_eq assms)



theorem sbunion_getchr[simp]:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<notin> chDom TYPE('cs1)"
  shows   "(sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c = sb2 \<^enum>\<^sub>\<star> c"
  by(auto simp add: sbgetch_insert sbunion_rep_eq assms)
 
lemma sbunion_conv_fst: 
      fixes sb1 :: "'cs1\<^sup>\<Omega>"
        and sb2 :: "'cs2\<^sup>\<Omega>"
      assumes "chDom TYPE('cs3) \<subseteq> chDom TYPE('cs1)"
      shows  "(((sb1 \<uplus> sb2)\<star>)::'cs3\<^sup>\<Omega>) = (sb1\<star>)"
  apply(rule sb_eqI)
  using assms sbunion_getchl by fastforce

lemma sbunion_conv_snd: 
      fixes sb1 :: "'cs1\<^sup>\<Omega>"
        and sb2 :: "'cs2\<^sup>\<Omega>"
      assumes "chDom TYPE('cs1) \<inter> chDom TYPE('cs3) = {}"
      shows  "(((sb1 \<uplus> sb2)\<star>)::'cs3\<^sup>\<Omega>) = (sb2\<star>)"
  apply(rule sb_eqI)
  using assms sbunion_getchr by fastforce

lemma sbunion_star_getchr_general:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
assumes "Rep c \<in> chDom TYPE('cs3) \<Longrightarrow> Rep c \<notin> chDom TYPE('cs1)"
    and "Rep c \<notin> chDom TYPE('cs3) \<Longrightarrow> Rep c \<notin> chDom TYPE('cs2)"
  shows "((sb1 \<uplus>\<^sub>\<star> sb2)::'cs3\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c = sb2 \<^enum>\<^sub>\<star> c"
  apply(case_tac "Rep c \<in> chDom TYPE('cs3)"; simp)
  using assms(1) apply simp
  using assms(2) by simp

lemma sbunion_star_getchr[simp]:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<notin> chDom TYPE('cs1)"
  shows   "(sb1 \<uplus>\<^sub>\<star> sb2) \<^enum> c = sb2 \<^enum>\<^sub>\<star> c"
  apply(rule sbunion_star_getchr_general[OF assms(1)])
  using cdom_notempty notcdom_empty by blast

lemma sbunion_star_getchl_general:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
assumes "Rep c \<in> chDom TYPE('cs1) \<Longrightarrow> Rep c \<in> chDom TYPE('cs3)"
    and "Rep c \<notin> chDom TYPE('cs1) \<Longrightarrow> Rep c \<in> chDom TYPE('cs2) \<Longrightarrow> Rep c \<notin> chDom TYPE('cs3)"
  shows "((sb1 \<uplus>\<^sub>\<star> sb2)::'cs3\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c = sb1 \<^enum>\<^sub>\<star> c"
  apply(case_tac "Rep c \<in> chDom TYPE('cs1)")
  using assms(1) apply simp
  using assms(2) by(simp add: sbgetch_insert)

lemma sbunion_star_getchl[simp]:
    fixes sb1 ::"'cs1\<^sup>\<Omega>"
      and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<notin> chDom TYPE('cs2)"
  shows   "(sb1 \<uplus>\<^sub>\<star> sb2) \<^enum> c = sb1 \<^enum>\<^sub>\<star> c"
  apply(rule sbunion_star_getchl_general)
  using cdom_notempty notcdom_empty apply blast
  using assms by blast

lemma sbunion_minus_getchr[simp]:
  fixes sb1 ::"('cs1-'cs2)\<^sup>\<Omega>"
  and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<in> chDom TYPE('cs1)"
  and "Rep c \<notin> chDom TYPE('cs1-'cs2)"
  shows   "(sb1 \<uplus>\<^sub>- sb2) \<^enum>\<^sub>\<star> c = sb2 \<^enum>\<^sub>\<star> c"
  using assms(1) assms(2) by auto

lemma sbunion_minus_getchl[simp]:
  fixes sb1 ::"('cs1-'cs2)\<^sup>\<Omega>"
  and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<in> chDom TYPE('cs1-'cs2)"
  shows   "(sb1 \<uplus>\<^sub>- sb2) \<^enum>\<^sub>\<star> c = sb1 \<^enum>\<^sub>\<star> c"
  apply(auto simp add: sbgetch_insert sbunion_rep_eq assms)[1]
  using assms by auto

lemma sbunion_minus_left:
  fixes sb1 ::"('cs1-'cs1)\<^sup>\<Omega>"
  and sb2 ::"'cs1\<^sup>\<Omega>"
  shows   "(sb1 \<uplus>\<^sub>- sb2) = sb2"
  apply(rule sb_eqI)
  by (auto simp add: sbgetch_insert sbunion_rep_eq)

lemma sbunion_minus_getchempty[simp]:
  fixes sb1 ::"('cs1-'cs2)\<^sup>\<Omega>"
  and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<notin> chDom TYPE('cs1)"
  shows   "(sb1 \<uplus>\<^sub>- sb2) \<^enum>\<^sub>\<star> c = \<epsilon>"
  by(simp add: assms)
 
lemma sbunion_minus_getchl2[simp]:
    fixes sb1 ::"('cs1-'cs2)\<^sup>\<Omega>"
      and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<notin> chDom TYPE('cs2)"
  shows   "(sb1 \<uplus>\<^sub>- sb2) \<^enum>\<^sub>\<star> c = sb1 \<^enum>\<^sub>\<star> c"
  by(auto simp add: sbgetch_insert sbunion_rep_eq assms)

lemma sbunion_getch_nomag [simp]:
"sb1 \<uplus>\<^sub>\<star> sb2  \<^enum>  c = (sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c"
  by(auto simp add: sbgetch_insert2 sbunion_rep_eq)

lemma sbunion_magic: 
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
  and   sb2 ::"'cs2\<^sup>\<Omega>"
  shows "(sb1 \<uplus> sb2)\<star> = sb1 \<uplus>\<^sub>\<star> sb2"
  apply(rule sb_eqI)
  by auto

lemma sbunion_magic_len_fst:
  fixes sb1 :: "'cs1\<^sup>\<Omega>"
  and   sb2 :: "'cs2\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs2)" 
    and "\<not>chDomEmpty TYPE('cs1)"
    and "chDom TYPE('cs3) = chDom TYPE('cs1)"
  shows "#((sb1 \<uplus>\<^sub>\<star> sb2)::'cs3\<^sup>\<Omega>) = #sb1"
proof-
  obtain least_ch::'cs1 where 
    sb2_len_chdef: "#sb1 = #(sb1 \<^enum>\<^sub>\<star> least_ch)"
    by (metis assms(2) sblen2slen)
  thus ?thesis
    apply (subst sbunion_conv_fst)
    apply (simp add: assms)
    apply (rule sblen_rule [where k="#sb1"])
    using assms apply blast
    apply (metis assms(2) assms(3) cnotempty_cdom sbgetch_insert
           sbgetch_insert2 sblen_min_len sbtypecast_getch)
    apply (rule_tac x="(Abs (Rep least_ch))" in exI)
    by (simp add: assms(2) assms(3) sbgetch_insert)
qed

lemma sbunion_emptyr: fixes sb2::"'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE('cs2) = {}"
  shows "sb1 \<uplus> sb2 = (sb1\<star>)"
  apply(rule sb_eqI, auto simp add: sbGetCh.rep_eq assms)
  by (simp add: sbgetch_insert sbunion_rep_eq)

lemma sbunion_emptyl: fixes sb1::"'cs1\<^sup>\<Omega>"
  assumes "chDom TYPE('cs1) = {}"
  shows "sb1 \<uplus> sb2 = (sb2\<star>)"
  apply(rule sb_eqI, auto simp add: sbGetCh.rep_eq assms)
  by (simp add: assms sbgetch_insert sbunion_rep_eq)

lemma sbunion_magic_len_snd:
  fixes sb1 :: "'cs1\<^sup>\<Omega>"
  and   sb2 :: "'cs2\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs1)" 
  and "\<not>chDomEmpty TYPE('cs2)"
  and "chDom TYPE('cs3) = chDom TYPE('cs2)"
  shows "#((sb1 \<uplus>\<^sub>\<star> sb2)::'cs3\<^sup>\<Omega>) = #sb2"
proof-
  obtain least_ch::'cs2 where
    sb2_len_chdef: "#sb2 = #(sb2 \<^enum>\<^sub>\<star> least_ch)"
    by (metis assms(2) sblen2slen)
  thus ?thesis
    apply (subst sbunion_conv_snd)
    apply (simp add: assms; fail)
    apply (rule sblen_rule [where k="#sb2"])
    using assms apply blast
    apply (metis assms(2) assms(3) cnotempty_cdom sbgetch_insert
           sbgetch_insert2 sblen_min_len sbtypecast_getch)
    apply (rule_tac x="(Abs (Rep least_ch))" in exI)
    by (simp add: assms sbgetch_insert)
qed

lemma chan_case[case_names indom notindom]:
  assumes"Rep c \<in> S \<Longrightarrow> P"
  and "Rep c \<notin> S \<Longrightarrow> P"
  shows "P"
  using assms(1) assms(2) by blast

lemma sbunion_magic_len:
  fixes sb1 :: "'cs1\<^sup>\<Omega>"
  and   sb2 :: "'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE('cs1) \<inter> chDom TYPE('cs2) = {}"
  and "chDom TYPE('cs3) = chDom TYPE('cs1) \<union> chDom TYPE('cs2)"
shows "#((sb1 \<uplus>\<^sub>\<star> sb2)::'cs3\<^sup>\<Omega>) = min (#sb1) (#sb2)"
proof (cases "chDomEmpty TYPE('cs1)")
  case cs1_dom_empty: True
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case cs2_dom_empty: True
    thus?thesis
      by (simp add: assms cs1_dom_empty)
  next
    case False
    then show ?thesis
      by (simp add: assms cs1_dom_empty sbunion_magic_len_snd)
    qed
next
  case cs1_dom_nempty: False
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case True
    then show ?thesis
      apply (subst sbunion_magic_len_fst, simp_all)
      using cs1_dom_nempty apply blast
      using assms by blast
  next
    case cs2_dom_nempty: False
    obtain least_cs1::'cs1 where 
      sb1_len_chdef: "#sb1 = #(sb1 \<^enum>\<^sub>\<star> least_cs1)"
      by (metis cs1_dom_nempty sblen2slen)
    obtain least_cs2::'cs2 where
      sb2_len_chdef: "#sb2 = #(sb2 \<^enum>\<^sub>\<star> least_cs2)"
      by (metis cs2_dom_nempty sblen2slen)
    have least_cs1_dom: "Rep least_cs1 \<in> chDom TYPE('cs1)"
      by (simp add: cs1_dom_nempty)
    have least_cs1_dom: "Rep least_cs2 \<in> chDom TYPE('cs2)"
      by (simp add: cs2_dom_nempty)
    have "\<And>c::'cs3. Rep c \<notin> chDom TYPE('cs1) \<Longrightarrow> 
            Rep c \<in> chDom TYPE('cs2)"
      using assms(2) cnotempty_cdom cs1_dom_nempty by auto
    then show ?thesis
      apply (subst sblen_rule [where k="min (#sb1) (#sb2)"])
      apply (simp_all add: assms cs1_dom_nempty)
      apply (rule_tac c="c" and S="chDom TYPE('cs1)" in chan_case)
      apply auto[2]
        apply (metis (full_types) min.coboundedI1 rep_reduction
             sbgetch_insert sblen_min_len2)
      apply (simp add: sbgetch_insert )
      apply (metis cs2_dom_nempty min_le_iff_disj sbgetch_insert2
             sblen_min_len)
      apply (cases "min (#sb1) (#sb2) = #sb1", simp_all)
      apply (rule_tac x="Abs (Rep least_cs1)" in exI)
      apply (simp add: sbgetch_insert)
      apply (simp add: assms cs1_dom_nempty sb1_len_chdef
             sbgetch_insert sbunion_rep_eq; fail)
      apply (rule_tac x="Abs (Rep least_cs2)" in exI)
      apply (subgoal_tac "min (#sb1) (#sb2) = #sb2")
      apply (simp add: sbgetch_insert)
      apply (simp add: assms cs2_dom_nempty sb2_len_chdef
             sbgetch_insert sbunion_rep_eq)
      using assms(1) least_cs1_dom apply blast
      by (metis min_def)
  qed
qed


theorem sbunion_fst: "(sb1 \<uplus> sb2)\<star>\<^sub>1 = sb1"
  by simp

lemma sb_union_cast_below: "((sb \<uplus> (sbRel))\<star>\<^sub>2)\<star> \<sqsubseteq> (sb::'cs::chan sb)"
  apply(rule sb_belowI)
  by (metis minimal not_below2not_eq sbgetch_empty sbtypecast_getch2 sbunion_fst)

lemma sb_union_cast_eq[simp]: 
  assumes cssubset: "chDom TYPE('csSmall) \<subseteq> chDom TYPE('csGreat)"
    shows"((sb \<uplus> (sbRel::'csGreat::chan sb))\<star>\<^sub>2)\<star> = (sb::'csSmall::chan sb)"
  apply(rule below_antisym)
  using sb_union_cast_below apply blast
  by (simp add: cssubset sb_star21)


theorem sbunion_snd[simp]:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE ('cs1) \<inter> chDom TYPE ('cs2) = {}"
  shows   "(sb1 \<uplus> sb2)\<star>\<^sub>2 = sb2"
  by (metis assms sbconv_eq ubunion_commu ubunion_fst)

lemma sbunion_eqI:
  assumes "sb1 = (sb\<star>\<^sub>1)"
    and "sb2 = (sb\<star>\<^sub>2)"
  shows "sb1 \<uplus> sb2 = sb"
  by (simp add: assms)

lemma sbunion_beqI:
  assumes "sb1 = (sb\<star>\<^sub>1)"
    and "sb2 = (sb\<star>\<^sub>2)"
  shows "sb1 \<uplus> sb2 \<triangleq> sb"
  by (simp add: assms sbEQ_def)

lemma sbunion_len[simp]:
  fixes sb1 :: "'cs1\<^sup>\<Omega>"
  and   sb2 :: "'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE('cs1) \<inter> chDom TYPE('cs2) = {}"
  shows "#(sb1 \<uplus> sb2) = min (#sb1) (#sb2)"
proof-
  have "#((sbUnion_magic_abbr::'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> ('cs1 \<union> 'cs2)\<^sup>\<Omega>) 
            sb1 sb2) = min (#sb1) (#sb2)"
    by (rule sbunion_magic_len, simp_all add: assms)
  thus ?thesis
    by simp
qed

lemma sbunion_len_fst_leq[simp]:
  fixes sb1 :: "'cs1\<^sup>\<Omega>"
  and   sb2 :: "'cs2\<^sup>\<Omega>"
assumes "#sb1 \<le> #sb2"
shows "#(sb1 \<uplus> sb2) = #sb1"
proof (cases "chDomEmpty TYPE('cs1)")
  case True
  then show ?thesis
    using assms by auto
next
  case cs1_nempty: False
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case True
    then show ?thesis
      by (simp add: sbtypecast_len)
  next
    case cs2_nempty: False
    hence cs1_cs2_union_nempty: "\<not>chDomEmpty TYPE('cs1 \<union> 'cs2)"
      by simp
    then obtain c where c_def: "#(sb1 \<uplus> sb2) = #(sb1 \<uplus> sb2 \<^enum> c)"
      using sblen2slen by blast
    hence c_in_dom_cs1_cs2:
      "Rep c \<in> chDom TYPE('cs1 \<union> 'cs2)"
      using chdom_in cs1_cs2_union_nempty by blast
    have c_nin_dom_union_eq:
      "Rep c \<notin> chDom (TYPE('cs1)) \<Longrightarrow> (sb1 \<uplus> sb2) \<^enum> c = sb2 \<^enum>\<^sub>\<star> c"
      using sbunion_getchr by blast
    have c_in_dom_sb1_leq: 
      "Rep c \<in> chDom (TYPE('cs1)) \<Longrightarrow> #sb1 \<le> #(sb1 \<^enum>\<^sub>\<star> c)"
      by (metis (full_types) rep_reduction sbgetch_insert sblen_min_len2)
    have h1: "Rep c \<notin> chDom (TYPE('cs1)) \<Longrightarrow> #sb2 \<le> #(sb2 \<^enum>\<^sub>\<star> c)"
      by (metis (full_types) UnE c_in_dom_cs1_cs2 chdom_union
          rep_reduction sbgetch_insert sblen_min_len2)
    thus ?thesis
    proof (cases "Rep c \<in> chDom (TYPE('cs1))")
      case True
      then have h2: "#(sb1 \<uplus> sb2 \<^enum> c) = #(sb1 \<^enum>\<^sub>\<star> c)"
        using c_in_dom_sb1_leq by simp
      then have h3: "#(sb1 \<^enum>\<^sub>\<star> c) \<le> #sb1"
        using c_in_dom_sb1_leq True
        by (metis Un_iff c_def chdom_union sbtypecast_len sbunion_fst subsetI)
      hence "#(sb1 \<uplus> sb2) = #(sb1 \<uplus> sb2 \<^enum> c)"
        using c_def by simp
      then show ?thesis
        using h2 h3 True c_in_dom_sb1_leq less2eq by presburger
    next
      case False
      then have h4: "#(sb1 \<uplus> sb2 \<^enum> c) = #(sb2 \<^enum>\<^sub>\<star> c)"
        using c_nin_dom_union_eq by simp
      then have h5: "#(sb2 \<^enum>\<^sub>\<star> c) \<le> #sb1"
        using assms
        by (metis Un_iff c_def chdom_union sbtypecast_len sbunion_fst subsetI)
      hence "#(sb1 \<uplus> sb2) = #(sb1 \<uplus> sb2 \<^enum> c)"
        using c_def by simp
      then show ?thesis
        using h4 h5  by (metis "h1" False assms dual_order.antisym trans_lnle)
    qed
  qed
qed

lemma sbunion_len_fst_leq_old:
  fixes sb1 :: "'cs1\<^sup>\<Omega>"
  and   sb2 :: "'cs2\<^sup>\<Omega>"
assumes "#sb1 \<le> #sb2"
shows "#sb1 \<le> #(sb1 \<uplus> sb2)"
  by (simp add: assms)

lemma sbunion_len_snd_leq:
  fixes sb1 :: "'cs1\<^sup>\<Omega>"
  and   sb2 :: "'cs2\<^sup>\<Omega>"
assumes "#sb2 \<le> #sb1"
shows "#sb2 \<le> #(sb1 \<uplus> sb2)"
  proof (cases "chDomEmpty TYPE('cs1)")
  case True
  then show ?thesis
    using assms by auto
next
  case cs1_nempty: False
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case True
    then show ?thesis
      using assms by auto
  next
    case cs2_nempty: False
    hence cs1_cs2_union_nempty: "\<not>chDomEmpty TYPE('cs1 \<union> 'cs2)"
      by simp
    then obtain c where c_def: "#(sb1 \<uplus> sb2) = #(sb1 \<uplus> sb2 \<^enum> c)"
      using sblen2slen by blast
    hence c_in_dom_cs1_cs2:
      "Rep c \<in> chDom TYPE('cs1 \<union> 'cs2)"
      using chdom_in cs1_cs2_union_nempty by blast
    have c_nin_dom_union_eq:
      "Rep c \<notin> chDom (TYPE('cs1)) \<Longrightarrow> (sb1 \<uplus> sb2) \<^enum> c = sb2 \<^enum>\<^sub>\<star> c"
      using sbunion_getchr by blast
    have c_in_dom_sb1_leq: 
      "Rep c \<in> chDom (TYPE('cs1)) \<Longrightarrow> #sb1 \<le> #(sb1 \<^enum>\<^sub>\<star> c)"
      by (metis (full_types) rep_reduction sbgetch_insert sblen_min_len2)
    have "Rep c \<notin> chDom (TYPE('cs1)) \<Longrightarrow> #sb2 \<le> #(sb2 \<^enum>\<^sub>\<star> c)"
      by (metis (full_types) UnE c_in_dom_cs1_cs2 chdom_union
          rep_reduction sbgetch_insert sblen_min_len2)
    thus ?thesis
      by (metis assms c_def c_in_dom_sb1_leq c_nin_dom_union_eq
          order.trans sbunion_getchl)
  qed
qed

lemma union_minus_nomagfst:
        fixes sb1 ::"(('a \<union> 'b) - 'c \<union> 'd)\<^sup>\<Omega>"
          and sb2 ::"('c \<union> 'd)\<^sup>\<Omega>"
        shows "sb1 \<uplus>\<^sub>\<star> sb2 = ((sb1 \<uplus>\<^sub>- sb2)\<star>\<^sub>1)"
  by (rule sb_eqI,simp)

lemma union_minus_nomagsnd:
        fixes sb1 ::"(('a \<union> 'b) - 'c \<union> 'd)\<^sup>\<Omega>"
          and sb2 ::"('c \<union> 'd)\<^sup>\<Omega>"
        shows "sb1 \<uplus>\<^sub>\<star> sb2 = ((sb1 \<uplus>\<^sub>- sb2)\<star>\<^sub>2)"
  by (rule sb_eqI,simp)

lemma union_minus:
  fixes sb1 ::"('cs1-'cs2)\<^sup>\<Omega>"
  and   sb2 ::"'cs2\<^sup>\<Omega>"
  shows "(sb1 \<uplus> sb2)\<star> = sb1 \<uplus>\<^sub>- sb2"
  by simp

lemma sbunion_belowI: 
  fixes sb1::"'cs1\<^sup>\<Omega>" and sb2::"'cs2\<^sup>\<Omega>"
    assumes "sb1 \<sqsubseteq> (out\<star>)" and "sb2\<sqsubseteq>(out\<star>)"
    shows "sb1 \<uplus>\<^sub>\<star> sb2 \<sqsubseteq> out"
  apply(rule sb_belowI, rename_tac c)
  apply(case_tac "(Rep c)\<in>(chDom TYPE('cs1))", simp)
  apply (metis assms(1) monofun_cfun_arg sbtypecast_getch2)
  apply(case_tac "(Rep c)\<in>(chDom TYPE('cs2))", auto)
  apply (metis  assms(2) monofun_cfun_arg sbtypecast_getch2)
  done

lemma sbunion_belowI2: 
  fixes sb1::"'cs1\<^sup>\<Omega>" and sb2::"'cs2\<^sup>\<Omega>"
    assumes "sb1 \<sqsubseteq> (out\<star>\<^sub>1)" and "sb2\<sqsubseteq>(out\<star>\<^sub>2)"
    shows "sb1 \<uplus> sb2 \<sqsubseteq> out"
  by (metis assms(1) assms(2) monofun_cfun monofun_cfun_arg 
      ubunion_id)

lemma sbunion_minus_len:
  fixes sb1 :: "('cs1-'cs2)\<^sup>\<Omega>" and sb2 :: "'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE('cs2) \<subseteq> chDom TYPE('cs1)"
  shows "#(sb1 \<uplus>\<^sub>- sb2) = min (#sb1) (#sb2)"
  apply (rule sbunion_magic_len)
  apply (simp add: inf_commute)
  using assms by auto

lemma sbunion_minus_len_fst_leq:
  fixes sb1 :: "('cs1-'cs2)\<^sup>\<Omega>" and sb2 :: "'cs2\<^sup>\<Omega>"
  assumes "#sb1 \<le> #sb2"
  shows "#sb1 \<le> #(sb1 \<uplus>\<^sub>- sb2)"
proof (cases "chDomEmpty TYPE('cs1)")
  case True
  then show ?thesis
    by simp
next
  case cs1_nempty: False
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case True
    then show ?thesis
      by (simp add: sbtypecast_len)
  next
    case cs2_nempty: False
    then obtain c where c_def: "#(sb1 \<uplus>\<^sub>- sb2) = #(sb1 \<uplus>\<^sub>- sb2 \<^enum> c)"
      using cs1_nempty sblen2slen by blast
    hence c_in_dom_cs2:
      "Rep c \<notin> chDom (TYPE('cs1-'cs2)) \<Longrightarrow> Rep c \<in> chDom TYPE('cs2)"
      by (simp add: cs1_nempty)
    have c_nin_dom_union_eq:
      "Rep c \<notin> chDom (TYPE('cs1-'cs2)) \<Longrightarrow> (sb1 \<uplus>\<^sub>- sb2) \<^enum> c = sb2 \<^enum>\<^sub>\<star> c"
      using chdom_in cs1_nempty sbunion_minus_getchr by blast
    have c_in_dom_sb1_leq: 
      "Rep c \<in> chDom (TYPE('cs1-'cs2)) \<Longrightarrow> #sb1 \<le> #(sb1 \<^enum>\<^sub>\<star> c)"
      by (metis (full_types) rep_reduction sbgetch_insert sblen_min_len2)
    have "Rep c \<notin> chDom (TYPE('cs1-'cs2)) \<Longrightarrow> #sb2 \<le> #(sb2 \<^enum>\<^sub>\<star> c)"
      by (metis c_in_dom_cs2 cs2_nempty sbgetch_insert sbgetch_insert2 sblen_min_len)
    thus ?thesis
      by (metis (no_types, lifting) assms c_def c_in_dom_sb1_leq
          c_nin_dom_union_eq order.trans sbunion_minus_getchl)
  qed
qed

lemma sbunion_minus_len_snd_leq:
  fixes sb1 :: "('cs1-'cs2)\<^sup>\<Omega>" and sb2 :: "'cs2\<^sup>\<Omega>"
  assumes "#sb2 \<le> #sb1"
  shows "#sb2 \<le> #(sb1 \<uplus>\<^sub>- sb2)"
  proof (cases "chDomEmpty TYPE('cs1)")
  case True
  then show ?thesis
    by simp
next
  case cs1_nempty: False
  have cs2_empty_sb2_leq:
    "chDomEmpty TYPE('cs2) \<Longrightarrow> #sb2 \<le> #(sb1 \<uplus>\<^sub>- sb2)"
    by (metis assms bot.extremum eq_refl min_absorb2 sbunion_minus_len)
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case True
    then show ?thesis
      using cs2_empty_sb2_leq by blast
  next
    case cs2_nempty: False
    then obtain c where c_def: "#(sb1 \<uplus>\<^sub>- sb2) = #(sb1 \<uplus>\<^sub>- sb2 \<^enum> c)"
      using cs1_nempty sblen2slen by blast
    hence c_in_dom_cs2:
      "Rep c \<notin> chDom (TYPE('cs1-'cs2)) \<Longrightarrow> Rep c \<in> chDom TYPE('cs2)"
      by (simp add: cs1_nempty)
    have c_nin_dom_union_eq:
      "Rep c \<notin> chDom (TYPE('cs1-'cs2)) \<Longrightarrow> (sb1 \<uplus>\<^sub>- sb2) \<^enum> c = sb2 \<^enum>\<^sub>\<star> c"
      using chdom_in cs1_nempty sbunion_minus_getchr by blast
    have c_in_dom_sb1_leq: 
      "Rep c \<in> chDom (TYPE('cs1-'cs2)) \<Longrightarrow> #sb1 \<le> #(sb1 \<^enum>\<^sub>\<star> c)"
      by (metis (full_types) rep_reduction sbgetch_insert sblen_min_len2)
    have "Rep c \<notin> chDom (TYPE('cs1-'cs2)) \<Longrightarrow> #sb2 \<le> #(sb2 \<^enum>\<^sub>\<star> c)"
      by (metis c_in_dom_cs2 cs2_nempty sbgetch_insert sbgetch_insert2 sblen_min_len)
    thus ?thesis
      by (metis (no_types, lifting) assms c_def c_in_dom_sb1_leq
          c_nin_dom_union_eq order.trans sbunion_minus_getchl)
  qed
qed

lemma sbunion_minus_sbunion_star_eq:
  fixes sb1::"'cs1\<^sup>\<Omega>"
  and   sb2::"'cs2\<^sup>\<Omega>"
  shows "(sb1\<star>\<^sub>-) \<uplus>\<^sub>- sb2 = (sb2 \<uplus>\<^sub>\<star> sb1)"
  apply(rule sb_eqI, simp)
  apply(case_tac " Rep c \<in> chDom TYPE ('cs2)")
  by (simp_all)
  
lemma sbunion_minus_star_minus_fst_id:
  fixes sb1::"'cs1\<^sup>\<Omega>"
  and   sb2::"'cs2\<^sup>\<Omega>"
  assumes "\<And>c. Rep c\<in> chDom TYPE ('cs1) \<inter> chDom TYPE ('cs2) \<Longrightarrow> sb1 \<^enum> c = sb2 \<^enum>\<^sub>\<star> c"
  shows   "(sb1\<star>\<^sub>-) \<uplus>\<^sub>- sb2 = sb1"
  apply(rule sb_eqI)
  by (case_tac "Rep c \<in>chDom TYPE ('cs1) - chDom TYPE ('cs2)", simp_all add: assms)

lemma sbunion21 [simp]: 
  fixes sbIn:: "(('c \<union> 'a - 'b) - 'd \<union> 'b)\<^sup>\<Omega>"
       and a:: "('d \<union> 'b)\<^sup>\<Omega>"
     shows "((sbIn \<uplus>\<^sub>- a)\<star>\<^sub>2) \<uplus>\<^sub>- (a\<star>\<^sub>2) = sbIn \<uplus>\<^sub>\<star> a"
  apply(rule sb_eqI, simp)
  by(simp add: sbGetCh.rep_eq sbunion_rep_eq)


lemma sbunion21' [simp]: "(sbIn \<uplus>\<^sub>- a\<star>\<^sub>1) \<uplus>\<^sub>- (a\<star>\<^sub>1) = sbIn \<uplus>\<^sub>\<star> a"
  apply(rule sb_eqI)
  by(simp add: sbGetCh.rep_eq sbunion_rep_eq)

lemma sbunion_magic21: 
  fixes sb1::"'cs1\<^sup>\<Omega>"
    and sb2::"'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE('cs1) \<inter> chDom TYPE('cs2) = {}"
      and "chDom TYPE('cs1) \<inter> chDom TYPE('cs4) = {}"
      and "chDom TYPE('cs5) \<subseteq> chDom TYPE('cs3) \<union> chDom TYPE('cs4)"
    shows "((sb1 \<uplus>\<^sub>\<star> sb2)::'cs3\<^sup>\<Omega>) \<uplus>\<^sub>\<star> ((sb2\<star>)::'cs4\<^sup>\<Omega>) = ((sb1 \<uplus>\<^sub>\<star> sb2)::'cs5\<^sup>\<Omega>)"
  apply(rule sb_eqI, simp)
  apply(case_tac "Rep c \<in> chDom TYPE('cs1)"; case_tac "Rep c \<in> chDom TYPE('cs3)"; simp)
  using assms by auto

lemma sbunion_bottom_fst: 
  fixes sb2 :: "'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE('cs1) \<inter> chDom TYPE('cs2) = {}"
  shows  "((\<bottom>::'cs1\<^sup>\<Omega>) \<uplus> sb2) = (sb2\<star>)"
  apply(rule sb_eqI,simp)
  using assms by (auto simp add: sbGetCh.rep_eq sbunion_rep_eq bot_sb)

lemma sbunion_bottom_snd: 
  fixes sb1 :: "'cs1\<^sup>\<Omega>"
  shows "(sb1 \<uplus> (\<bottom>::'cs2\<^sup>\<Omega>)) = (sb1\<star>)"
  apply(rule sb_eqI,simp)
  by (auto simp add: sbGetCh.rep_eq sbunion_rep_eq bot_sb)

lemma unionm_empty_bottom:
  fixes a::"'a\<^sup>\<Omega>" and b::"'b\<^sup>\<Omega>"
  assumes "chDom TYPE('b) \<inter> chDom TYPE('c) = {}"
      and "chDom TYPE('a) \<inter> chDom TYPE('c) = {}"
  shows "(((a\<star>) \<uplus>\<^sub>\<star> (b\<star>))::'c\<^sup>\<Omega>) = \<bottom>"
  apply (rule sb_rep_eqI)
  apply (subst  sbunionm_rep_eq)
  apply auto[1]
  using assms cdom_notempty notcdom_empty by (auto simp add: sbgetch_insert Rep_lsb_strict)

lemma sbunionm_typecast_reduce:
  fixes sb1 :: "'a\<^sup>\<Omega>"
  and sb2 :: "'b\<^sup>\<Omega>"
  assumes "chDom TYPE('a) \<subseteq> chDom TYPE('a2)"
  and "chDom TYPE('b)  \<subseteq> chDom TYPE('b2)"
  and "chDom TYPE('b) \<inter>  chDom TYPE('a2) = {}"
shows "(sb1\<star>::'a2\<^sup>\<Omega>) \<uplus>\<^sub>\<star> (sb2\<star>::'b2\<^sup>\<Omega>) = sb1 \<uplus>\<^sub>\<star> sb2"
  apply (rule sb_eqI)
  using assms by (auto simp add: sbunion_insert sbgetch_insert)

paragraph\<open>Commutativity and Associativity of sbUnion\<close>

text\<open>If the domains of the input \glspl{sb} are pairwise disjoint
then @{const sbUnion} is commutative and associative.\<close>

lemma sbunion_commu_sbtypecast:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE ('cs1) \<inter> chDom TYPE ('cs2) = {}"
  shows   "sb1 \<uplus> sb2 = sb2 \<uplus>\<^sub>\<star> sb1"
  apply(rule sb_rep_eqI)
  apply(simp add: sbunion_rep_eq sbgetch_insert)
  using assms by auto

theorem sbunion_commu:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom TYPE ('cs1) \<inter> chDom TYPE ('cs2) = {}"
  shows   "sb1 \<uplus> sb2 \<triangleq> sb2 \<uplus> sb1"
  apply(simp add: sbEQ_def)
  apply(subst sbunion_commu_sbtypecast)
  apply(simp add: sbunion_rep_eq sbgetch_insert)
  using assms by auto

lemma sbunion_assoc_sbtypecast:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  and     sb3 ::"'cs3\<^sup>\<Omega>"
  assumes "chDom TYPE ('cs1) \<inter> chDom TYPE ('cs2) = {}"
  assumes "chDom TYPE ('cs1) \<inter> chDom TYPE ('cs3) = {}"
  shows   "(sb1 \<uplus> sb2) \<uplus> sb3 = sb1 \<uplus>\<^sub>\<star> (sb2 \<uplus> sb3)"
  apply(rule sb_rep_eqI)
  by (simp add: sbunion_rep_eq sbgetch_insert assms)

theorem sbunion_assoc:
  fixes   sb1 ::"'cs1\<^sup>\<Omega>"
  and     sb2 ::"'cs2\<^sup>\<Omega>"
  and     sb3 ::"'cs3\<^sup>\<Omega>"
  assumes "chDom TYPE ('cs1) \<inter> chDom TYPE ('cs2) = {}"
  assumes "chDom TYPE ('cs1) \<inter> chDom TYPE ('cs3) = {}"
  shows   "(sb1 \<uplus> sb2) \<uplus> sb3 \<triangleq> sb1 \<uplus> (sb2 \<uplus> sb3)"
  apply(simp only: sbEQ_def)
  apply(subst sbunion_assoc_sbtypecast)
  by (auto simp add: assms)

lemma sbtypecast_exchangeorderfst[simp]:
  fixes x::"(('I3 \<union> 'I4) - 'O3 \<union> 'O4)\<^sup>\<Omega>"
    and xa::"('O3 \<union> 'O4)\<^sup>\<Omega>"
assumes "chDom TYPE ('I1) = chDom TYPE('I3)"
assumes "chDom TYPE ('O1) = chDom TYPE('O3)"
assumes "chDom TYPE ('I2) = chDom TYPE('I4)"
assumes "chDom TYPE ('O2) = chDom TYPE('O4)"
  shows"((x\<star>::(('I1 \<union> 'I2) - 'O1 \<union> 'O2)\<^sup>\<Omega>) \<uplus>\<^sub>- (xa\<star>)\<star>\<^sub>1) = (x \<uplus>\<^sub>- xa\<star>\<^sub>1\<star>)"
  apply(rule sb_eqI,simp)
  by(simp add: sbgetch_insert assms sbunion_rep_eq)

lemma sbtypecast_exchangeordersnd[simp]:
  fixes x::"(('I3 \<union> 'I4) - 'O3 \<union> 'O4)\<^sup>\<Omega>"
    and xa::"('O3 \<union> 'O4)\<^sup>\<Omega>"
assumes "chDom TYPE ('I1) = chDom TYPE('I3)"
assumes "chDom TYPE ('O1) = chDom TYPE('O3)"
assumes "chDom TYPE ('I2) = chDom TYPE('I4)"
assumes "chDom TYPE ('O2) = chDom TYPE('O4)"
  shows"((x\<star>::(('I1 \<union> 'I2) - 'O1 \<union> 'O2)\<^sup>\<Omega>) \<uplus>\<^sub>- (xa\<star>)\<star>\<^sub>2) = (x \<uplus>\<^sub>- xa\<star>\<^sub>2\<star>)"
  apply(rule sb_eqI,simp)
  by(simp add: sbgetch_insert assms sbunion_rep_eq)

lemma sbeUnion2sbUnion: 
  fixes sbe1 :: "'a\<^sup>\<surd>"
  and sbe2 :: "'b\<^sup>\<surd>"
assumes "chDom TYPE('c) \<subseteq>  chDom TYPE('a \<union> 'b)"
  shows "sbe2sb ((sbeUnion sbe1 sbe2)::'c\<^sup>\<surd>) = (sbe2sb sbe1) \<uplus>\<^sub>\<star> (sbe2sb sbe2)"
  apply (rule sb_eqI)
  apply (auto simp add: sbe2sb_getch)[1]
  apply (case_tac "Rep c \<in> chDom TYPE('a)")
  apply (metis empty_iff sbe2sb_getch sbeunion_getchfst2 sbunion_getchl)
  apply (case_tac "Rep c \<in> chDom TYPE('b)")
  apply (metis empty_iff sbe2sb_getch sbeunion_getchsnd2 sbunion_getchr)
  using assms by auto

lemma sbunion_sbconc: "(sb1 \<Zcat>\<^sup>\<Omega> sb2) \<uplus> (sb3 \<Zcat>\<^sup>\<Omega> sb4) = (sb1 \<uplus> sb3) \<Zcat>\<^sup>\<Omega> (sb2 \<uplus> sb4)"
  apply (rule sb_eqI)
  apply (case_tac "Rep c \<in> chDom TYPE('a)")
  by auto

lemma sbunion_sbconc2: "(sb1 \<Zcat>\<^sup>\<Omega> sb2) \<uplus> (sb3) = (sb1 \<uplus> sb3) \<Zcat>\<^sup>\<Omega> (sb2\<star>)"
  apply (rule sb_eqI)
  apply (case_tac "Rep c \<in> chDom TYPE('a)")
  by auto

lemma sbunion_sbconc3: "(sb1 \<Zcat>\<^sup>\<Omega> sb2) \<uplus> (sb3) = (sb1\<star>)  \<Zcat>\<^sup>\<Omega> (sb2 \<uplus> sb3)"
  apply (rule sb_eqI)
  apply (case_tac "Rep c \<in> chDom TYPE('a)")
  by auto
 
lemma sbunion_sbconc4:
  assumes "chDom TYPE('a) \<inter> chDom TYPE('b) = {}"
  shows "(((sb1) \<uplus> (sb2 \<Zcat>\<^sup>\<Omega> sb3))::('a \<union> 'b)\<^sup>\<Omega>) = (sb2\<star>)  \<Zcat>\<^sup>\<Omega> (sb1 \<uplus> sb3)"
  apply (rule sb_eqI)
  apply (case_tac "Rep c \<in> chDom TYPE('a)")
  apply auto[2]
  apply (simp add: sbgetch_insert)
  using assms by blast

lemma sbecons_union: "(((sbe1 \<Zcat>\<^sup>\<surd> sb1) \<uplus> (sbe2 \<Zcat>\<^sup>\<surd> sb2))) = (sbeUnion sbe1 sbe2) \<Zcat>\<^sup>\<surd> (sb1 \<uplus> sb2)"
  by (simp add:  sbeUnion2sbUnion sbunion_sbconc)



lift_definition sbRenameCh::"('cs1 \<Rightarrow> 'cs2) \<Rightarrow> 'cs2\<^sup>\<Omega> \<rightarrow> 'cs1\<^sup>\<Omega>" is
"\<lambda>f sb. if (\<forall>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)) 
          then Abs_lsb (\<lambda>c. sb \<^enum> (f c))
          else undefined"
  apply(intro cont2cont)
  apply(rule lsbwellI) using sbgetch_ctypewell by blast

lemma sbrenamech_rep: 
  assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
  shows "Rep_lsb (sbRenameCh f\<cdot>sb) = (\<lambda>c. sb \<^enum> (f c)) "
  apply(simp add: assms sbRenameCh.rep_eq)
  apply(rule Abs_lsb_inverse, simp)
  apply(rule lsbwellI) using sbgetch_ctypewell assms by blast

lemma sbrename_id: "sbRenameCh id = ID"
  by (simp add: sbRenameCh_def ID_def)


theorem sbrenamech_getch[simp]: 
  assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
  shows "(sbRenameCh f\<cdot>sb) \<^enum> c = sb \<^enum> (f c)"
  by (simp add: assms sbgetch_insert2 sbrenamech_rep)

lemma sbrenamech_getch2:
  fixes f::"'a \<Rightarrow> 'b"
  assumes "Rep c \<in> chDom TYPE('a)"
      and "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
  shows "sbRenameCh f\<cdot>sb \<^enum>\<^sub>\<star> c = sb \<^enum> (f (Abs (Rep c)))"
  by (metis assms(1) assms(2) sbgetch_insert sbrenamech_rep)

lemma sbrenamech_getch3: 
  fixes f::"'a \<Rightarrow> 'b"
  assumes well: "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
      and req1: "\<And>c. Rep c \<in> chDom TYPE('c) \<Longrightarrow> Rep (f c) = Rep c"
      and req2: "\<And>c::'c. Rep c \<notin> chDom TYPE('a) \<Longrightarrow> Rep c \<notin> chDom TYPE('b)"
    shows "\<And>c::'c. sbRenameCh f\<cdot>sb  \<^enum>\<^sub>\<star>  c = sb  \<^enum>\<^sub>\<star>  c"
  apply(case_tac "Rep c \<in> chDom TYPE('a)")
  apply(subst sbrenamech_getch2, simp, simp add: well)
  apply(metis (mono_tags) abs_fail cdom_notempty cempty_rule chdom_in req1 sbgetch_insert)
  apply(simp add: sbgetch_insert)
  by(simp add: req2)

lemma sbrenamech_remove: 
  assumes well: "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
      and req1: "\<And>c. Rep c \<in> chDom TYPE('c) \<Longrightarrow> Rep (f c) = Rep c"
      and req2: "\<And>c. Rep c \<notin> chDom TYPE('c) \<Longrightarrow> Rep (f c) \<notin> chDom TYPE('c)"
    shows "\<And>sb::'c\<^sup>\<Omega>. sbRenameCh f\<cdot>(sb\<star>) = (sb\<star>)"
  apply(rule sb_eqI)
  apply(subst sbrenamech_getch, simp add: well, simp)
  apply(case_tac "Rep c \<in> chDom TYPE('c)")
  apply(metis req1 sbgetch_insert)
  by(metis req2 sbgetch_insert)

lemma sbrename_strict:
  assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
  shows "sbRenameCh f\<cdot>\<bottom> = \<bottom>"
  apply(rule sb_eqI)
  apply(subst sbrenamech_getch, rule assms)
  by(auto)

lemma sbrenamech_len[simp]: 
  fixes f::"'cs1 \<Rightarrow> 'cs2"
  assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "\<not>chDomEmpty TYPE('cs2)"
  shows "#sb \<le> #(sbRenameCh f\<cdot>sb)"
  by (rule sblengeq, simp add: assms)

lemma sbconvert_eq2:
  fixes sb1::"'a\<^sup>\<Omega>"
  and   sb2::"'b\<^sup>\<Omega>"
  assumes "chDom TYPE('a) = chDom TYPE ('b)"
  shows   "sb1\<star> = sb2 \<Longrightarrow> sb1 = (sb2\<star>)"
  apply (rule sb_eqI, simp)
  by (metis assms sb_star21 sbtypecast_rep subsetI)

lemma sbrenamecompfg:
  assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
  and"\<And>c. ctype (Rep (g c)) \<subseteq> ctype (Rep c)"
  shows"sbRenameCh f oo sbRenameCh g = sbRenameCh(g o f)"
  apply (rule cfun_eqI)
  apply (rule sb_eqI,simp add: assms)
  by (metis (mono_tags, lifting) assms comp_apply dual_order.trans 
      sbrenamech_getch)

lemma sbrenamecompfg2:
assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (g c)) \<subseteq> ctype (Rep c)"
    and "g o f = id"
  shows "sbRenameCh f oo sbRenameCh g = ID"
  apply(subst sbrenamecompfg[OF assms(1-2)])
  apply(subst assms(3))
  by(rule sbrename_id)

lemma sbrename_id_surj:
  assumes "surj f"
  and "\<And>c. ctype (Rep (f c)) = ctype (Rep c)"
  shows "sbRenameCh (inv f) oo sbRenameCh f = ID"
  apply (subst sbrenamecompfg)
  apply (simp_all add: assms)
  apply (metis assms(1) assms(2) equalityE surj_f_inv_f)
  apply (rule cfun_eqI)
  apply (rule sb_eqI)
  apply (subst sbrenamech_getch)
  apply (metis assms(1) comp_def equalityE pointfree_idE surj_iff)
  by (simp add: assms(1) surj_f_inv_f)

lemma sbrename_id_inj:
  assumes "inj f"
  and "\<And>c. ctype (Rep (inv f c)) = ctype (Rep c)"
  shows "sbRenameCh f oo sbRenameCh (inv f) = ID"
  apply (subst sbrenamecompfg)
  apply (simp_all add: assms)
  apply (metis assms(1) assms(2) inv_f_f order_refl)
  apply (rule cfun_eqI)
  apply (rule sb_eqI)
  by simp

lemma sbrenamech2sberenamech: 
  fixes f:: "'a \<Rightarrow> 'b"
  assumes "(\<And>c::'a. ctype (Rep (f c)) \<subseteq> ctype (Rep c))"
      and "\<not>chDomEmpty TYPE('b)"
  shows "sbRenameCh f\<cdot>(sbe2sb sbe) = sbe2sb (sbeRenameCh f sbe)"
  apply (rule sb_eqI)
  by (simp add: assms sbe2sb_getch)

lemma sbrename_eq:
assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. ctype (Rep (g c)) \<subseteq> ctype (Rep c)"
    and "\<And>c. f c = g c"
  shows "sbRenameCh f = sbRenameCh g"
  apply(rule cfun_eqI)
  apply(rule sb_eqI)
  apply(subst sbrenamech_getch[OF assms(1)])
  apply(subst sbrenamech_getch[OF assms(2)])
  using assms(3) by(simp add: sbgetch_insert)

lemma sbrenamech_typecast_swap:
  fixes f::"'cs1 \<Rightarrow> 'cs2"
    and g::"'cs3 \<Rightarrow> 'cs4"
assumes "\<And> c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. ctype (Rep (g c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. Rep c \<in> chDom TYPE('cs3) \<longrightarrow> Rep c \<in> chDom TYPE('cs1) \<longrightarrow> Rep (f (Abs (Rep c))) = Rep (g c)"
    and "\<And> c. Rep c \<in> chDom TYPE('cs3) \<longrightarrow> Rep c \<notin> chDom TYPE('cs1) \<longrightarrow> Rep (g c) \<notin> chDom TYPE('cs2)"
  shows "sbTypeCast oo sbRenameCh f = sbRenameCh g oo sbTypeCast"
  apply(rule cfun_eqI)
  apply(rule sb_eqI, simp)
  apply(subst sbrenamech_getch[OF assms(2)])
  apply(case_tac "Rep c \<in> chDom TYPE('cs1)"; simp)
  apply(subst sbrenamech_getch2[OF _ assms(1)], simp)
  using assms(3) apply(simp add: sbgetch_insert)
  using assms(4) by(simp add: sbgetch_insert)

lemma seqcomp_sbrename_image_elem:
assumes "\<And>c. ctype (Rep (m c)) = ctype (Rep c)"
    and "surj m"
    and "f oo sbRenameCh (inv m) \<in> F"
  shows "f \<in> {sbRenameCh m} \<then> F"
  apply(subst ID2[symmetric])
  apply(subst sbrename_id_surj[symmetric, OF assms(2,1)])
  apply(subst assoc_oo)
  using assms(3) seqcomp_insert by fastforce

definition sbRename_part::"('cs1 \<rightharpoonup> 'cs2) \<Rightarrow> 'cs2\<^sup>\<Omega> \<rightarrow> 'cs1\<^sup>\<Omega>" where
"sbRename_part f = sbRenameCh (\<lambda>cs1. case (f cs1) of Some cs2 \<Rightarrow> cs2 
                                          | None \<Rightarrow> Abs (Rep cs1))"

lemma sbrenamepart_well[simp]: 
    fixes f :: "('cs1 \<rightharpoonup> 'cs2)"
  assumes "\<And>c. c\<in>dom f \<Longrightarrow> ctype (Rep (the (f c))) \<subseteq> ctype (Rep c)"
      and "\<And>c. c\<notin>dom f \<Longrightarrow> (Rep c) \<in> chDom TYPE ('cs2)"
    shows "ctype (Rep (case f c of None \<Rightarrow> Abs (Rep c) | Some (cs2::'cs2) \<Rightarrow> cs2)) \<subseteq> ctype (Rep c)"
  apply(cases "c\<in>dom f")
  apply(auto simp add: assms)[1]
  using assms(1) apply fastforce
  by (simp add: assms(2) domIff)

theorem sbrenamepart_getch_in[simp]: 
    fixes f :: "('cs1 \<rightharpoonup> 'cs2)"
    assumes "\<And>c. c\<in>dom f \<Longrightarrow> ctype (Rep (the (f c))) \<subseteq> ctype (Rep c)"
        and "\<And>c. c\<notin>dom f \<Longrightarrow> (Rep c) \<in> chDom TYPE ('cs2)"
        and "c\<in>dom f"
    shows "(sbRename_part f\<cdot>sb) \<^enum> c = sb \<^enum> the (f c)"
  apply(simp add: sbRename_part_def)
  apply(subst sbrenamech_getch)
  apply(auto simp add: assms)[1]
  using assms(3) by auto

lemma sbrenamepart_getch_in2: 
fixes f :: "('cs1 \<rightharpoonup> 'cs2)"
assumes "\<And>c. c\<in>dom f \<longrightarrow> ctype (Rep (the (f c))) \<subseteq> ctype (Rep c)"
    and "\<And>c. c\<notin>dom f \<longrightarrow> (Rep c) \<in> chDom TYPE ('cs2)"
    and "Abs (Rep c) \<in> dom f"
    and "Rep c \<in> chDom TYPE('cs1)"
  shows "sbRename_part f\<cdot>sb \<^enum>\<^sub>\<star> c = sb \<^enum> the (f (Abs (Rep c)))"
  apply(simp add: sbRename_part_def)
  apply(subst sbrenamech_getch2)
  apply(rule assms(4))
  apply(auto simp add: assms(1,2))[1]
  using assms(3) by auto

theorem sbrenamepart_getch_out[simp]: 
    fixes f :: "('cs1 \<rightharpoonup> 'cs2)"
    assumes "\<And>c. c\<in>dom f \<Longrightarrow> ctype (Rep (the (f c))) \<subseteq> ctype (Rep c)"
        and "\<And>c. c\<notin>dom f \<Longrightarrow> (Rep c) \<in> chDom TYPE ('cs2)"
        and "c\<notin>dom f"
    shows "(sbRename_part f\<cdot>sb) \<^enum> c = sb \<^enum>\<^sub>\<star> c"
  apply(simp add: sbRename_part_def)
  apply(subst sbrenamech_getch)
  apply(auto simp add: assms)[1]
  by (metis assms(2) assms(3) domIff option.simps(4) sbgetch_insert 
      sbgetch_insert2)

lemma sbrenamepart_getch_out2: 
fixes f :: "('cs1 \<rightharpoonup> 'cs2)"
assumes "\<And>c. c\<in>dom f \<Longrightarrow> ctype (Rep (the (f c))) \<subseteq> ctype (Rep c)"
    and "\<And>c. c\<notin>dom f \<Longrightarrow> (Rep c) \<in> chDom TYPE ('cs2)"
    and "Abs (Rep c) \<notin> dom f"
    and "Rep c \<in> chDom TYPE('cs1)"
  shows "(sbRename_part f\<cdot>sb) \<^enum>\<^sub>\<star> c = sb \<^enum>\<^sub>\<star> c"
  apply(simp add: sbRename_part_def)
  apply(subst sbrenamech_getch2)
  apply(rule assms(4))
  apply(auto simp add: assms(1,2))[1]
  by (metis assms(2) assms(3) assms(4) domIff option.simps(4) rep_reduction sbgetch_insert)


instantiation sb::(chan) conc
begin
definition "conc_sb = sbConc"

instance
  apply standard
    apply(simp_all add: conc_sb_def)
  by (simp add: sbconc_asso)
end


lemma sbconc_getch_split:"(sb1\<Zcat>\<Zcat>sb2)  \<^enum>  c = (sb1  \<^enum>  c)\<Zcat>\<Zcat>(sb2 \<^enum>  c) "
  by (metis conc_sb_def conc_stream_def sbconc_getch)

lemma sbtypecast_conc: "(sb1 \<Zcat>\<Zcat> sb2)\<star> = (sb1\<star>) \<Zcat>\<Zcat> (sb2\<star>)"
  apply(rule sb_eqI)
  using sbtypecast_sbconc by (metis conc_sb_def)

lemma sbconc_union:"(sbA\<Zcat>\<Zcat>restA) \<uplus> (sbB\<Zcat>\<Zcat>restB) = (sbA \<uplus> sbB) \<Zcat>\<Zcat>(restA \<uplus> restB)"
  apply(rule sb_eqI, simp)
proof -
  fix n
  have "snth n ((sbA\<Zcat>\<Zcat>restA) \<uplus> (sbB\<Zcat>\<Zcat>restB) \<^enum> c)
        = snth n (((sbA \<uplus> sbB)\<Zcat>\<Zcat>(restA \<uplus> restB)) \<^enum> c)"
  proof (cases "Fin n < #sbA")
    case True
    then show ?thesis
      by (metis conc_sb_def len_sb_def lnat.dis_rews(1) lnzero_def neg_thms(1) one_lnat_def run_strict sbunion_sbconc)
  next
    case False
    then show ?thesis
      by (metis conc_sb_def sbunion_sbconc)
  qed
  show " \<And>c::'a \<union> 'b. Rep c \<in> chDom TYPE('a) \<or> Rep c \<in> chDom TYPE('b) \<Longrightarrow> (sbA\<Zcat>\<Zcat>restA) \<uplus> (sbB\<Zcat>\<Zcat>restB)  \<^enum>  c = (sbA \<uplus> sbB)\<Zcat>\<Zcat>(restA \<uplus> restB)  \<^enum>  c"
    by (metis conc_sb_def sbunion_sbconc) 
qed


lemma sbconc_unionm:"(sbA\<Zcat>\<Zcat>restA) \<uplus>\<^sub>\<star> (sbB\<Zcat>\<Zcat>restB) = (sbA \<uplus>\<^sub>\<star> sbB) \<Zcat>\<Zcat>(restA \<uplus>\<^sub>\<star> restB)"
  apply(rule sb_eqI, simp)
  by (metis (no_types) sbconc_union sbtypecast_conc sbtypecast_getch)


lemma sbconc_mgetch_split:"(sb1\<Zcat>\<Zcat>sb2)  \<^enum>\<^sub>\<star>  c = (sb1  \<^enum>\<^sub>\<star>  c)\<Zcat>\<Zcat>(sb2 \<^enum>\<^sub>\<star> c) "
  by (metis (mono_tags, lifting) sbconc_getch_split sbtypecast_conc sbtypecast_getch)

lemma unionconc_before:
  assumes "chDom TYPE('cs) \<inter> chDom TYPE('cs2) = {}"
  shows "(x::'cs::chan\<^sup>\<Omega>) \<uplus>\<^sub>\<star> ((y::'cs2::chan\<^sup>\<Omega>)\<Zcat>\<Zcat>z) = (y\<star>) \<Zcat>\<Zcat> (x \<uplus>\<^sub>\<star>z)"
  apply(subst(2) botconc1[symmetric])
  apply(subst sbconc_unionm)
  apply(intro conc_arg_cong2)
  apply(rule sb_eqI, simp)
  using assms apply (metis sbtypecast_empty2 sbtypecast_getch2 sbunion_fst sbunion_getchr)
  ..

lemma spf2stream_ind[simp]:
  assumes "\<And>s sbe. \<exists>a s2. \<forall>sb. spf s\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = \<up>a \<Zcat> (spf s2\<cdot>sb)"
      and "\<And>s. spf s\<cdot>\<bottom>=\<epsilon>"
      and "\<And>sbe s. P (shd (spf s\<cdot>(sbe2sb sbe)))"
      and "Fin n < #sb"
    shows"P (snth n (spf state\<cdot>sb))"
  using assms
  apply(cases sb rule: sb_cases2)
  apply (metis Fin_02bot lnat_well_h1 lnzero_def not_less_zero)
proof(induction n arbitrary:state sb)
  case 0
  then obtain a s2 where a_def:"spf state\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = \<up>a\<Zcat> (spf s2\<cdot>sb)"
    by blast
  then have "spf state\<cdot>(sbe2sb sbe) = \<up>a"
    by (metis "0.prems"(1) "0.prems"(2) inject_scons sbconc_bot_r 
        sconc_snd_empty)
  then have "shd (spf state\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb)) = shd (spf state\<cdot>(sbe2sb sbe))"
    by (simp add: a_def)
  then show ?case
    using "0.prems" by simp
next
  case (Suc n)
  then obtain a s2 where a_def:"spf state\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = \<up>a\<Zcat>(spf s2\<cdot>sb)"
    by blast
  obtain sbea sb2 where sbea_def:"sb = sbea \<Zcat>\<^sup>\<surd> sb2"
    using "Suc.prems"(4,5) apply simp
    by (metis Fin_0 lnat_well_h1 not_less0 sb_cases2)
  have "Fin n < #(sbea \<Zcat>\<^sup>\<surd> sb2)"
    apply(simp add: sbea_def[symmetric])
    using "Suc.prems"(4,5) by (simp)
  then show ?case
    by (metis Suc.IH Suc.prems(5) assms(1) assms(2) assms(3) 
        sbea_def snth_scons)
qed

lemma  spf2stream_ind_reduce:
  assumes "\<And>s sbe. \<exists>a s2. \<forall>sb. spf s\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = \<up>a \<Zcat> (spf s2\<cdot>sb)"
      and "\<And>s. spf s\<cdot>\<bottom>=\<epsilon>"
      and "\<And>sbe s. P (shd (spf s\<cdot>(sbe2sb sbe)))"               
      and "Fin n < #sb"
    shows"P (snth n (spf state\<cdot>sb)) \<and> P2 y = P2 y"
  apply(rule spf2stream_ind,simp add: assms)
  by(simp add: assms)+

lemma conc_getch: "(y\<Zcat>\<Zcat>x)\<^enum>c = (y\<^enum>c) \<Zcat> (x\<^enum>c)"
  by (metis conc_sb_def sbconc_getch)


lemma conc_typecast_one:
  assumes disjunct: "chDom TYPE('csA) \<inter> chDom TYPE('csB) = {}"
        and "chDom TYPE('csAll) \<subseteq> chDom TYPE('csA) \<union> chDom TYPE('csB)"
      shows  "(((x\<star>::'csA::chan\<^sup>\<Omega>)\<star>)\<Zcat>\<Zcat>((x\<star>::'csB::chan\<^sup>\<Omega>)\<star>)) = (x\<star>::'csAll::chan\<^sup>\<Omega>)"
  apply(rule sb_eqI)
  apply(case_tac "Rep c \<in> chDom TYPE('csA)"; simp add: conc_getch)
  using disjunct sbgetch_empty apply fastforce
  apply(case_tac "Rep c \<in> chDom TYPE('csB)"; simp)
  using assms(2) apply blast
  done




fun map_combstream_h::"('m::countable event stream \<rightarrow> 'm event stream)
                    \<Rightarrow> ('m tsyn stream \<rightarrow> 'm tsyn stream)
                    \<Rightarrow> ('m tone stream \<rightarrow> 'm tone stream)
                    \<Rightarrow> ('m list stream \<rightarrow> 'm list stream)
                    \<Rightarrow> ('m stream \<rightarrow> 'm stream)
                    \<Rightarrow> 'm combinedstream \<Rightarrow> 'm combinedstream" where
"map_combstream_h _ _ _ _ f (UNTIMED s) =  UNTIMED (undefined\<cdot>s)" |
"map_combstream_h f _ _ _ _ (TEVENT s) = TEVENT (f\<cdot>s)"   |
"map_combstream_h _ _ _ f _ (TSLICED s) = TSLICED (f\<cdot>s)"    |
"map_combstream_h _ _ f _ _ (TONE s) = TONE (f\<cdot>s)"    |
"map_combstream_h _ f _ _ _ (TSYN s) = TSYN (f\<cdot>s)"

definition map_combstream::"('m::countable event stream \<rightarrow> 'm event stream)
                    \<Rightarrow> ('m tsyn stream \<rightarrow> 'm tsyn stream)
                    \<Rightarrow> ('m tone stream \<rightarrow> 'm tone stream)
                    \<Rightarrow> ('m list stream \<rightarrow> 'm list stream)
                    \<Rightarrow> ('m stream \<rightarrow> 'm stream)
                    \<Rightarrow> 'm combinedstream \<rightarrow> 'm combinedstream" where
"map_combstream f1 f2 f3 f4 f5 = (\<Lambda> s. map_combstream_h f1 f2 f3 f4 f5 s)"


definition tsbMap::"(msg event stream \<rightarrow> msg event stream)
                    \<Rightarrow> (msg tsyn stream \<rightarrow> msg tsyn stream)
                    \<Rightarrow> (msg tone stream \<rightarrow> msg tone stream)
                    \<Rightarrow> (msg list stream \<rightarrow> msg list stream)
                    \<Rightarrow> 'cs::tchan sb \<rightarrow> 'cs sb"where
"tsbMap f1 f2 f3 f4 = ( \<Lambda> sb. Abs_sb (\<lambda>c. map_combstream f1 f2 f3 f4 undefined\<cdot>((Rep_sb sb) c)))"


definition tslicednth::"nat \<Rightarrow> 'a::countable list stream \<rightarrow> 'a list stream" where
"tslicednth n = sEventToList oo (tsnth n)oo sListToEvent"

definition tsbDrop::"nat \<Rightarrow> 'cs::tchan\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" where
"tsbDrop n = tsbMap (tsnth n) (tsnth n) (tsnth n) ((tslicednth n))"

fun OneTLen::"timeType \<Rightarrow> msg set \<Rightarrow> msg combinedstream" where
"OneTLen TTOne msgs = TONE (\<up>(TOneMsg (SOME x. x\<in>msgs)))" |
"OneTLen TTFin _ =  TSLICED (\<up>[])" |
"OneTLen TTLive _ = TEVENT (\<up>Tick)"|
"OneTLen TTsyn _ =  TSYN (\<up>Eps)"

definition tsbTick :: "'cs::tchan\<^sup>\<Omega>" where
"tsbTick = (if (chDom TYPE('cs) = {}) then \<bottom> 
    else Abs_sb (\<lambda>c. OneTLen (cTime (Rep c)) (cMsg (Rep c))))"



instantiation combinedstream :: (countable)tlen
begin

definition tlen_combinedstream::" 'a combinedstream \<Rightarrow> lnat" where
"tlen_combinedstream = Rep_cfun (combStreamCases (Abs_cfun tlen) (Abs_cfun tlen)
(Abs_cfun tlen) (Abs_cfun len) undefined)"
instance
   apply(intro_classes)
   apply(simp_all add: tlen_combinedstream_def)
   apply (simp add: monofun_Rep_cfun2)
  apply(rule_tac x="TEVENT (\<up>\<surd>)" in exI)
  by(simp add: combstreamcases_insert one_lnat_def)
end


  definition tlen_sbn::"'cs::tchan\<^sup>\<Omega> \<Rightarrow> lnat" where
  "tlen_sbn sb \<equiv> if chDomEmpty TYPE('cs) then \<infinity> 
                else LEAST n . n\<in>{#\<^sub>\<surd>((Rep_sb sb)  c) | c. True}"

instantiation sb ::(tchan) tlen
begin
  definition tlen_sb::"'cs::tchan\<^sup>\<Omega> \<Rightarrow> lnat" where
  "tlen_sb sb \<equiv> if chDomEmpty TYPE('cs) then \<infinity> 
                else LEAST n . n\<in>{#\<^sub>\<surd>(sb \<^enum> c) | c. True}"

lemma sbtlen_empty'[simp]:
  fixes   sb::"'cs::tchan\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs)"
  shows   "tlen sb = \<infinity>"
  by(simp add: tlen_sb_def assms)

lemma sbtlen_bot'[simp]:
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows   "tlen (\<bottom>::'cs::tchan\<^sup>\<Omega>) = 0"
  apply(simp add: tlen_sb_def assms)
  by (metis (full_types) LeastI)

lemma sbtlenleq': assumes "\<not> chDomEmpty TYPE('cs::tchan)" and
 "\<exists>c::'cs. #\<^sub>\<surd>(sb\<^enum>c) \<le> k"
  shows "tlen sb \<le> k" 
proof(simp add: tlen_sb_def assms)
  obtain c where c_def:"#\<^sub>\<surd>(sb\<^enum>c) \<le> k"
    using assms(2) by blast
  have "(LEAST n::lnat. \<exists>c::'cs. n = #\<^sub>\<surd> (sb  \<^enum>  c)) \<le> #\<^sub>\<surd>(sb\<^enum>c)"
    apply(rule Least_le)
    by(rule exI,simp)
  then show "(LEAST n::lnat. \<exists>c::'cs. n = #\<^sub>\<surd> (sb  \<^enum>  c)) \<le> k"
    using c_def dual_order.trans by blast
qed


lemma sbtlen2stlen_h:
  fixes "c1"
  assumes"\<not>chDomEmpty(TYPE('c::tchan))"
  and "\<And>c2. #\<^sub>\<surd>((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) \<le> #\<^sub>\<surd>(sb \<^enum> c2)"
  shows "#\<^sub>\<surd>((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) = tlen sb"
  apply(simp add: assms tlen_stream_def tlen_sb_def)
  apply(subst Least_equality)
  apply(simp_all add: assms )
  apply auto[1]
  by (metis assms(2) tlen_stream_def)

lemma sbtlengeq': 
  fixes sb::"'cs::tchan\<^sup>\<Omega>"
    assumes "\<And>c. (Rep c)\<in>chDom TYPE('cs) \<Longrightarrow> k\<le> #\<^sub>\<surd>(sb\<^enum>c)"
  shows "k \<le> tlen sb" 
  apply(cases  "chDomEmpty(TYPE('cs))",simp add: assms)
  apply(subgoal_tac "\<And>c.  k\<le> #\<^sub>\<surd>(sb\<^enum>c)")
  apply(simp add: tlen_sb_def)
  apply(rule LeastI2_wellorder_ex)
  using assms chdom_in by blast+

lemma sb_tlenminc_exists:
  assumes "\<not>chDomEmpty(TYPE('c::tchan))"
  shows "\<exists>c1. \<forall>c2. #\<^sub>\<surd>((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) \<le> #\<^sub>\<surd>(sb \<^enum> c2)"
  using  assms
proof -
  { fix cc :: "'c \<Rightarrow> 'c"
    have ff1: "\<forall>s c l. l \<le> #\<^sub>\<surd>(s \<^enum> (c::'c)) \<or> \<not> l \<le> tlen s"
      by (metis assms le_cases less2eq sbtlenleq')
    { assume a1:"\<exists>c l. \<not> l \<le> #\<^sub>\<surd>(sb \<^enum> c)"
      then have "\<not> \<infinity> \<le> tlen sb"
        using ff1 by (meson inf_ub trans_lnle)
      then have "\<exists>c. #\<^sub>\<surd>(sb \<^enum> c) \<le> #\<^sub>\<surd>(sb \<^enum> cc c)" 
        using ff1         
        by (metis less_le_not_le ln_less
                Orderings.linorder_class.linear lnle2le sbtlengeq') }
    then have "\<exists>c. #\<^sub>\<surd>(sb \<^enum> c) \<le> #\<^sub>\<surd>(sb \<^enum> cc c)"
      by meson }
  then show ?thesis
    by metis
qed

theorem sbtlen2stlen:
  assumes "\<not>chDomEmpty TYPE('cs::tchan)"
  shows "\<exists>c. tlen (sb :: 'cs\<^sup>\<Omega>) = #\<^sub>\<surd>(sb \<^enum> c)"
proof -
  obtain min_c where "\<And>c2. #\<^sub>\<surd>((sb :: 'cs\<^sup>\<Omega>) \<^enum> min_c) \<le> #\<^sub>\<surd>(sb \<^enum> c2)"
    using sb_tlenminc_exists assms by blast
  then have "tlen (sb :: 'cs\<^sup>\<Omega>) = #\<^sub>\<surd>(sb \<^enum> min_c)" 
    by(subst sbtlen2stlen_h,auto simp add: assms)
  then show ?thesis
    by auto 
qed

lemma sbtlen_mono:"monofun (tlen::'cs::tchan\<^sup>\<Omega> \<Rightarrow> lnat)"
  apply(rule monofunI,simp)
  apply(cases "chDomEmpty TYPE('cs)",simp)
  apply(rule sbtlengeq')
  apply(rule sbtlenleq')
  apply simp
  apply(rule_tac x="c" in exI)
  using sbgetch_sbelow tlen_class.mono_tlen by blast

  fun MTimed_OneTLen::"timeType \<Rightarrow> msg set \<Rightarrow> M_timed" where
  "MTimed_OneTLen TTOne msgs = TOne (TOneMsg (SOME x. x\<in>msgs))" |
  "MTimed_OneTLen TTFin _ = TFin []" |
  "MTimed_OneTLen TTLive _ = TLive Tick"|
  "MTimed_OneTLen TTsyn _ = Tsyn Eps" |
  "MTimed_OneTLen TUntimed _ = undefined"

  
  lift_definition sbInfTlen::"'a::tchan\<^sup>\<Omega>" is
  "(\<lambda>c. if (Rep c \<in> chDom TYPE('a)) then (\<up>(Timed (MTimed_OneTLen (cTime (Rep c)) (cMsg (Rep c)))))\<^sup>\<infinity>
                                    else \<epsilon>)"
    apply(rule lsbwellI)
    apply(case_tac "(Rep c) \<in> chDom (TYPE ('a))"; simp)
    apply(case_tac "cTime (Rep c)"; simp add: ctype_def)
    using tchan_ctime apply blast
    defer
       apply (metis ctype_empty_iff dom2ctypenempty empty_iff)
      apply (metis ctype_empty_iff dom2ctypenempty empty_iff)
     apply (metis ctype_empty_iff dom2ctypenempty empty_iff)
    by (metis (mono_tags, lifting) ctype_empty_iff 
       dom2ctypenempty emtpy_reduce image_iff neq_emptyD someI2)

  lemma sbinftlen_getch_len[simp]:"(Rep c \<in> chDom TYPE('a)) \<Longrightarrow> #\<^sub>\<surd> ((sbInfTlen::'a\<^sup>\<Omega>)  \<^enum>  c) = \<infinity>"
  apply(simp add: sbInfTlen.rep_eq sbgetch_insert)
    apply(rule steam_tlen_inf, simp add: lnzero_def one_def)+
      apply(case_tac "cTime (Rep c)"; simp)
    using tchan_ctime apply blast
    by(simp add: lnzero_def one_def)+

  lemma sbinftlen_len: "\<infinity> \<le> tlen sbInfTlen"
    apply(rule sbtlengeq')
    by simp
  instance
    apply(intro_classes)
    using sbtlen_mono apply blast
    apply(rule exI [where x=sbInfTlen])
    using less_lnsuc lnsuc_neq_0_rev lnzero_def one_def
    by (metis SB.sbinftlen_len inf_less_eq)
end

lemma sbtlen_empty:
  fixes   sb::"'cs::tchan\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs)"
  shows   "#\<^sub>\<surd>sb = \<infinity>"
  by(simp add: assms)

lemma ctype_timed:
  assumes "Rep c \<in> chDom TYPE('cs)"
  shows"ctype (Rep (c::'cs::tchan)) \<subseteq> Timed ` UNIV"
  apply(simp add: ctype_def)
  apply(cases "cTime (Rep c)")
  apply auto[5]
  using assms tchan_ctime by blast


lemma tschan_len[simp]:assumes"m \<in> ctype (Rep (c::'cs::tschan))"
  and "Rep c \<in> chDom TYPE('cs)"
  shows "#\<^sub>\<surd> m = 1"
  using assms
  apply(cases m;simp)
  using tschan_ctime[of c] 
  by(cases "cMsg (Rep c) = {}";auto simp add: ctype_def)+
 
lemma tschanlen_eq:
  assumes "sValues\<cdot>s \<subseteq> ctype (Rep (c::'cs::tschan))"
  and "Rep c \<in> chDom TYPE('cs)"
  shows "#\<^sub>\<surd> s = # s"
  using assms
  apply(induction s;simp)
  by (metis lnat_suc_plus tschan_len)

lemma tlensmallerstream:
  assumes "sValues\<cdot>s \<subseteq> Timed ` UNIV"
  shows"#\<^sub>\<surd> (s::M stream) \<le> #s"
  using assms
  apply(induction s,auto)
  apply(rule adm_imp,simp)
  apply(subst lnle_def)
  apply(rule adm_below;simp)
  apply(case_tac x;simp add: lnat_suc_plus)
  apply(case_tac x3;simp_all add: lnat_suc_plus) 
  using less_lnsuc trans_lnle by blast

lemma tlensmallerbundle:"#\<^sub>\<surd> (a::'cs::tchan\<^sup>\<Omega>) \<le> # a"
  apply(simp add: len_sb_def)
  apply(rule sblengeq')
  apply(rule sbtlenleq')
  apply blast
  apply(rule_tac x="c" in exI)
  apply(rule tlensmallerstream)
  by (metis ctype_timed dual_order.trans sbgetch_ctypewell)

lemma sbleninfgetch:
  assumes"#sb = \<infinity>"
  and "chDom TYPE('cs) \<noteq> {}"
  shows "#(sb \<^enum> (c::'cs)) = \<infinity>"
  using assms
  apply(simp add: len_sb_def)
  by (metis eq_iff inf_ub len_sb_def sblen_min_len)

lemma sbleninfconc:
  assumes"#sb1 = \<infinity>"
  shows"sb1 \<Zcat>\<^sup>\<Omega> sb2 = sb1"
  apply(rule sb_eqI)
  apply(simp)
  apply(rule sconc_fst_inf)
  using assms sbleninfgetch by blast

lemma sbtlen_min_len [simp]:
  assumes"\<not>chDomEmpty(TYPE('c::tchan))"
  shows"#\<^sub>\<surd>(sb :: 'c\<^sup>\<Omega>) \<le> #\<^sub>\<surd>(sb \<^enum> c)"
  apply(simp add: tlen_sb_def assms)
  by (metis (mono_tags, lifting) Least_le)

instantiation sb ::(tchan) wellformed
begin
definition wellformed_sb::"'a sb \<Rightarrow> bool" where
"wellformed_sb sb = (\<forall>c. wellformed (sb \<^enum> c))"

instance
  apply(intro_classes)
  apply(rule exI [of _ "\<bottom>"])
  apply(auto simp add: wellformed_sb_def wellformed_stream_def)[4]
   apply (metis sbleninfgetch sbtlen_empty' sbtlen2stlen)
  using sbtlen_min_len apply (metis Inf'_neq_0_rev SB.slen_empty_eq inf_ub order_antisym_conv)
   apply (metis eq_less_and_fst_inf sbgetch_sbelow)
  apply(rule_tac x="a\<Zcat>\<Zcat>sbInfTlen" in exI)
  apply (rule conjI)
  apply (metis botconc2 conc_belowI minimal)
  apply(rule sbtlengeq')
  apply(subst conc_sb_def, subst sbconc_getch, simp)
  by (metis SB.wellformed_sb_def plus_lnatInf_l sbinftlen_getch_len tlen_wellformed_sconc)

end

lemma wellformed_sb_below:
  fixes x :: "('a::{tchan})\<^sup>\<Omega>"
  assumes "x \<sqsubseteq> y"
    and "wellformed y"
  shows "wellformed x"
  by (metis assms wellformed_sb_def below_lsb_def
      fun_below_iff sbgetch_insert2 wellformed_stream_below)

lemma wellformed_sbI:
  fixes sb::"'csIn::tchan\<^sup>\<Omega>"
  assumes "\<And>c. (Rep c)\<in>chDom (TYPE ('csIn)) \<Longrightarrow> #(sb \<^enum> c) = \<infinity>
           \<Longrightarrow> #\<^sub>\<surd>sb < \<infinity> \<Longrightarrow> #\<^sub>\<surd> (sb \<^enum> c) = \<infinity>"
  shows "wellformed sb"
  apply(cases "chDom (TYPE ('csIn)) = {}")
   apply(auto simp add: wellformed_sb_def wellformed_stream_def)[2]
  apply(cases "#\<^sub>\<surd>sb < \<infinity>")
  using assms chdom_in apply blast
  by (metis emptyE inf_less_eq inf_ub nless_le sbtlen_min_len)

lemma wellsblen2tlen:
  assumes "chDom TYPE('cs::tchan) \<noteq>{}"
  and"# a = \<infinity>"
  and "wellformed a"
shows "#\<^sub>\<surd>(a \<^enum> (c::'cs)) = \<infinity>"
  using assms
  by(simp add: wellformed_sb_def wellformed_stream_def sbleninfgetch)

lemma tschansb_wellformed[simp]:"wellformed (sb::'cs::tschan\<^sup>\<Omega>)"
  apply(simp add: wellformed_sb_def wellformed_stream_def)
  by (metis Inf'_neq_0 SB.slen_empty_eq chdom_in sbgetch_ctypewell tschanlen_eq)

lemma sbconc_well_inf[simp]: "wellformed sb \<Longrightarrow> #\<^sub>\<surd>(sb\<Zcat>\<Zcat>sbInfTlen) = \<infinity>"
  apply(auto simp add: wellformed_sb_def)[1]
  by (metis conc_sb_def inf_less_eq plus_lnatInf_l sbconc_getch sbinftlen_getch_len sbinftlen_len sblen_sbconc tlen_wellformed_sconc tlensmallerbundle well_tlen wellformed_sbI)

lemma wellformed_sbrenamech:
assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "wellformed sb"
  shows "wellformed (sbRenameCh f\<cdot>sb)"
  apply(simp add: wellformed_sb_def)
  apply(subst sbrenamech_getch[OF assms(1)])
  using assms(2) wellformed_sb_def by blast

lemma wellformed_sbtypecast: "wellformed sb \<Longrightarrow> wellformed (sb\<star>)"
  apply(auto simp add: wellformed_sb_def wellformed_stream_def)[1]
  by (metis Inf'_neq_0 sbgetch_insert sbgetch_insert2 slen_zero)

lemma wellformed_union: "wellformed sb1 \<Longrightarrow> wellformed sb2 \<Longrightarrow> wellformed (sb1 \<uplus> sb2)"
  by (metis sbtypecast_getch sbunion_getchl sbunion_getchr wellformed_sb_def wellformed_sbtypecast)

lemma wellformed_union_minus: "wellformed sb1 \<Longrightarrow> wellformed sb2 \<Longrightarrow> wellformed (sb1 \<uplus>\<^sub>- sb2)"
  using wellformed_sbtypecast wellformed_union by blast

lemma wellformed_union_minus_star: "wellformed sb1 \<Longrightarrow> wellformed sb2 \<Longrightarrow> wellformed (sb1 \<uplus>\<^sub>- sb2\<star>)"
  using wellformed_sbtypecast wellformed_union_minus by blast


instance sb::(tschan)tlen_len
  apply(intro_classes)
  apply(rule fun_eqI)
  apply (metis dual_order.eq_iff inf_ub sbgetch_ctypewell sblen_min_len sbtlen_empty' sbtlengeq' tlensmallerbundle tschanlen_eq)
  by simp

instance sb ::(tchan) tlenconc
  apply(intro_classes)
  apply(rule sbtlengeq')
  apply(case_tac "#a \<noteq> \<infinity>")
proof(auto simp add: conc_sb_def)
  fix a b::"'a\<^sup>\<Omega>" and c::'a
  assume a0:"wellformed a"
  assume a1: "#a \<noteq> \<infinity>"
  assume a2:"Rep c \<in> chDom TYPE('a)"
  obtain c1 c2 where c1_def:"#\<^sub>\<surd> a = #\<^sub>\<surd>( a \<^enum> c1)" 
                 and c2_def:"#\<^sub>\<surd> b = #\<^sub>\<surd>( b \<^enum> c2)"
    using sbtlen2stlen a1 sblen_empty by blast
  then have asmaller:"#\<^sub>\<surd>( a \<^enum> c1) \<le> #\<^sub>\<surd>( a \<^enum> c)"
    by (metis a1 eq_iff sblen_empty sbtlenleq')
  have bsmaller:"#\<^sub>\<surd>( b \<^enum> c2) \<le> #\<^sub>\<surd>( b \<^enum> c)"
    by (metis a1 eq_iff sblen_empty c2_def sbtlenleq')
  have "#\<^sub>\<surd> a + #\<^sub>\<surd> b \<le> #\<^sub>\<surd> (a  \<^enum>  c) + #\<^sub>\<surd>(b  \<^enum>  c)"
    by (simp add: asmaller bsmaller c1_def c2_def lessequal_addition)
  moreover have "#\<^sub>\<surd> (a  \<^enum>  c) + #\<^sub>\<surd>(b  \<^enum>  c) \<le> #\<^sub>\<surd> ((a  \<^enum>  c) \<Zcat>\<Zcat> (b  \<^enum>  c))"
    apply(rule tlen_conc)
    using a0 well_tlen wellformed_sb_def by blast
  ultimately show "#\<^sub>\<surd> a + #\<^sub>\<surd> b \<le> #\<^sub>\<surd> ((a  \<^enum>  c) \<Zcat> b  \<^enum>  c)"
    by(simp)
  next
  fix a b::"'a\<^sup>\<Omega>" and c::'a
  assume dom:"Rep c \<in> chDom TYPE('a)"
  assume a1: "#a = \<infinity>"
  assume a2:"wellformed a"
  then have h:"#\<^sub>\<surd>(a  \<^enum>  c) = \<infinity>"
    by (metis a1 dom emptyE sbleninfgetch well_tlen wellformed_sb_def)
  then have "#(a  \<^enum>  c) = \<infinity>"
    using tlensmallerstream
    by (metis a1 dom empty_iff sbleninfgetch)
  thus "#\<^sub>\<surd> a + #\<^sub>\<surd> b \<le> #\<^sub>\<surd> ((a  \<^enum>  c) \<Zcat> b  \<^enum>  c)" 
    by (simp add: h)
  next
  show "\<And>(a::'a\<^sup>\<Omega>) b::'a\<^sup>\<Omega>. #a = \<infinity> \<Longrightarrow> a \<Zcat>\<^sup>\<Omega> b = a"
    using sbleninfconc by blast
qed

instance sb ::(tchan) tlen_inf
  apply(intro_classes)
  using inf_less_eq sbinftlen_len by blast


theorem sbtlen_rule:
  fixes sb::"'cs::tchan\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)" 
      and "\<And>c. k \<le> #\<^sub>\<surd>(sb \<^enum> c)"
      and "\<exists>c. #\<^sub>\<surd>(sb \<^enum> c) = k"
    shows "#\<^sub>\<surd>sb = k"
  by (metis assms(1) assms(2) assms(3) sbtlen2stlen_h)

lemma sbtlen_all_rule:
  fixes sb::"'cs::tchan\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)" 
      and "\<And>c. #\<^sub>\<surd>(sb \<^enum> c) = k"
    shows "#\<^sub>\<surd>sb = k"
  by (metis assms(1) assms(2) sbtlen2stlen)

lemma sbtypecast_tlen:
  assumes "chDom TYPE('cs2::tchan) \<subseteq> chDom TYPE('cs1::tchan)"
  shows "#\<^sub>\<surd>sb \<le> #\<^sub>\<surd>((sbTypeCast_abbr :: 'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega>) sb)"
  proof (cases "chDomEmpty TYPE('cs2)")
  case True
  then show ?thesis
    by simp
  next
  case cs2_typenempty: False
  obtain least_ch where least_ch1_def: "#\<^sub>\<surd>sb = #\<^sub>\<surd>(sb \<^enum> least_ch)"
    by (metis cs2_typenempty assms empty_subsetI equalityI
        order.trans sbtlen2stlen)
  have cs2_sbtypecast_getch: "\<And>c::'cs2. sb\<star> \<^enum> c = sb \<^enum>\<^sub>\<star> c"
    by simp
  thus ?thesis
  proof (cases "Rep least_ch \<in> chDom TYPE('cs2)")
    case least_ch_in_cs2: True
    then show ?thesis
      apply (simp add: least_ch1_def)
    proof -
      assume "Rep least_ch \<in> chDom (TYPE('cs2)::'cs2 itself)"
      then have f1: "chDom (TYPE('cs1)::'cs1 itself) \<noteq> {}"
        using assms by blast
      obtain cc :: "'cs2\<^sup>\<Omega> \<Rightarrow> lnat \<Rightarrow> 'cs2" where
        f2: "\<forall>x0 x1. (\<exists>v2. Rep v2 \<in> chDom (TYPE('cs2)::'cs2 itself) \<and> \<not> x1 \<le> #\<^sub>\<surd> (x0 \<^enum> v2)) = (Rep (cc x0 x1) \<in> chDom (TYPE('cs2)::'cs2 itself) \<and> \<not> x1 \<le> #\<^sub>\<surd> (x0 \<^enum> cc x0 x1))"
        by moura
      moreover
      { assume "(#\<^sub>\<surd> sb \<le> #\<^sub>\<surd> (sb \<^enum> Abs (Rep (cc (sb\<star>) (#\<^sub>\<surd> (sb \<^enum> least_ch)))))) \<noteq> (#\<^sub>\<surd> (sb \<^enum> least_ch) \<le> #\<^sub>\<surd> (sb\<star> \<^enum> cc (sb\<star>) (#\<^sub>\<surd> (sb \<^enum> least_ch))))"
        then have "Rep (cc (sb\<star>) (#\<^sub>\<surd> (sb \<^enum> least_ch))) \<notin> chDom (TYPE('cs1)::'cs1 itself)"
          by (metis (full_types) least_ch1_def sbGetCh.rep_eq sbgetch_insert2 sbtypecast_getch)
        then have "#\<^sub>\<surd> (sb \<^enum> least_ch) \<le> #\<^sub>\<surd> (sb\<star>::'cs2\<^sup>\<Omega>)"
          using f2 by (meson assms sbtlengeq' subsetD) }
      ultimately show "#\<^sub>\<surd> (sb \<^enum> least_ch) \<le> #\<^sub>\<surd> (sb\<star>::'cs2\<^sup>\<Omega>)"
        using f1 by (meson sbtlen_min_len sbtlengeq')
    qed
  next
    case least_ch_nin_cs2: False
    then show ?thesis
      apply (simp add: least_ch1_def)
      by (metis (mono_tags, opaque_lifting) assms chdom_in cs2_typenempty 
          least_ch1_def sbGetCh.rep_eq sbgetch_empty2 sbgetch_insert2 
          sbtlen2stlen sbtlen_min_len sbtypecast_getch subsetD)
  qed
qed

lemma sbunion_magic_tlen_fst:
  fixes sb1 :: "'cs1::tchan\<^sup>\<Omega>"
  and   sb2 :: "'cs2\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs2)" 
    and "\<not>chDomEmpty TYPE('cs1)"
    and "chDom TYPE('cs3::tchan) = chDom TYPE('cs1)"
  shows "#\<^sub>\<surd>((sb1 \<uplus>\<^sub>\<star> sb2)::'cs3\<^sup>\<Omega>) = #\<^sub>\<surd>sb1"
  proof-
  obtain least_ch::'cs1 where 
    sb2_len_chdef: "#\<^sub>\<surd>sb1 = #\<^sub>\<surd>(sb1 \<^enum>\<^sub>\<star> least_ch)"
    by (metis assms(2) sbtlen2stlen)
  thus ?thesis
    apply (subst sbunion_conv_fst)
    apply (simp add: assms; fail)
    apply (rule sbtlen_rule [where k="#\<^sub>\<surd>sb1"])
    using assms apply blast
    apply (metis assms(2) assms(3) cnotempty_cdom sbgetch_insert
           sbgetch_insert2 sbtlen_min_len sbtypecast_getch)
    apply (rule_tac x="(Abs (Rep least_ch))" in exI)
    by (simp add: assms(2) assms(3) sbgetch_insert)
qed

lemma sbunion_magic_tlen_snd:
  fixes sb1 :: "'cs1\<^sup>\<Omega>"
  and   sb2 :: "'cs2::tchan\<^sup>\<Omega>"
  assumes "chDomEmpty TYPE('cs1)" 
  and "\<not>chDomEmpty TYPE('cs2)"
  and "chDom TYPE('cs3::tchan) = chDom TYPE('cs2)"
  shows "#\<^sub>\<surd>((sb1 \<uplus>\<^sub>\<star> sb2)::'cs3\<^sup>\<Omega>) = #\<^sub>\<surd>sb2"
  proof-
  obtain least_ch::'cs2 where
    sb2_len_chdef: "#\<^sub>\<surd>sb2 = #\<^sub>\<surd>(sb2 \<^enum>\<^sub>\<star> least_ch)"
    by (metis assms(2) sbtlen2stlen)
  thus ?thesis
    apply (subst sbunion_conv_snd)
    apply (simp add: assms; fail)
    apply (rule sbtlen_rule [where k="#\<^sub>\<surd>sb2"])
    using assms apply blast
    apply (metis assms(2) assms(3) cnotempty_cdom sbgetch_insert
           sbgetch_insert2 sbtlen_min_len sbtypecast_getch)
    apply (rule_tac x="(Abs (Rep least_ch))" in exI)
    by (simp add: assms sbgetch_insert)
qed

lemma sbunion_tlen[simp]:
  fixes sb1 :: "'cs1::tchan\<^sup>\<Omega>"
  and   sb2 :: "'cs2::tchan\<^sup>\<Omega>"
  assumes "chDom TYPE('cs1) \<inter> chDom TYPE('cs2) = {}"
  shows "#\<^sub>\<surd>(sb1 \<uplus> sb2) = min (#\<^sub>\<surd>sb1) (#\<^sub>\<surd>sb2)"
  proof (cases "chDomEmpty TYPE('cs1)")
  case cs1_dom_empty: True
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case cs2_dom_empty: True
    thus?thesis
      by (simp add: assms cs1_dom_empty)
  next
    case False
    then show ?thesis
      apply (subst(2) sbconv_eq [symmetric])
      apply (subst sbunion_magic_tlen_snd)
      by (simp_all add: cs1_dom_empty)
    qed
  next
  case cs1_dom_nempty: False
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case True
    then show ?thesis
      apply (subst(2) sbconv_eq [symmetric])
      apply (subst sbunion_magic_tlen_fst)
      by (simp_all add: cs1_dom_nempty)
  next
    case cs2_dom_nempty: False
    obtain least_cs1::'cs1 where 
      sb1_len_chdef: "#\<^sub>\<surd>sb1 = #\<^sub>\<surd>(sb1 \<^enum>\<^sub>\<star> least_cs1)"
      by (meson cs1_dom_nempty sbtlen2stlen)
    obtain least_cs2::'cs2 where
      sb2_len_chdef: "#\<^sub>\<surd>sb2 = #\<^sub>\<surd>(sb2 \<^enum>\<^sub>\<star> least_cs2)"
      by (meson cs2_dom_nempty sbtlen2stlen)
    have least_cs1_dom: "Rep least_cs1 \<in> chDom TYPE('cs1)"
      by (simp add: cs1_dom_nempty)
    have least_cs1_dom: "Rep least_cs2 \<in> chDom TYPE('cs2)"
      by (simp add: cs2_dom_nempty)
    then show ?thesis
      apply (subst sbtlen_rule [where k="min (#\<^sub>\<surd>sb1) (#\<^sub>\<surd>sb2)"])
      apply (simp_all add: assms cs1_dom_nempty)
      apply (rule_tac c="c" and S="chDom TYPE('cs1)" in chan_case)
      apply auto[2]
      apply (metis cs1_dom_nempty min.coboundedI1 sbGetCh.rep_eq sbgetch_insert2 sbtlen_min_len)
      apply (auto simp add: sbgetch_insert)[1]
      apply (metis cs2_dom_nempty min_le_iff_disj sbgetch_insert2
             sbtlen_min_len)
      using union_empty apply auto[1]
      apply (cases "min (#\<^sub>\<surd>sb1) (#\<^sub>\<surd>sb2) = #\<^sub>\<surd>sb1", simp_all)
      apply (rule_tac x="Abs (Rep least_cs1)" in exI)
      apply (simp add: sbgetch_insert)
      apply (simp add: assms cs1_dom_nempty sb1_len_chdef
             sbgetch_insert sbunion_rep_eq; fail)
      apply (rule_tac x="Abs (Rep least_cs2)" in exI)
      apply (subgoal_tac "min (#\<^sub>\<surd>sb1) (#\<^sub>\<surd>sb2) = #\<^sub>\<surd>sb2")
      apply (simp add: sbgetch_insert)
      apply (simp add: assms cs2_dom_nempty sb2_len_chdef
             sbgetch_insert sbunion_rep_eq)
      using assms(1) least_cs1_dom apply blast
      by (metis min_def)
  qed
qed

lemma sbtlen_conc_eq: 
  assumes "\<And>c.#\<^sub>\<surd>((sb1::'cs::{tchan}\<^sup>\<Omega>) \<^enum> c) = k"
  and "wellformed sb1"
  shows "(#\<^sub>\<surd>(sb1 \<Zcat>\<^sup>\<Omega> sb2)) = (#\<^sub>\<surd>sb2) + k"
  apply(cases  "chDomEmpty(TYPE('cs))",simp)
  apply(subgoal_tac "#\<^sub>\<surd>sb1 = k")
proof(rule sbtlen_rule,simp)
  fix c::'cs
  assume chdom:"chDom TYPE('cs) \<noteq>{}"
  assume sbtlen:"#\<^sub>\<surd> sb1= k"
  then have "#\<^sub>\<surd> ((sb1::'cs\<^sup>\<Omega>) \<Zcat>\<^sup>\<Omega> (sb2::'cs\<^sup>\<Omega>)) \<le> #\<^sub>\<surd> (sb1 \<Zcat>\<^sup>\<Omega> sb2  \<^enum>  c)"
    using sbtlen_min_len chdom by blast
  moreover have "#\<^sub>\<surd> sb1 + #\<^sub>\<surd> sb2 \<le> #\<^sub>\<surd> ((sb1::'cs\<^sup>\<Omega>) \<Zcat>\<^sup>\<Omega> (sb2::'cs\<^sup>\<Omega>))"
    apply(simp add: conc_sb_def[symmetric])
    apply(rule tlen_conc)
    by(simp add: assms(2))
  ultimately show "#\<^sub>\<surd> sb2 + k \<le> #\<^sub>\<surd> (sb1 \<Zcat>\<^sup>\<Omega> sb2  \<^enum>  c)"
    apply(subst lnat_plus_commu,subst sbtlen[symmetric])
    using trans_lnle by blast
next
  assume chdom_cs_nempty: "chDom TYPE('cs) \<noteq> {}" and sb1_tlen: "#\<^sub>\<surd> sb1 = k"
  then obtain c where c_def: "#\<^sub>\<surd> sb2 = #\<^sub>\<surd>(sb2 \<^enum> c)"
    using sbtlen2stlen by blast
  have wellformed_sb1_c: "wellformed (sb1 \<^enum> c)"
    using assms(2) wellformed_sb_def by blast
  thus "\<exists>c::'cs. #\<^sub>\<surd> (sb1 \<Zcat>\<^sup>\<Omega> sb2  \<^enum>  c) = #\<^sub>\<surd> sb2 + k"
    apply (rule_tac x="c" in exI)
    apply (simp add: tlen_wellformed_sconc wellformed_sb1_c)
    by (metis add.commute assms(1) c_def)
next
  show "chDom TYPE('cs) \<noteq> {} \<Longrightarrow> #\<^sub>\<surd> sb1 = k"
    using assms sbtlen_all_rule by blast
qed

lemma sbtlen_sbconc_eq: 
  assumes "\<And>c.#\<^sub>\<surd>((sb1::'cs::{tschan}\<^sup>\<Omega>) \<^enum> c) = k" 
  shows "(#\<^sub>\<surd>(sb1 \<Zcat>\<^sup>\<Omega> sb2)) = (#\<^sub>\<surd>sb2) + k"
  using assms sbtlen_conc_eq tschansb_wellformed by blast

lemma tlen_sbecons[simp]:
  "#\<^sub>\<surd> (sbe \<Zcat>\<^sup>\<surd> (sb::('cs::tschan)\<^sup>\<Omega>)) = lnsuc\<cdot>(#\<^sub>\<surd>sb)"
  apply (cases "chDomEmpty TYPE('cs)")
  apply (simp; fail)
  apply (subst sbtlen_sbconc_eq [where k="#\<^sub>\<surd>(sbe2sb sbe)"])
  apply (metis sbe2slen_1 sbelen_one sbgetch_ctypewell sbgetch_empty sbgetch_sbe2sb_nempty
      tlen_len_eq tschanlen_eq)
  by (metis lnat_plus_suc sbelen_one tlen_len_eq)

lemma sbunion_tlen_fst_leq[simp]:
  fixes sb1 :: "'cs1::tchan\<^sup>\<Omega>"
  and   sb2 :: "'cs2::tchan\<^sup>\<Omega>"
  assumes "#\<^sub>\<surd>sb1 \<le> #\<^sub>\<surd>sb2"
  shows "#\<^sub>\<surd>(sb1 \<uplus> sb2) = #\<^sub>\<surd>sb1"
  proof (cases "chDomEmpty TYPE('cs1)")
  case True
  then show ?thesis
    using assms by simp
  next
  case cs1_nempty: False
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case True
    then show ?thesis
      by simp
  next
    case cs2_nempty: False
    hence cs1_cs2_union_nempty: "\<not>chDomEmpty TYPE('cs1 \<union> 'cs2)"
      by simp
    then obtain c where c_def: "#\<^sub>\<surd>(sb1 \<uplus> sb2) = #\<^sub>\<surd>(sb1 \<uplus> sb2 \<^enum> c)"
      using sbtlen2stlen by blast
    hence c_in_dom_cs1_cs2:
      "Rep c \<in> chDom TYPE('cs1 \<union> 'cs2)"
      using chdom_in cs1_cs2_union_nempty by blast
    have c_nin_dom_union_eq:
      "Rep c \<notin> chDom (TYPE('cs1)) \<Longrightarrow> (sb1 \<uplus> sb2) \<^enum> c = sb2 \<^enum>\<^sub>\<star> c"
      using sbunion_getchr by blast
    have c_in_dom_sb1_leq: 
      "Rep c \<in> chDom (TYPE('cs1)) \<Longrightarrow> #\<^sub>\<surd>sb1 \<le> #\<^sub>\<surd>(sb1 \<^enum>\<^sub>\<star> c)"
      by (metis cs1_nempty sbGetCh.rep_eq sbgetch_insert2 sbtlen_min_len)
    have h1: "Rep c \<notin> chDom (TYPE('cs1)) \<Longrightarrow> #\<^sub>\<surd>sb2 \<le> #\<^sub>\<surd>(sb2 \<^enum>\<^sub>\<star> c)"
    proof -
      assume "Rep c \<notin> chDom (TYPE('cs1)::'cs1 itself)"
      then have "Rep c \<in> chDom (TYPE('cs2)::'cs2 itself)"
        using cs1_cs2_union_nempty union_empty by blast
      then show ?thesis
        by (metis (full_types) cs2_nempty sbGetCh.rep_eq sb_tlenminc_exists sbgetch_insert2 sbtlenleq')
    qed
    have h2: "#\<^sub>\<surd>(sb1 \<uplus> sb2) \<le> #\<^sub>\<surd>sb1"
      using c_def
      by (metis Un_iff chdom_union sbtypecast_tlen sbunion_fst subsetI)
    have "#\<^sub>\<surd>sb1 \<le> #\<^sub>\<surd>(sb1 \<uplus> sb2)"
      by (metis (no_types, lifting) assms c_def c_in_dom_sb1_leq c_nin_dom_union_eq h1 sbunion_getchl trans_lnle)
    then show ?thesis
      using h2 less2eq by presburger
  qed
qed

lemma sbunion_tlen_fst_leq_old:
  assumes "#\<^sub>\<surd>sb1 \<le> #\<^sub>\<surd>sb2"
  shows "#\<^sub>\<surd>sb1 \<le>  #\<^sub>\<surd>(sb1 \<uplus> sb2)"
  by (metis assms eq_refl sbunion_tlen_fst_leq)

lemma sbunion_minus_tlen_fst_leq:
  assumes "#\<^sub>\<surd>sb1 \<le> #\<^sub>\<surd>sb2"
  shows "#\<^sub>\<surd>sb1 \<le> #\<^sub>\<surd>(sb1 \<uplus>\<^sub>- sb2)"
  apply (subst sbunion_tlen_fst_leq [symmetric])
  using assms apply blast
  by (simp add: sbtypecast_tlen)

lemma sbunion_tlen_snd_leq:
  fixes sb1 :: "'cs1::tchan\<^sup>\<Omega>"
  and   sb2 :: "'cs2::tchan\<^sup>\<Omega>"
  assumes "#\<^sub>\<surd>sb2 \<le> #\<^sub>\<surd>sb1"
  shows "#\<^sub>\<surd>sb2 \<le> #\<^sub>\<surd>(sb1 \<uplus> sb2)"
  proof (cases "chDomEmpty TYPE('cs1)")
  case True
  then show ?thesis
    using assms apply (simp add: sbunion_emptyl)
    by (metis order_refl sbtypecast_tlen uniondom_fstempty)
  next
  case cs1_nempty: False
  then show ?thesis
  proof (cases "chDomEmpty TYPE('cs2)")
    case True
    then show ?thesis
      using assms by auto
  next
    case cs2_nempty: False
    hence cs1_cs2_union_nempty: "\<not>chDomEmpty TYPE('cs1 \<union> 'cs2)"
      by simp
    then obtain c where c_def: "#\<^sub>\<surd>(sb1 \<uplus> sb2) = #\<^sub>\<surd>(sb1 \<uplus> sb2 \<^enum> c)"
      using sbtlen2stlen by blast
    hence c_in_dom_cs1_cs2:
      "Rep c \<in> chDom TYPE('cs1 \<union> 'cs2)"
      using chdom_in cs1_cs2_union_nempty by blast
    have c_nin_dom_union_eq:
      "Rep c \<notin> chDom (TYPE('cs1)) \<Longrightarrow> (sb1 \<uplus> sb2) \<^enum> c = sb2 \<^enum>\<^sub>\<star> c"
      using sbunion_getchr by blast
    have c_in_dom_sb1_leq: 
      "Rep c \<in> chDom (TYPE('cs1)) \<Longrightarrow> #\<^sub>\<surd>sb1 \<le> #\<^sub>\<surd>(sb1 \<^enum>\<^sub>\<star> c)"
      by (metis cs1_nempty sbGetCh.rep_eq sbgetch_insert2 sbtlen_min_len)
    have "Rep c \<notin> chDom (TYPE('cs1)) \<Longrightarrow> #\<^sub>\<surd>sb2 \<le> #\<^sub>\<surd>(sb2 \<^enum>\<^sub>\<star> c)"
    proof -
      assume "Rep c \<notin> chDom (TYPE('cs1)::'cs1 itself)"
      then have "Rep c \<in> chDom (TYPE('cs2)::'cs2 itself)"
        using cs1_cs2_union_nempty union_empty by blast
      then show ?thesis
        by (metis (full_types) cs2_nempty order_refl sbGetCh.rep_eq sbgetch_insert2 sbtlenleq')
    qed
    thus ?thesis
      by (metis assms c_def c_in_dom_sb1_leq c_nin_dom_union_eq
          order.trans sbunion_getchl)
  qed
qed

lemma sbunion_minus_tlen_snd_leq:
  assumes "#\<^sub>\<surd>sb2 \<le> #\<^sub>\<surd>sb1"
  shows "#\<^sub>\<surd>sb2 \<le> #\<^sub>\<surd>(sb1 \<uplus>\<^sub>- sb2)"
  proof -
  have "#\<^sub>\<surd>sb2 \<le> #\<^sub>\<surd>(sb1 \<uplus> sb2)"
    by  (simp add: assms sbunion_tlen_snd_leq)
  moreover have " #\<^sub>\<surd>(sb1 \<uplus> sb2)  \<le> #\<^sub>\<surd>(sb1 \<uplus>\<^sub>- sb2)" 
    by (simp add: sbtypecast_tlen)
  ultimately show ?thesis
    using order_trans by blast
  qed

lemma sbrenamech_tlen[simp]: 
  fixes f::"('cs1::tchan) \<Rightarrow> ('cs2::tchan)"
  assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "\<not>chDomEmpty TYPE('cs2)"
  shows "#\<^sub>\<surd>sb \<le> #\<^sub>\<surd>(sbRenameCh f\<cdot>sb)"
  by (simp add: assms sbtlengeq')



lift_definition ticksb::"'cs::{echan} sb" is
"\<lambda>c. if chDom TYPE('cs) = {} then \<bottom> else \<up>(Timed (TLive Tick)) "
  apply(rule lsbwellI)
  by(simp add: ctype_echan_def)

lemma ticksb_insert:assumes "chDom TYPE ('cs::echan) \<noteq> {}"
  shows"Rep_lsb (ticksb::'cs::echan sb) = (\<lambda>c. \<up>(Timed (TLive Tick)))"
  by(simp add: assms ticksb.rep_eq)


lemma ticksblnsuc[simp]:"#\<^sub>\<surd>(ticksb \<Zcat>\<^sup>\<Omega> sb) = lnsuc\<cdot>(#\<^sub>\<surd> sb)"
  apply(cases "chDom TYPE ('a) = {}",simp)
  apply(rule less2eq)
   apply(rule sbtlenleq',simp_all)
proof(simp add: sbgetch_insert ticksb.rep_eq)
  assume "chDom TYPE('a) \<noteq> {}"
  then obtain c where sblen_def:"#\<^sub>\<surd> sb = #\<^sub>\<surd>(sb \<^enum> c)"
    using sbtlen2stlen by blast
  show "\<exists>c::'a. (1::lnat) + #\<^sub>\<surd> (Rep_lsb sb c) \<le> lnsuc\<cdot>(#\<^sub>\<surd> sb)"
   by(rule exI[where x=c],simp add: sblen_def sbgetch_insert2 lnat_suc_plus)
next
  assume a1:"chDom TYPE('a) \<noteq>{}"
  then obtain c where sblen_def:"#\<^sub>\<surd> sb = #\<^sub>\<surd>(sb \<^enum> c)"
    using sbtlen2stlen by blast
  have "lnsuc\<cdot>(#\<^sub>\<surd> (sb \<^enum> c)) \<le> #\<^sub>\<surd>(ticksb \<Zcat>\<^sup>\<Omega> sb) "
    apply(rule sbtlengeq',simp)
    apply (simp add: sbgetch_insert2 a1 ticksb.rep_eq)
    by (metis a1 lnat_suc_plus lnsuc_lnle_emb sb_tlenminc_exists sbgetch_insert2 sblen_def sbtlen2stlen_h)
  then show "#\<^sub>\<surd> sb <\<^sup>l #\<^sub>\<surd> (ticksb \<Zcat>\<^sup>\<Omega> sb)"
    by(simp add: sblen_def)
qed

lemma sb_echan_smapstream:"\<exists> s. (sb::'cs::{echan}\<^sup>\<Omega>) \<^enum> c = smap (Timed o TLive)\<cdot>s"
  apply(simp add: sbgetch_insert2)
  apply(cases "chDom TYPE('cs) = {}")
proof(rule_tac x="\<epsilon>" in exI,simp)
  assume chdom:"chDom TYPE('cs) \<noteq>{}"
  have "sValues\<cdot>(Rep_lsb sb c) \<subseteq> ctype (Rep c)"
    using lsb_well_def rep_sb_well by blast
  then have "sValues\<cdot>(Rep_lsb sb c) \<subseteq> (Timed \<circ> TLive) ` ({Tick} \<union> EventMsg ` cMsg (Rep c))"
    by(simp add: chdom ctype_echan_def)
  then show "\<exists>s::msg event stream. Rep_lsb sb c = smap (Timed \<circ> TLive)\<cdot>s"
    by (metis smap_obtainin)
qed

lemma sb_singleton_zerolen_bot: fixes sb::"'cs::chan\<^sup>\<Omega>" 
  assumes "#sb = (0::lnat)" and "is_singleton (chDom TYPE('cs))"
  shows "sb = \<bottom>" 
  apply(rule sb_eqI)
  apply simp
  using assms(1) assms(2) sbgetch_bot sbleast2bot sbnleast_len by blast


lemma tlen_tlensbn_eq: "tlen (sb::('cs::tchan sb)) = tlen_sbn sb"
  apply(simp add: tlen_sb_def tlen_sbn_def)
  apply rule
  apply(subgoal_tac "chDom TYPE('cs) \<noteq> {} \<Longrightarrow> (\<And>c. #\<^sub>\<surd> (Rep_sb sb c) = #\<^sub>\<surd> (Rep_lsb sb c))")
  apply (simp add: sbgetch_insert2)
  apply(simp add: tlen_combinedstream_def)
  apply(simp add: Rep_lsb_def sbnew2legacy_def combined2mstream_def)
  apply(case_tac "Rep_sb sb c",simp_all add: combstreamcases_insert smap_tlen)
  apply(subgoal_tac "cTime (Rep c) \<noteq> TUntimed")
  using rep_untimed apply blast
  using tchan_class.sometschan apply blast
  by (simp add: smap_list_tlen)
end

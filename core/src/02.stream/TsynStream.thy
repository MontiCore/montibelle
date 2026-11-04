

theory TsynStream
imports StreamFilter StreamScanl EventStream inc.TSynDatatype

begin



text \<open>@{term tsynValues}: Obtain the set of all stream messages.\<close>
definition tsynValues :: "'a tsyn stream \<rightarrow> 'a set" where
  "tsynValues \<equiv> \<Lambda> s. {m | m. (TSynMsg m) \<in> sValues\<cdot>s}"

text \<open>@{term tsyn2ustreamElem}: Return the corresponding non tsyn element.\<close>
fun tsyn2ustreamElem :: "'a tsyn \<Rightarrow> 'a" where
  "tsyn2ustreamElem Eps = undefined " |
  "tsyn2ustreamElem (TSynMsg a) = a"

text \<open>@{term tsyn2ustream}: Filter the Epss and return the corresponding stream.\<close>
definition tsyn2ustream:: "'a tsyn stream \<rightarrow> 'a stream" where
  "tsyn2ustream \<equiv> \<Lambda> s. smap tsyn2ustreamElem\<cdot>(sfilter {e. e \<noteq> Eps}\<cdot>s)"

abbreviation tsyn2ustream_abbr :: "'a tsyn stream \<Rightarrow> 'a stream"
 ("_\<^sup>-" [1000]) where "s\<^sup>- \<equiv> tsyn2ustream\<cdot>s"

text \<open>@{term tsynEps}: Return the number of Epss of in a stream.\<close>
definition tsynEps::"'a::countable tsyn stream \<rightarrow> lnat"where
  "tsynEps \<equiv> \<Lambda> ts. #(sfilter {Eps}\<cdot>ts)"

text \<open>@{term tsynLen}: Return the number of messages.\<close>
definition tsynLen:: "'a tsyn stream \<rightarrow> lnat" where 
  "tsynLen \<equiv> \<Lambda> s. #s\<^sup>-"

abbreviation tsynLen_abbr :: "'a tsyn stream \<Rightarrow> lnat" ("#\<^sub>-_" [1000] 999) where
  "#\<^sub>-s == tsynLen\<cdot>s"

text \<open>@{term tsynApplyElem}: Apply the function direct to the message.\<close>
fun tsynApplyElem :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn \<Rightarrow> 'b tsyn" where
  "tsynApplyElem _ Eps = Eps" |
  "tsynApplyElem f (TSynMsg a) = TSynMsg (f a)"

text \<open>@{term tsynMap}: Apply a function to all elements of the stream.\<close>
definition tsynMap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynMap f = smap (tsynApplyElem f)"

text\<open>@{term tsynFst}: Access the first element of a pair.\<close>
fun tsynFst :: "('a \<times> 'b) tsyn \<Rightarrow> 'a tsyn" where
  "tsynFst Eps = Eps" |
  "tsynFst (TSynMsg x) = TSynMsg (fst x)"

text\<open>@{term tsynSnd}: Access the second element of a pair .\<close>
fun tsynSnd :: "('a \<times> 'b) tsyn \<Rightarrow> 'b tsyn" where
  "tsynSnd Eps = Eps" |
  "tsynSnd (TSynMsg x) = TSynMsg (snd x)"

text \<open>tsynRemDups removes consecutive duplicates from a time-synchronous stream 
by replacing them with @{term "\<sim>"}\<close>


fun tsynRemDups_h :: "'a::countable tsyn \<Rightarrow> 'a tsyn \<Rightarrow> ('a tsyn \<times> 'a tsyn)" where
"tsynRemDups_h x \<sim> = (x, \<sim>)" |
"tsynRemDups_h x y = (if x = y then (x, \<sim>) else (y, y))"


definition tsynRemDups :: "'a::countable tsyn stream \<rightarrow> 'a tsyn stream" where
"tsynRemDups = sscanlAOne tsynRemDups_h \<sim>"

abbreviation tsynRemDups_abbr :: "'a tsyn stream \<Rightarrow> 'a tsyn stream" ("\<alpha>\<^sub>-_" [1000] 999) where
"\<alpha>\<^sub>- s == tsynRemDups\<cdot>s "

text\<open>@{term tsynProjFst}: Access the first stream of two zipped streams .\<close>
definition tsynProjFst :: "('a \<times> 'b) tsyn stream \<rightarrow> 'a tsyn stream" where
"tsynProjFst = smap tsynFst"

abbreviation tsynProjFst_abbr :: "('a \<times> 'b) tsyn stream \<Rightarrow> 'a tsyn stream"  ("\<Pi>\<^sub>1\<^sub>-_" [1000] 999) where
"\<Pi>\<^sub>1\<^sub>- s == tsynProjFst\<cdot>s"

text\<open>@{term tsynProjSnd}: Access the second stream of two zipped streams.\<close>
definition tsynProjSnd :: "('a \<times> 'b) tsyn stream \<rightarrow> 'b tsyn stream" where
"tsynProjSnd = smap tsynSnd"

abbreviation tsynProjSnd_abbr :: "('a \<times> 'b) tsyn stream \<Rightarrow> 'b tsyn stream"  ("\<Pi>\<^sub>2\<^sub>-_" [1000] 999) where
"\<Pi>\<^sub>2\<^sub>- s == tsynProjSnd\<cdot>s"

text \<open>@{term tsynFilterElem}: Replace elements not inside the set with a emtpy time-slot.\<close>
fun tsynFilterElem :: "('a set) \<Rightarrow> 'a tsyn \<Rightarrow> 'a tsyn" where
  "tsynFilterElem _ Eps = Eps" |
  "tsynFilterElem A (TSynMsg a) = (if a \<notin> A then Eps else (TSynMsg a))"

text \<open>@{term tsynFilter}: Remove all elements from the stream which are not included in the given
        set.\<close>
definition tsynFilter :: "'a set \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynFilter A = smap (tsynFilterElem A)"

abbreviation tsynFilter_abbr :: "'a set \<Rightarrow> 'a tsyn stream \<Rightarrow> 'a tsyn stream" 
  ("(_ \<ominus>\<^sub>- _)" [66, 65] 65) where "F \<ominus>\<^sub>- s \<equiv> tsynFilter F\<cdot>s"


text \<open>@{term tsynZip}: Merge a tysn stream with a stream.\<close>
fixrec tsynZip :: "'a tsyn stream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tsyn stream" where
  "tsynZip\<cdot>\<epsilon>\<cdot>s = \<epsilon>" |
  "tsynZip\<cdot>s\<cdot>\<epsilon> = \<epsilon>" |
  "tsynZip\<cdot>(up\<cdot>a && as)\<cdot>(up\<cdot>b && bs) = (
     if (undiscr a) = Eps then \<up>Eps \<Zcat> tsynZip\<cdot>as\<cdot>(up\<cdot>b && bs)
     else \<up>(TSynMsg ((invMsg (undiscr a)), (undiscr b))) \<Zcat> tsynZip\<cdot>as\<cdot>bs 
  )"

fun zipOrElse:: "('a tsyn \<times> 'b tsyn) \<Rightarrow> ('a \<times> 'b) tsyn" where
"zipOrElse ((TSynMsg a),(TSynMsg b)) = TSynMsg (a,b)" |
"zipOrElse _  = Eps"

definition tsynZipAlt:: "'a tsyn stream \<rightarrow> 'b tsyn stream \<rightarrow> ('a \<times> 'b) tsyn stream" where
"tsynZipAlt = (\<Lambda> a b. smap zipOrElse\<cdot>(szip\<cdot>a\<cdot>b))"

text \<open>@{term tsynBoolFilter}: forwards values from the input stream
      only at positions where the Boolean stream is @{term True};
      otherwise @{term Eps} is produced..\<close>
definition tsynBoolFilter:: "'a tsyn stream \<rightarrow> bool stream \<rightarrow> 'a tsyn stream" where
"tsynBoolFilter \<equiv> \<Lambda> i ora.  \<Pi>\<^sub>1\<^sub>-({d. snd d} \<ominus>\<^sub>- tsynZip\<cdot>i\<cdot>ora)"



text \<open>Cardinality of the set @{term sValues} is smaller or equal to the length of the original 
        stream.\<close>
lemma sValues_slen: assumes "#s = Fin k" shows "card (sValues\<cdot>s) \<le> k"
  proof -
    have sValues_def_assm: "sValues\<cdot>s = {snth n s | n :: nat. n < k}" 
      by (simp add: assms sValues_def2)
    then have "{snth n s | n :: nat. n < k} \<subseteq> (\<lambda> n. snth n s) ` {i :: nat. i < k}" 
      by blast
    then have "card {snth n s | n :: nat. n < k} \<le> card {i :: nat. i < k}" 
      using surj_card_le by blast
    then show ?thesis 
      by (simp add: sValues_def_assm)
  qed


lemma tsyn_finind [case_names fin bot msg Eps]:
  assumes fin: "#x < \<infinity>"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P s \<Longrightarrow> P (\<up>(TSynMsg m) \<Zcat> s)"
    and Eps: "\<And>s. P s \<Longrightarrow> P (\<up>Eps \<Zcat> s)"
  shows "P x"
  using assms
  proof (induction x rule: ind)
    case 1
    then show ?case 
      by simp
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    then show ?case 
      by (metis fold_inf inf_ub less_le slen_scons tsyn.exhaust)
  qed

lemma tsyn_ind [case_names adm bot msg Eps]:
  assumes adm: "adm P"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P s \<Longrightarrow> P (\<up>(TSynMsg m) \<Zcat> s)"
    and Eps: "\<And>s. P s \<Longrightarrow> P (\<up>Eps \<Zcat> s)"
  shows "P x"
  using assms 
  apply (induction rule: ind [of _ x])
  apply (simp_all add: adm bot)
  by (metis tsyn.exhaust msg Eps)

lemma tsyn_cases [case_names bot msg Eps]:
  assumes bot: "x = \<epsilon> \<Longrightarrow> P \<epsilon>"
    and msg: "\<And>m s. x = \<up>(TSynMsg m) \<Zcat> s \<Longrightarrow> P x"
    and Eps: "\<And> s. x = \<up>Eps \<Zcat> s \<Longrightarrow> P x"
  shows "P x"
  using assms
  apply (cases rule: scases [of x])
  apply (simp add: bot)
  by (metis tsyn.exhaust)


text \<open>@{term tsynValues} is a monotonous function.\<close>
lemma tsyndom_monofun [simp]: "monofun (\<lambda>s. {m | m. (X m) \<in> sValues\<cdot>s})"
  apply (rule monofunI)
  apply (simp add: set_cpo_simps(1))
  by (meson Collect_mono sValues_prefix subsetCE)

text \<open>@{term tsynValues} is a continous function.\<close>
lemma tsyndom_cont [simp]: "cont (\<lambda>s. {m | m. (X m) \<in> sValues\<cdot>s})"
  apply (rule contI2)
  apply (simp only: tsyndom_monofun)
  apply (simp add: set_cpo_simps(1))
  apply (rule subsetI)
  by (simp add: image_iff lub_eq_Union sValues_cont2)

text \<open>@{term tsynValues} insertion lemma.\<close>
lemma tsyndom_insert: "tsynValues\<cdot>s = {m | m. (TSynMsg m) \<in> sValues\<cdot>s}"
  by (metis (no_types) Abs_cfun_inverse2 tsynValues_def tsyndom_cont)

text \<open>@{term tsynValues} maps the empty stream on the empty set.\<close>
lemma tsyndom_strict [simp]: "tsynValues\<cdot>\<epsilon> = {}"
  by (simp add: tsyndom_insert)

lemma tsyndom_sconc_msg_sub: "tsynValues\<cdot>(\<up>(TSynMsg x) \<Zcat> xs) \<subseteq> S \<Longrightarrow> tsynValues\<cdot>xs \<subseteq> S"
  by (simp add: subset_eq tsyndom_insert)

lemma tsyndom_sconc_msg_sub2: "tsynValues\<cdot>xs \<subseteq> S \<Longrightarrow> x \<in> S \<Longrightarrow> tsynValues\<cdot>(\<up>(TSynMsg x) \<Zcat> xs) \<subseteq> S"
  by (simp add: subset_iff tsyndom_insert)

text \<open>@{term tsynValues} of concatenations distributes via union of sets.\<close>
lemma tsyndom_sconc_msg[simp]: "tsynValues\<cdot>(\<up>(TSynMsg a) \<Zcat> as) = {a} \<union> tsynValues\<cdot>as"
  by (simp add: tsyndom_insert set_eq_iff)

lemma tsyndom_sconc_Eps[simp]: "tsynValues\<cdot>(\<up>Eps \<Zcat> s) = tsynValues\<cdot>s"
  by (metis (no_types, lifting) Collect_cong Un_insert_left tsyn.distinct(1) insert_iff sValues2un 
      sup_bot.left_neutral tsyndom_insert)

text \<open>@{term tsynValues} of the concatenation of two streams is equal to the union of @{term tsynValues} 
        applied to both streams.\<close>
lemma tsyndom_sconc: assumes "#as < \<infinity>" shows "tsynValues\<cdot>(as \<Zcat> bs) = tsynValues\<cdot>as \<union> tsynValues\<cdot>bs"
  proof -
    have "sValues\<cdot>(as \<Zcat> bs) = sValues\<cdot>(as) \<union> sValues\<cdot>(bs)" 
      by (meson assms ninf2Fin lnat_well_h2 sValues_sconc2un)
    then have "{x. TSynMsg x \<in> sValues\<cdot>(as \<Zcat> bs)} = {x. TSynMsg x \<in> sValues\<cdot>as \<or> TSynMsg x \<in> sValues\<cdot>bs}"
      by simp
    then show ?thesis 
      by (metis (no_types, lifting) Collect_cong Collect_disj_eq tsyndom_insert)
  qed

text \<open>@{term tsynValues} is only a singleton set if the stream just contains one element.\<close>
lemma tsyndom_singleton_msg: "tsynValues\<cdot>(\<up>(TSynMsg a)) = {a}"
  by (metis insert_is_Un lscons_conv sup'_def tsyndom_sconc_msg tsyndom_strict)

text \<open>@{term tsynValues} is empty if stream is Eps.\<close>
lemma tsyndom_singleton_Eps: "tsynValues\<cdot>(\<up>Eps) = {}"
  using tsyndom_sconc_Eps tsyndom_strict by fastforce

text \<open>Cardinality of the set @{term tsynValues} is smaller or equal to the length of the original 
        stream.\<close>
lemma tsyndom_slen: assumes "#s = Fin k" shows "card (tsynValues\<cdot>s) \<le> k"
  proof -
    have inj_message: "inj (\<lambda>x. TSynMsg x)" 
      by (meson injI tsyn.inject)
    then have image_subset_sValues: "(\<lambda>x. TSynMsg x) ` {u. TSynMsg u \<in> sValues\<cdot>s} \<subseteq> sValues\<cdot>s" 
      by (simp add: image_Collect_subsetI)
    then have inj_on_mset: "inj_on (\<lambda>x. TSynMsg x) {u. TSynMsg u \<in> sValues\<cdot>s}" 
      using inj_message inj_on_def by blast
    then have sValues_is_image: "sValues\<cdot>s = (\<lambda>n. snth n s) ` {i :: nat. Fin i < #s}"
      by (metis (no_types) sValues_def2 setcompr_eq_image)
    then have "finite (sValues\<cdot>s)"
      using nat_seg_image_imp_finite assms by simp
    then have "card ({u. TSynMsg u \<in> sValues\<cdot>s}) \<le> card (sValues\<cdot>s)" 
      using inj_on_mset card_inj_on_le image_subset_sValues by blast 
    then have "card {u. TSynMsg u \<in> sValues\<cdot>s} \<le> k"
      using sValues_slen assms le_trans by blast
    then show ?thesis
      by (simp add: tsyndom_insert)
  qed

lemma tsyndom_subset: "tsynValues\<cdot>(stake n\<cdot>s) \<subseteq> tsynValues\<cdot>s"
  apply(induction s arbitrary: n rule:ind)
  apply auto[2]
  by (metis cont_pref_eq1I set_cpo_simps(1) stream.take_below)

lemma tsyn_ticks_only: assumes "#s = Fin n" and "tsynValues\<cdot>s = {}"
  shows "s = sntimes n (\<up>Eps)"
  using assms proof(induction s arbitrary: n rule: finind)
  case 1
  then show "#s = Fin n"
    by (simp add: assms(1))
next
  case 2
  then show ?case
    by simp 
next
  case (3 a s)
  hence "a = Eps"
    by (metis insert_is_Un insert_not_empty tsyn.exhaust tsyndom_sconc_msg)
  then show ?case
    apply(cases n)
    using "3.prems"(1) apply fastforce
    apply simp
    apply(rule cfun_arg_cong)
    apply(rule "3.IH")
    using "3.prems" by simp_all
qed
 
lemma tsyn_ticks_only_inf: assumes "#s = \<infinity>" and "tsynValues\<cdot>s = {}"
  shows "s = ((\<up>Eps)\<^sup>\<infinity>)"
proof - 
  have "\<And>n. tsynValues\<cdot>(stake n\<cdot>s) = {}"
    using assms(2) tsyndom_subset by fastforce
  hence "\<And>n. stake n\<cdot>s = stake n\<cdot>((\<up>Eps)\<^sup>\<infinity>)"
    by (metis assms(1) slen_stake_fst_inf sntimes_stake tsyn_ticks_only)
  thus ?thesis
    using stream.take_lemma by blast 
qed

text \<open>@{term tsynValues} inverses the msg, removes Eps.\<close>
lemma tsyndom_sValues: "tsynValues\<cdot>s = inverseMsg ` ((sValues\<cdot>s) - {Eps})"
  apply (simp add: tsyndom_insert image_def set_eq_iff)
  by (metis DiffE DiffI empty_iff insert_iff inverseMsg.simps(2) tsyn.exhaust tsyn.simps(3))

text \<open>@{term tsynValues} test on finite stream.\<close>
lemma tsyndom_test_finstream: "tsynValues\<cdot>(<[TSynMsg (1 :: nat), TSynMsg 2, Eps, Eps, TSynMsg 1, Eps]>) = {1, 2}"
  apply (simp add: tsyndom_insert set_eq_iff) 
  by blast

text \<open>@{term tsynValues} test on infinite stream.\<close>
lemma tsyndom_test_infstream: "tsynValues\<cdot>((<[TSynMsg (1 :: nat), TSynMsg 2, Eps, TSynMsg 3]>)\<^sup>\<infinity>) = {1, 2, 3}"
  apply (simp add:  tsyndom_insert set_eq_iff)
  by blast


text \<open>@{term tsyn2ustream} insertion lemma.\<close>
lemma tsynabs_insert: "s\<^sup>- = smap tsyn2ustreamElem\<cdot>(sfilter {e. e \<noteq> Eps}\<cdot>s)"
  by (simp add: tsyn2ustream_def)                            

text \<open>@{term tsyn2ustream} maps the empty stream on the empty stream.\<close>
lemma tsynabs_strict [simp]: "\<epsilon>\<^sup>- = \<epsilon>"
  by (simp add: tsynabs_insert)

text \<open>@{term tsyn2ustream} distributes over concatenation.\<close>
lemma tsynabs_sconc_msg[simp]: "(\<up>(TSynMsg a) \<Zcat> as)\<^sup>- = \<up>a \<Zcat> as\<^sup>-"
  by (simp add: tsynabs_insert)

text \<open>@{term tsyn2ustream} ignores empty time-slots.\<close>
lemma tsynabs_sconc_Eps[simp]: "(\<up>Eps \<Zcat> s)\<^sup>- = s\<^sup>-"
  by (simp add: tsynabs_insert)

text \<open>@{term tsyn2ustream} of the concatenation of two streams equals the concatenation of 
        @{term tsyn2ustream} of both streams.\<close>
lemma tsynabs_sconc: assumes "#as < \<infinity>" shows "(as \<Zcat> bs)\<^sup>- = as\<^sup>- \<Zcat> bs\<^sup>-"
  by (simp add: add_sfilter2 assms smap_split tsynabs_insert)

text \<open>@{term tsyn2ustream} of a singleton stream with a message is the singleton stream with the 
        message.\<close>
lemma tsynabs_singleton_msg[simp]: "(\<up>(TSynMsg a))\<^sup>- = \<up>a"
  by (simp add: tsynabs_insert)

text \<open>@{term tsyn2ustream} of a singleton stream with Eps is the empty stream.\<close>
lemma tsynabs_singleton_Eps[simp]: "(\<up>Eps)\<^sup>- = \<epsilon>"
  by (simp add: tsynabs_insert)

lemma tsynabs_below_lub: "chain Y \<Longrightarrow> #((Y i )\<^sup>-) \<le> #((\<Squnion>i. Y i)\<^sup>-)"
  using is_ub_thelub mono_slen monofun_cfun_arg by blast


text \<open>Length of @{term tsyn2ustream} is smaller or equal to the length of the original stream.\<close>
lemma tsynabs_slen: "#s\<^sup>- \<le> #s"
  by (simp add: tsynabs_insert)

lemma tsynabs_sValues_subset_eq: "(sValues\<cdot>s \<subseteq> insert Eps (TSynMsg ` range a)) = (sValues\<cdot>(s\<^sup>-) \<subseteq> range a)"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by (rule admI, simp add: contlub_cfun_arg lub_eq_Union UN_subset_iff)
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    then show ?case 
      by (simp only: tsynabs_sconc_msg sValues2un, auto)
  next
    case (Eps s)
    then show ?case 
      by (simp only: tsynabs_sconc_Eps sValues2un, auto)
  qed

text \<open>The set of messages of a stream equals the set of values of @{term tsyn2ustream} of the 
        stream.\<close>
lemma tsynabs_tsyndom: "tsynValues\<cdot>s = sValues\<cdot>(s\<^sup>-)"
  apply (induction s rule: tsyn_ind, simp_all)
  done

lemma tsyn_fin_msg: assumes "#s\<^sup>- < \<infinity>" and "#s = \<infinity>"
  shows "\<exists>n. sdrop n\<cdot>s = \<up>Eps\<^sup>\<infinity>"
proof - 
  obtain n where "s\<^sup>- = (stake n\<cdot>s)\<^sup>-"
    by (metis assms(1) fun_approxl2 len_stream_def lnat_well_h2)
  have "s\<^sup>- = (stake n\<cdot>s)\<^sup>- \<Zcat> (sdrop n\<cdot>s)\<^sup>-"
    by (metis Fin_neq_inf inf_less_eq not_le split_streaml1 tsynabs_sconc ub_slen_stake)
  hence "(sdrop n\<cdot>s)\<^sup>- = \<epsilon>"
    by (metis \<open>s\<^sup>- = (stake n\<cdot>s)\<^sup>-\<close> assms(1) lnat_well_h2 sconc_snd_empty sdropl6)
  hence "tsynValues\<cdot>(sdrop n\<cdot>s) = {}" using tsynabs_tsyndom by force
  moreover have "#(sdrop n\<cdot>s) = \<infinity>"
    using assms(2) fair_sdrop by blast
  ultimately have "sdrop n\<cdot>s = \<up>Eps\<^sup>\<infinity>"
    using tsyn_ticks_only_inf by blast
  thus ?thesis
    by blast 
qed

lemma tsynabs_sValues: "sValues\<cdot>(s\<^sup>-) = tsynValues\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)done

lemma tsynabs_fin_take: assumes "#(s\<^sup>-) < \<infinity>"
  shows "\<exists>n. (stake n\<cdot>s)\<^sup>- = s\<^sup>-"
  by (metis assms fun_approxl2 len_stream_def lnat_well_h2)

lemma tsynabs_fin_drop: assumes "#(s\<^sup>-) < \<infinity>"
  shows "\<exists>n. (sdrop n\<cdot>s)\<^sup>- = \<bottom>"
  by (metis (no_types, lifting) assms drop_not_all inf_less_eq leI notinfI3 sconc_neq_h sconc_snd_empty sdropostake split_streaml1 tsynabs_fin_take tsynabs_sconc)


text \<open>@{term tsyn2ustream} test on finite stream.\<close>
lemma tsynabs_test_finstream: "(<[TSynMsg 1, TSynMsg 2, Eps, Eps, TSynMsg 1, Eps]>)\<^sup>- = <[1, 2, 1]>"
  by (simp add: tsynabs_insert)

text \<open>@{term tsyn2ustream} test on infinite stream.\<close>
lemma tsynabs_test_infstream: "((<[TSynMsg 1, TSynMsg 2, Eps, TSynMsg 3]>)\<^sup>\<infinity>)\<^sup>- = (<[1, 2, 3]>)\<^sup>\<infinity>"
  by (simp add: tsynabs_insert)

text \<open>If a timed stream has a finite prefix of @{term Eps}, then applying @{term tsyn2ustream} gives
        us the same result  whether we drop the prefix before or not.\<close>
lemma tsynabs_remEps[simp]:
  assumes "sValues\<cdot>s= {Eps}"
  and "# s < \<infinity>"
  shows "(s\<Zcat>s2)\<^sup>- = s2\<^sup>-"
  using assms apply(induction s rule: tsyn_ind, simp_all add: assms)
  apply (rule admI)
  apply (metis inf_chainl4 l42 neq_iff)
  by (metis le_less_trans less_lnsuc sconc_fst_empty strict_sValues_rev subset_singleton_iff)

text \<open>If a timed stream has a finite prefix of @{term Eps}, followed by some message 
        @{term TSynMsg}, then the stream obtained by applying  @{term tsyn2ustream} to it begins with this
        message.\<close>
lemma tsynabs_remEps_msg:
  assumes "sValues\<cdot>s={Eps}"
  and "# s < \<infinity>"
  shows "(s \<Zcat> \<up>(TSynMsg a) \<Zcat> s2)\<^sup>- = \<up>a \<Zcat>(s2\<^sup>-)"
  using assms by simp

lemma tsynabs_ind [case_names adm bot msg]:
  assumes adm: "adm P"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P (s\<^sup>-) \<Longrightarrow> P ((\<up>(TSynMsg m) \<Zcat> s)\<^sup>-)"
  shows "P (x\<^sup>-)"
  apply (induction x rule: tsyn_ind)
  apply (simp add: adm adm_subst)
  apply (simp add: bot) 
  using msg by auto

lemma tsynabs_cases [case_names bot msg]:
  assumes bot: "x\<^sup>- = \<epsilon> \<Longrightarrow> P \<epsilon>"
    and msg: "\<And>m s. x\<^sup>- = \<up>m \<Zcat> s \<Longrightarrow> P (\<up>m \<Zcat> s)"
  shows "P (x\<^sup>-)"
  apply (rule_tac x = "x\<^sup>-" in scases)
  apply (simp add: bot)
  by (simp add: msg)

lemma tsynabs_stakewhile: "(stakewhile (\<lambda>x. x = Eps)\<cdot>s)\<^sup>- = \<epsilon>"
  apply (induction s rule: tsyn_ind)
  by simp_all

lemma tsynabs_sdropwhile_nEps:
  assumes "a\<^sup>- \<noteq> \<epsilon>"
  shows "sdropwhile (\<lambda>x. x = Eps)\<cdot>a \<noteq> \<epsilon>"
  by (metis assms sconc_snd_empty stakewhileDropwhile tsynabs_stakewhile)

lemma tsynabs_sdropwhile: "(sdropwhile (\<lambda>x. x = Eps)\<cdot>ts)\<^sup>- = ts\<^sup>-"
  apply (induction ts rule: tsyn_ind)
  by simp_all

lemma tsynabs_sdropwhile_srt:
  "(srt\<cdot>(sdropwhile (\<lambda>x. x = Eps)\<cdot>port_i))\<^sup>- = srt\<cdot>(port_i\<^sup>-)"
  apply (induction port_i rule: tsyn_ind)
  by simp_all

lemma sdropwhile2tsynabs_shd:
  assumes "sdropwhile (\<lambda>x. x = Eps)\<cdot>ts = \<up>(TSynMsg m) \<Zcat> s"
  shows "shd (ts\<^sup>-) = m"
  by (metis assms shd1 tsynabs_sdropwhile tsynabs_sconc_msg)

lemma sdropwhile_shd2tsynabs_shd:
  assumes "shd (sdropwhile (\<lambda>x. x = Eps)\<cdot>ts) = TSynMsg m"
    and "ts\<^sup>- \<noteq> \<epsilon>"
  shows "shd (ts\<^sup>-) = m"
  by (metis assms surj_scons tsynabs_sdropwhile_nEps sdropwhile2tsynabs_shd)

lemma tsyn2ustream_ne_eps: "#(tsyn2ustream\<cdot>s) \<noteq> #s \<Longrightarrow> Eps \<in> sValues\<cdot>s"
  apply(simp add: tsyn2ustream_def)
  by (metis (mono_tags, lifting) Collect_mono mem_Collect_eq not_Eps_eq sValues_def2 sfilter_sValuesl3)

lemma
  tsyn2ustream_eq_no_eps:
  assumes"#(tsyn2ustream\<cdot>s) = #s"
    and "#s \<noteq> \<infinity>"
  shows "(Eps \<notin> sValues\<cdot>s)"
  apply(insert assms)
  apply(induct s, simp_all add: tsyn2ustream_def)
   apply(simp add: adm_def)
   apply(auto)
  using inf_chainl4 l42 apply force
   apply (metis less_lnsuc lnle_and_gt_inf(1) order_antisym_conv slen_sfilterl1)
  by (metis (no_types, lifting) LNat.lnat.sel_rews(2) lnle_and_gt_inf(2) sfilter_in sfilter_nin slen_scons slen_sfilterl1)

lemma tsyn2ustream_no_eps_eq: "Eps \<notin> sValues\<cdot>s \<Longrightarrow> #(tsyn2ustream\<cdot>s) = #s"
  apply(simp add: tsyn2ustream_def)
  apply(insert sfilter_sValuesl3[of s])
  by (metis (mono_tags, lifting) Collect_mem_eq Collect_mono not_Eps_eq)

lemma tsyn2ustream_conc: "#a \<noteq> \<infinity> \<Longrightarrow> tsyn2ustream\<cdot>(a \<Zcat> s) = tsyn2ustream\<cdot>a \<Zcat> tsyn2ustream\<cdot>s"
  by (simp add: tsyn2ustream_def add_sfilter2 order_less_le smap_split)


text \<open>@{term tsynLen} insertion lemma.\<close>
lemma tsynlen_insert: "tsynLen\<cdot>s =  #(s\<^sup>-)"
  by (simp add: tsynLen_def len_stream_def)

text \<open>@{term tsynLen} maps the empty stream to zero.\<close>
lemma tsynlen_strict [simp]: "tsynLen\<cdot>\<epsilon> = 0"
  by (simp add: tsynlen_insert)


text \<open>@{term tsynLen} distributes over concatenation.\<close>
lemma tsynlen_sconc_msg: "tsynLen\<cdot>(\<up>(TSynMsg a) \<Zcat> as) = lnsuc\<cdot>(tsynLen\<cdot>as)"
  by (simp add:  tsynlen_insert)

text \<open>@{term tsynLen} distributes over concatenation.\<close>
lemma tsynlen_sconc_msg2:
  assumes "m \<noteq> Eps"
  shows "tsynLen\<cdot>(\<up>m \<Zcat> s) = lnsuc\<cdot>(tsynLen\<cdot>s)"
using tsynlen_sconc_msg assms tsyn2ustreamElem.cases by blast

text \<open>@{term tsynLen} ignores empty time slots.\<close>
lemma tsynlen_sconc_Eps: "tsynLen\<cdot>(\<up>(Eps) \<Zcat> as) = tsynLen\<cdot>as"
  by (simp add:  tsynlen_insert)

text \<open>@{term tsynLen} of the concatenation of two streams equals the sum of @{term tsynLen} of 
        both streams if the number of messages and the first stream are finite.\<close>
lemma tsynlen_sconc_finite:
  assumes "#as < \<infinity>" and "tsynLen\<cdot>as = Fin k" and "tsynLen\<cdot>bs = Fin n"
  shows "tsynLen\<cdot>(as \<Zcat> bs) = Fin (k + n)"
  using assms
  by (simp add: slen_sconc_all_finite tsynabs_sconc tsynlen_insert)

text \<open>@{term tsynLen} of the concatenation of two streams with finite many messages is less or 
        equal to the sum of @{term tsynLen} of both streams\<close>
lemma  tsynlen_sconc_infinite:
  assumes "tsynLen\<cdot>as = Fin n" and "tsynLen\<cdot>bs = Fin  m"
  shows "tsynLen\<cdot>(as \<Zcat> bs) \<le> Fin (n + m)"
  using assms leI sconc_fst_inf tsynlen_sconc_finite by fastforce

text \<open>@{term tsynLen} is less or equal to the length of the stream.\<close>
lemma tsynlen_slen: "tsynLen\<cdot>s \<le> #s"
  by (simp add: tsynabs_slen tsynlen_insert)

text \<open>@{term tsynLen} Non-empty singleton streams have length 1.\<close>
lemma tsynlen_singleton_msg: "tsynLen\<cdot>(\<up>(TSynMsg a)) = Fin 1"
  by (simp add: tsynlen_insert )

text \<open>@{term tsynLen} Empty slots have length zero.\<close>
lemma tsynlen_singleton_Eps: "tsynLen\<cdot>(\<up>Eps) = 0"
  by (simp add:  tsynlen_insert)

lemma tsynlen_sfoot_msg_geq:
  assumes "#s < \<infinity>"
    and "s \<noteq> \<epsilon>"
    and "sfoot s = (TSynMsg m)" 
  shows "Fin 1 \<le> tsynLen\<cdot>s"
  using assms
  apply (induction s arbitrary: m rule: tsyn_finind, simp_all)
  apply (metis Fin_02bot  gr_0 less2lnleD lnzero_def tsynlen_sconc_msg)
  by (metis Fin_02bot Fin_Suc Fin_neq_inf inf_ub less_le lnzero_def only_empty_has_length_0 
      sconc_snd_empty sfoot_conc sfoot_one slen_sconc_snd_inf slen_scons slen_zero 
      tsyn.distinct(1) tsynlen_sconc_Eps)

text \<open>If @{term tsynLen} is infinity the stream cannot be empty.\<close>
lemma tsynlen_inf_nbot: assumes "tsynLen\<cdot>s = \<infinity>"
  shows "s \<noteq> \<epsilon>"
  using assms by fastforce

text \<open>@{term tsynLen} of the infinte concatenation of a finite stream with more than one 
        message is @{term "\<infinity>"}.\<close>
lemma tsynlen_inftimes_finite:
  assumes "#as < \<infinity> " and "0 < tsynLen\<cdot>as" 
  shows "tsynLen\<cdot>(as\<^sup>\<infinity>) = \<infinity>"
  by (metis (no_types, lifting) assms(1) assms(2) neq_iff rek2sinftimes sinftimes_unfold 
      slen_empty_eq slen_sinftimes tsynabs_sconc tsynlen_insert)

lemma tsynlen_inftimes_finite_inf_tsynlen:
  assumes "tsynLen\<cdot>as = \<infinity>" 
  shows "tsynLen\<cdot>(as\<^sup>\<infinity>) = \<infinity>"
  by (metis assms inf_less_eq sinf_inf tsynlen_slen)


text \<open>@{term tsynLen} test for finite tsyn stream.\<close>
lemma tsynlen_test_finstream: 
  "tsynLen\<cdot>(<[TSynMsg 1, Eps, TSynMsg 2, Eps, Eps, TSynMsg 1]>) = Fin 3"
  by (simp add: tsynlen_insert)

text \<open>@{term tsynLen} test for infinite tsyn stream.\<close>
lemma tsynlen_test_infstream: "tsynLen\<cdot>(<[Eps, TSynMsg a]>\<^sup>\<infinity>) = \<infinity>"
  by (metis Fin_neq_inf gr_0 inf_ub less_le list2s_Suc list2streamFin lscons_conv 
      tsynlen_inftimes_finite tsynlen_sconc_msg tsynlen_sconc_Eps) 

lemma tsynabs_snths_eq [case_names len nth]:
  assumes len: "tsynLen\<cdot>x = tsynLen\<cdot>y"
      and nth: "\<And>n. Fin n < tsynLen\<cdot>x \<Longrightarrow> snth n (x\<^sup>-) =  snth n (y\<^sup>-)"
  shows "x\<^sup>- = y\<^sup>-"
  by (metis len nth snths_eq tsynlen_insert)

lemma tsynabs_snths_eq_ext [case_names len nth]:
  assumes len: "tsynLen\<cdot>x = #y"
      and nth: "\<And>n. Fin n < tsynLen\<cdot>x \<Longrightarrow> snth n (x\<^sup>-) =  snth n y"
  shows "x\<^sup>- = y"
  by (metis len nth snths_eq tsynlen_insert)

lemma tsynlen2sdropwhile_nEps:
  assumes "0 < tsynLen\<cdot>a"
  shows "sdropwhile (\<lambda>x. x = Eps)\<cdot>a \<noteq> \<epsilon>"
  by (metis assms gr_0 lnsuc_neq_0 slen_empty_eq tsynabs_sdropwhile_nEps tsynlen_insert)

lemma tsynlen2nEps:
  assumes "0 < tsynLen\<cdot>s"
  shows "s \<noteq> \<epsilon>"
  using assms by auto

lemma tsynlen2tsynabs_nEps: 
  assumes "0 < tsynLen\<cdot>s"
  shows "s\<^sup>- \<noteq> \<epsilon>"
  by (metis assms slen_zero tsynlen_insert tsynlen2nEps tsynlen_strict)

lemma tsynlen_inf2tsynabs_nEps:
  assumes "tsynLen\<cdot>s = \<infinity>"
  shows "s\<^sup>- \<noteq> \<epsilon>"
  by (metis Inf'_neq_0_rev assms slen_zero tsynlen_insert)

lemma eq_tsynlen_eq_and_less: "\<lbrakk>#\<^sub>-s = #\<^sub>-t; s\<^sup>- \<sqsubseteq>  t\<^sup>-\<rbrakk> 
                      \<Longrightarrow>  (s::'a tsyn stream)\<^sup>- =  t\<^sup>-"
  apply (simp add: tsynlen_insert)
  apply (rule stream.take_lemma)
  by (rule stake_eq_slen_eq_and_less [rule_format], rule conjI)

lemma tsynlen_not_inf_eq_inf:" \<not> #\<^sub>-s < \<infinity> \<Longrightarrow> #\<^sub>-s = \<infinity>"
  using inf_great linorder_less_linear by blast

lemma tsynlen_inf_lub: "chain Y \<Longrightarrow> #\<^sub>- (Y i) = \<infinity> \<Longrightarrow> #\<^sub>-(\<Squnion>i. Y i) = \<infinity>"
  by (metis below_antisym  inf_ub is_ub_thelub lnle_def monofun_cfun_arg)

text \<open>Prepending a message increases increases @{term tsynLen} by exactly one.\<close>
lemma tsynlen_sconc_tsynmsg:
  "tsynLen\<cdot>(\<up>(TSynMsg v) \<Zcat> s) = tsynLen\<cdot>s + 1"
proof -
  have "tsynLen\<cdot>(\<up>(TSynMsg v) \<Zcat> s)
        = # ((\<up>(TSynMsg v) \<Zcat> s)\<^sup>-)"
    apply (simp add: tsynLen_def) 
    by (metis tsynLen_def tsynlen_insert tsynlen_sconc_msg)
  also have "\<dots> = # (s\<^sup>-) + 1"
    by (simp add: lnat_plus_commu one_lnat_def sconc_slen2)
  also have "\<dots> = tsynLen\<cdot>s + 1"
    apply (simp add: tsynLen_def) 
    by (metis tsynLen_def tsynlen_insert)
  finally show ?thesis .
qed

lemma tsynlen_sscanlaone_stateleq:
  fixes s:: "'a :: countable stream"
  assumes a1: "\<And>state m. snd (t state m) = snd (t init m) \<or> snd (t state m) \<in> S0"
    and a2: "\<And>state m. fst (t init m) \<noteq> init \<Longrightarrow> fst (t state m) = fst (t init m)"
    and S0_zero: "\<And>x. x \<in> S0 \<Longrightarrow> tsynLen\<cdot>(sup' x) = 0"
  shows "tsynLen\<cdot>(sscanlAOne t state\<cdot>s) \<le> tsynLen\<cdot>(sscanlAOne t init\<cdot>s)"
proof (induction s arbitrary: state)
  case adm
  show ?case
  proof (rule admI)
    fix Y :: "nat \<Rightarrow> ('a:: countable) stream"
    assume chY: "chain Y"
    assume IH: "\<And>i. tsynLen\<cdot>(sscanlAOne t state\<cdot>(Y i))
                  \<le> tsynLen\<cdot>(sscanlAOne t init\<cdot>(Y i))"

    let ?F = "\<lambda>x. tsynLen\<cdot>(sscanlAOne t state\<cdot>x)"
    let ?G = "\<lambda>x. tsynLen\<cdot>(sscanlAOne t init\<cdot>x)"

    have cF: "cont ?F" by (intro cont2cont)
    have cG: "cont ?G" by (intro cont2cont)

    have F_lub: "?F (\<Squnion>i. Y i) = (\<Squnion>i. ?F (Y i))"
      using cF chY by (rule cont2contlubE)
    have G_lub: "?G (\<Squnion>i. Y i) = (\<Squnion>i. ?G (Y i))"
      using cG chY by (rule cont2contlubE)

    have lub_le: "(\<Squnion>i. ?F (Y i)) \<le> (\<Squnion>i. ?G (Y i))"
      using IH 
      apply (intro lub_mono2)
      using cF ch2ch_cont chY apply blast
       apply (simp add: chY)
      by simp
    have " \<And>Y. chain Y \<Longrightarrow>
         \<forall>i x. #\<^sub>-(sscanlAOne t x\<cdot>(Y i)) \<le> #\<^sub>-(sscanlAOne t init\<cdot>(Y i)) \<Longrightarrow>
         \<forall>x. #\<^sub>-(sscanlAOne t x\<cdot>(\<Squnion>i. Y i)) \<le> #\<^sub>-(sscanlAOne t init\<cdot>(\<Squnion>i. Y i))"
      unfolding F_lub G_lub using lub_le 
      by (simp add: contlub_cfun_arg lub_mono2)
  next
    show " \<And>Y. chain Y \<Longrightarrow>
         \<forall>i x. #\<^sub>-(sscanlAOne t x\<cdot>(Y i)) \<le> #\<^sub>-(sscanlAOne t init\<cdot>(Y i)) \<Longrightarrow>
         \<forall>x. #\<^sub>-(sscanlAOne t x\<cdot>(\<Squnion>i. Y i)) \<le> #\<^sub>-(sscanlAOne t init\<cdot>(\<Squnion>i. Y i))"
      by (simp add: contlub_cfun_arg lub_mono2)
  qed
  
next
  case bottom
  then show ?case
    by (simp add: tsynLen_def sscanlAOne_def)

next
  case (step a s state)
  obtain st1 out1 where T1: "t state a = (st1,out1)"
    by (cases "t state a") auto
  obtain st2 out2 where T2: "t init a = (st2,out2)"
    by (cases "t init a") auto

  have L: "sscanlAOne t state\<cdot>(\<up>a \<Zcat> s) = sup' out1 \<Zcat>\<Zcat> sscanlAOne t st1\<cdot>s"
    by (simp add: sscanlaone_step T1)
  have R: "sscanlAOne t init\<cdot>(\<up>a \<Zcat> s) = sup' out2 \<Zcat>\<Zcat> sscanlAOne t st2\<cdot>s"
    by (simp add: sscanlaone_step T2)

  have out_rel: "out1 = out2 \<or> out1 \<in> S0"
    using a1[of state a] by (simp add: T1 T2)

  have tail_le:
    "tsynLen\<cdot>(sscanlAOne t st1\<cdot>s) \<le> tsynLen\<cdot>(sscanlAOne t st2\<cdot>s)"
  proof (cases "st2 = init")
    case True
    have "tsynLen\<cdot>(sscanlAOne t st1\<cdot>s) \<le> tsynLen\<cdot>(sscanlAOne t init\<cdot>s)"
      using step.IH[of st1] by simp
    then show ?thesis using True by simp
  next
    case False
    have st_eq: "st1 = st2"
      by (metis False T1 T2 a2 split_pairs)
    then show ?thesis by simp
  qed

  show ?case
  proof (cases "out1 = out2")
    case True
    show ?thesis
      by (metis (no_types, opaque_lifting) L R T1 T2 True a2 conc_stream_def fst_conv lnsuc_lnle_emb local.step
        order_refl tsynlen_sconc_Eps tsynlen_sconc_msg2)
  next
    case False
    from out_rel False have out1S: "out1 \<in> S0" by blast
    have head0: "tsynLen\<cdot>(sup' out1) = 0"
      using S0_zero out1S by simp
    show ?thesis
      unfolding L R
    proof (cases out1)
      case Eps
      have "tsynLen\<cdot>(sup' out1 \<Zcat>\<Zcat> sscanlAOne t st1\<cdot>s) = tsynLen\<cdot>(sscanlAOne t st1\<cdot>s)"
        using Eps by (simp add: tsynlen_sconc_Eps)
      also have "... \<le> tsynLen\<cdot>(sscanlAOne t st2\<cdot>s)"
        using tail_le .
      also have "... \<le> tsynLen\<cdot>(sup' out2 \<Zcat>\<Zcat> sscanlAOne t st2\<cdot>s)"
        apply (cases out2; simp add: tsynlen_sconc_Eps tsynlen_sconc_tsynmsg)
        by (simp add: lnat_plus_suc)
      finally show "#\<^sub>-(\<up>out1\<Zcat>\<Zcat>sscanlAOne t st1\<cdot>s) \<le> #\<^sub>-(\<up>out2\<Zcat>\<Zcat>sscanlAOne t st2\<cdot>s)" by simp
    next
      case (Msg x)
      have False
        using head0 Msg by (simp add: tsynlen_singleton_msg)
      then show " #\<^sub>-(\<up>out1\<Zcat>\<Zcat>sscanlAOne t st1\<cdot>s) \<le> #\<^sub>-(\<up>out2\<Zcat>\<Zcat>sscanlAOne t st2\<cdot>s)" by simp
    qed
  qed
qed

lemma tsyn2ustream_len: "#(tsyn2ustream\<cdot>s) = #(tsyn2ustream\<cdot>(smap (map_tsyn f)\<cdot>s))"
  by (simp add: tsyn2ustream_def sfilter_smap_len)

lemma tsynLen_smap_map_tsyn: " #\<^sub>-s = #\<^sub>-(smap (map_tsyn f)\<cdot>s)"
  apply(simp add: tsynLen_def)
  apply(subst beta_cfun, simp add: len_stream_def)+
  by(simp add: tsyn2ustream_len)


lemma szip_sfilter_infty_len:
  assumes "#(M \<ominus> ora) = \<infinity>"
    and "#s = \<infinity>"
  shows "#(szip\<cdot>ora\<cdot>s) = \<infinity>"
  apply(insert assms, simp)
  using sfilterl4 by blast

lemma tsynlen_inf_srt_ne: "#\<^sub>-s = \<infinity> \<Longrightarrow> srt\<cdot>s \<noteq> \<epsilon>"
  apply(simp add: sdrop_def tsynlen_insert tsyn2ustream_def)
  by (metis sfilter_srt_sinf slen_zero strict_sfilter tsynlen_inf_nbot tsynlen_strict)

lemma tsynlen_inf_drop_ne: "#\<^sub>-s = \<infinity> \<Longrightarrow> sdrop i\<cdot>s \<noteq> \<epsilon>"
  apply(induction i, simp_all add: tsynlen_inf_nbot)
  apply(simp add: sdrop_def)
  by (metis Inf'_neq_0 fair_sdrop inf_less_eq sdrop_back_rt sdrop_def slen_zero tsynlen_slen)

lemma tsynLen_TSynMsg_sfilter: "#\<^sub>-((TSynMsg ` A) \<ominus> s) = #((TSynMsg ` A) \<ominus> s)"
  apply(simp add: tsynlen_insert tsyn2ustream_def)
  apply(subgoal_tac "{e::'a tsyn. \<exists>y::'a. e = TSynMsg y} \<inter> TSynMsg ` A = TSynMsg ` A")
   apply(simp)
  by(blast)

lemma tsynLen_tsynFilter1: "#\<^sub>-(A \<ominus>\<^sub>- s) =  #((TSynMsg ` A) \<ominus> s)"
  apply(simp add: tsynlen_insert tsyn2ustream_def tsynFilter_def)
  apply(rule sfilter_smap_len[symmetric])
  apply(auto)
  apply(case_tac "a = Eps", simp_all)
  by (metis TSynDatatype.tsyn.simps(3) TsynStream.tsynFilterElem.simps(2) rev_image_eqI)

lemma tsynLen_tsynFilter2: "#\<^sub>-(A \<ominus>\<^sub>- s) =  #\<^sub>-((TSynMsg ` A) \<ominus> s)"
  by(simp add: tsynLen_TSynMsg_sfilter tsynLen_tsynFilter1)

lemma tsynlen_stake_mono: "i \<le> j \<Longrightarrow> #\<^sub>-(stake i\<cdot>s) \<le> #\<^sub>-(stake j\<cdot>s)"
  by (meson cont_pref_eq1I lnle_def stake_mono)



lemma tsyn_cases_inf [case_names inf msg Eps]:
  assumes inf: "tsynLen\<cdot>s = \<infinity>"
    and msg: "\<And>a as. s= (\<up>(TSynMsg a) \<Zcat> as) \<Longrightarrow> P s"
    and Eps: "\<And>as. s=(\<up>Eps \<Zcat> as) \<Longrightarrow> P s"
  shows "P s"
  using assms
  apply (cases rule: scases [of s], simp_all)
  by (metis tsyn2ustreamElem.cases)



lemma tsynEps_insert: "tsynEps\<cdot>ts = #(sfilter {Eps}\<cdot>ts)"
  by (simp add: tsynEps_def len_stream_def)
 
lemma tsynEps_strict [simp]:"tsynEps\<cdot>\<epsilon> = 0"
  by (simp add: tsynEps_insert)

lemma tsynEps_sconc_msg:"tsynEps\<cdot>(\<up>(TSynMsg m) \<Zcat> ts) = tsynEps\<cdot>ts"
  by (simp add: tsynEps_insert)

lemma tsynEps_sconc_Eps:"tsynEps\<cdot>(\<up>Eps \<Zcat> ts) = lnsuc\<cdot>(tsynEps\<cdot>ts)"
  by(simp add: tsynEps_insert)

text \<open>@{term tsynEps} of the concatenation of two streams equals the sum of @{term tsynEps} of 
        both streams if the number of Epss and the first stream are finite.\<close>
lemma tsynEps_sconc_finite:
  assumes "#as < \<infinity>"
  and "tsynEps\<cdot>as = Fin k"
  and "tsynEps\<cdot>bs = Fin n"
  shows "tsynEps\<cdot>(as \<Zcat> bs) = Fin (k + n)"
  using assms
  by (simp add: slen_sconc_all_finite tsynEps_insert add_sfilter2 sconc_slen2)

text \<open>@{term tsynEps} of the concatenation of two streams with finite many Epss is less or 
        equal to the sum of @{term tsynEps} of both streams\<close>
lemma  tsynEps_sconc_infinite:
  assumes "tsynEps\<cdot>as = Fin n"
  and "tsynEps\<cdot>bs = Fin m"
  shows "tsynEps\<cdot>(as \<Zcat> bs) \<le> Fin (n + m)"
  using assms leI sconc_fst_inf tsynEps_sconc_finite by fastforce

text \<open>@{term tsynEps} is less or equal to the length of the stream.\<close>
lemma tsynEps_slen: "tsynEps\<cdot>s \<le> #s"
  by (simp add: tsynEps_insert)

text \<open>@{term tsynEps} Non-empty singleton streams have length 0.\<close>
lemma tsynEps_singleton_msg: "tsynEps\<cdot>(\<up>(TSynMsg a)) = Fin 0"
  by (simp add: tsynEps_insert)

text \<open>@{term tsynEps} Empty slots have length 1.\<close>
lemma tsynEps_singleton_Eps: "tsynEps\<cdot>(\<up>Eps) = Fin 1"
  by (simp add: tsynEps_insert)

lemma tsynEps_sfoot_msg_geq:
  assumes "#s < \<infinity>"
    and "s \<noteq> \<epsilon>"
    and "sfoot s = Eps"
  shows "Fin 1 \<le> tsynEps\<cdot>s"
  using assms
  apply (induction s rule: tsyn_finind, simp_all)
  apply (metis fold_inf inf_ub leD neq_iff sconc_fst_inf sconc_snd_empty sfoot_conc sfoot_one tsyn.distinct(1) tsynEps_sconc_msg)
  by (simp add: One_nat_def tsynEps_sconc_Eps)

text \<open>If @{term tsynEps} is infinity the stream cannot be empty.\<close>
lemma tsynEps_inf_nbot: assumes "tsynEps\<cdot>s = \<infinity>"
  shows "s \<noteq> \<epsilon>"
  using assms by fastforce

text \<open>@{term tsynEps} of the infinte concatenation of a finite stream with more than one 
        message is @{term "\<infinity>"}.\<close>
lemma tsynEps_inftimes_finite:
  assumes "#as < \<infinity> "
  and "0 < tsynEps\<cdot>as" 
shows "tsynEps\<cdot>as\<^sup>\<infinity> = \<infinity>"
  using assms
  by (metis neq_iff sfilter_sinf slen_sinftimes slen_zero tsynEps_insert)

text \<open>@{term tsynEps} test for finite tsyn stream.\<close>
lemma tsynEps_test_finstream: 
  "tsynEps\<cdot>(<[TSynMsg 1, Eps, TSynMsg 2, Eps, Eps, TSynMsg 1]>) = Fin 3"
  by (simp add: tsynEps_insert)

text \<open>@{term tsynEps} test for infinite tsyn stream.\<close>
lemma tsynEps_test_infstream: "tsynEps\<cdot>(<[Eps, TSynMsg a]>\<^sup>\<infinity>) = \<infinity>"
  by (metis Fin_neq_inf gr_0 inf_ub less_le list2s_Suc list2streamFin lscons_conv 
      tsynEps_inftimes_finite tsynEps_sconc_Eps) 

lemma no_msg_before_least: 
  assumes "k = (LEAST k. snth k z \<noteq> Eps)"
  shows "\<forall>i < k. snth i z = Eps"
  using assms not_less_Least by blast

  subsection \<open>Relationship between @{term tsynEps}, @{term tsynLen}  @{term slen}\<close>

text \<open>The @{term slen} of stream is the sum of its finite  @{term tsynLen} and finite
        @{term tsynEps}. There is also a stronger variant of this lemma, that generalizes
        to the infinite cases: @{term tsynlen_tsynEps2slen}\<close>
lemma tsynEps_tsynEps2slen_finite:
  assumes "#as < \<infinity>"
  and "tsynEps\<cdot>as = k"
  and "tsynLen\<cdot>as = n"
  shows "#as = k + n"
  using assms
  apply (induction as arbitrary: n k  rule: tsyn_ind, simp_all)
  apply (simp_all add: tsynEps_sconc_msg tsynlen_sconc_Eps)
   apply (metis add.assoc inf_ub less_le lnat_plus_suc sconc_fst_inf slen_lnsuc tsynlen_sconc_msg)
  by (metis (no_types, opaque_lifting) add.assoc le_less_trans less_lnsuc lnat_plus_lnsuc lnat_plus_suc tsynEps_sconc_Eps)

text \<open>If a stream has infinite @{term tsynLen} then it has infnite @{term slen}\<close>
lemma  tsynEps_tsynEps2slen_infinite_msg:
  assumes "tsynLen\<cdot>as = \<infinity>"
  shows "#as = \<infinity>"
  using assms
  by (metis inf_less_eq tsynlen_slen) 

text \<open>If a stream has infinite @{term tsynEps} then it has infnite @{term slen}\<close>
lemma  tsynEps_tsynEps2slen_infinite_Eps:
  assumes "tsynEps\<cdot>as = \<infinity>"
  shows "#as = \<infinity>"
  using assms
  by (metis inf_less_eq tsynEps_slen)  

text \<open>The @{term slen} of stream is the sum of its @{term tsynLen} and @{term tsynEps}.
        Same as @{term tsynlen_tsynEps2slen}, but more verbose.\<close>
lemma  tsynEps_tsynEps2slen_verbose:
  assumes "tsynEps\<cdot>as = n"
  and "tsynLen\<cdot>as = m"
  shows "#as = n + m"
  using assms apply(case_tac "n = \<infinity>")
  apply (simp add: tsynEps_tsynEps2slen_infinite_Eps)
  using assms apply(case_tac "m = \<infinity>")
  apply (simp add: tsynEps_tsynEps2slen_infinite_msg)
  apply (subst tsynEps_tsynEps2slen_finite, simp_all)
  apply (simp add: tsynEps_insert tsynlen_insert tsynabs_insert)
  by (metis Fin_02bot Fin_Suc One_nat_def assms(2) inf_ub less_le ln_less lnle_Fin_0 not_less notinfI3 sfilter_sinftimes_in slen_sfilter_sdrop_ile slen_sinftimes strict_sfilter slen_zero tsyn_fin_msg tsynEps_insert tsynEps_singleton_Eps tsynlen_insert)

text \<open>The @{term slen} of stream is the sum of its @{term tsynLen} and @{term tsynEps}.
        Same as @{term tsynEps_tsynEps2slen_verbose}, but less verbose.\<close>
lemma tsynlen_tsynEps2slen:"#\<^sub>-(ts) + (tsynEps\<cdot>ts) = #ts"
  by (simp add: tsynEps_tsynEps2slen_verbose lnat_plus_commu)

text \<open>If two streams have the same @{term slen} and same finite @{term tsynEps}, then they
        also have the same @{term tsynLen}\<close>
lemma tsynlen_eq_tsynLen_verbose:
  assumes "m < \<infinity>"
    and "#s1 = n"
    and "#s2 = n"
    and "tsynEps\<cdot>s1 = m"
    and "tsynEps\<cdot>s2 = m"
  shows"#\<^sub>-s1 = #\<^sub>-s2"
proof -
  have n1: "n = m + #\<^sub>-s1" using assms by (simp add: tsynEps_tsynEps2slen_verbose)
  have n2: "n = m + #\<^sub>-s2" using assms by (simp add: tsynEps_tsynEps2slen_verbose)
  show "#\<^sub>-s1 = #\<^sub>-s2" using assms(1) n1 n2 plus_unique_r
    by blast
qed

text \<open>If two streams have the same @{term slen} and same finite @{term tsynLen}, then they
        also have the same @{term tsynEps}\<close>
lemma tsynlen_eq_tsynEps_verbose:
  assumes "m < \<infinity>"
    and "#s1 = n"
    and "#s2 = n"
    and "tsynLen\<cdot>s1 = m"
    and "tsynLen\<cdot>s2 = m"
  shows "tsynEps\<cdot>s1 = tsynEps\<cdot>s2"
proof -
  have n1: "n = m + tsynEps\<cdot>s1" using assms by (simp add: tsynEps_tsynEps2slen_verbose lnat_plus_commu)
  have n2: "n = m + tsynEps\<cdot>s2" using assms by (simp add: tsynEps_tsynEps2slen_verbose lnat_plus_commu)
  show "tsynEps\<cdot>s1 = tsynEps\<cdot>s2" using assms(1) n1 n2 plus_unique_r
    by blast
qed

text \<open>Same as @{term tsynlen_eq_tsynLen_verbose}, but less verbose.\<close>
lemma tsynlen_eq_tsynLen:
  assumes "#s1 = #s2"
    and "tsynEps\<cdot>s1 < \<infinity>"
    and "tsynEps\<cdot>s1 = tsynEps\<cdot>s2"
  shows"#\<^sub>-s1 = #\<^sub>-s2"
  using assms tsynlen_eq_tsynLen_verbose by auto

text \<open>Same as @{term tsynlen_eq_tsynEps_verbose}, but less verbose.\<close>
lemma tsynlen_eq_tsynEps:
  assumes "#s1 = #s2"
    and "tsynLen\<cdot>s1 < \<infinity>"
    and "tsynLen\<cdot>s1 = tsynLen\<cdot>s2"
  shows "tsynEps\<cdot>s1 = tsynEps\<cdot>s2"
  using assms tsynlen_eq_tsynEps_verbose by auto

lemma tsynLen_eps_inf: "#\<^sub>-s = \<infinity> \<Longrightarrow> #({e . e \<noteq> Eps} \<ominus> s) = \<infinity>"
  by (metis (no_types, lifting) ext Collect_mono Int_def mem_Collect_eq sValues_sfilter sfilter_sValuesl3 tsynEps_tsynEps2slen_infinite_msg tsynabs_insert
      tsynlen_insert)

text \<open>If a function preserves the @{term slen} and @{term tsynEps} of a stream and a stream
        has only finite many Eps, then the function preserves @{term tsynLen}\<close>
lemma tsynlen_f_preserves_tsynLen:
  fixes "s"
  assumes "tsynEps\<cdot>s < \<infinity>"
  and "#(f s) = #s"
  and "tsynEps\<cdot>(f s) = tsynEps\<cdot>s"
  shows "#\<^sub>-(f s) = #\<^sub>-s"
  using assms by (subst tsynlen_eq_tsynLen, simp_all)

text \<open>If a function preserves the @{term slen} and @{term tsynLen} of a stream and a stream
        has only finite many msgs, then the function preserves @{term tsynEps}\<close>
lemma tsynlen_f_preserves_tsynEps:
  fixes "s"
  assumes "tsynLen\<cdot>s < \<infinity>"
  and "#(f s) = #s"
  and "tsynLen\<cdot>(f s) = tsynLen\<cdot>s"
  shows "tsynEps\<cdot>(f s) = tsynEps\<cdot>s"
  using assms by (subst tsynlen_eq_tsynEps, simp_all)


text \<open>@{term tsynFilter} insertion lemma.\<close>
lemma tsynfilter_insert: "(tsynFilter A)\<cdot>s =  smap (tsynFilterElem A)\<cdot>s"
  by (simp add: tsynFilter_def)

text \<open>@{term tsynFilter} maps the empty stream on the empty stream.\<close>
lemma tsynfilter_strict [simp]: "(tsynFilter A)\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynfilter_insert)

text \<open>@{term tsynFilter} distributes over concatenation, having the first Stream consist of 
        one Msg-element included in the given set.\<close>
lemma tsynfilter_sconc_msg_in: assumes "m \<in> A"
   shows "(tsynFilter A)\<cdot>(\<up>(TSynMsg m) \<Zcat> as) = \<up>(TSynMsg m) \<Zcat> (tsynFilter A)\<cdot>as"
  by (simp add: assms tsynfilter_insert)

text \<open>@{term tsynFilter} distributes over concatenation, having the first Stream consist of one 
        Msg-element not included in the given set.\<close>
lemma tsynfilter_sconc_msg_nin: assumes "m \<notin> A" 
  shows"(tsynFilter A)\<cdot>(\<up>(TSynMsg m) \<Zcat> as) = \<up>(Eps) \<Zcat> (tsynFilter A)\<cdot>as"
  by (simp add: assms tsynfilter_insert)

text \<open>@{term tsynFilter} distributes over concatenation, having the first Stream consist of one 
        Eps-element.\<close>
lemma tsynfilter_sconc_Eps: "(tsynFilter A)\<cdot>(\<up>(Eps)\<Zcat> as) = \<up>(Eps) \<Zcat> (tsynFilter A)\<cdot>as"
  by (simp add: tsynfilter_insert)

text \<open>@{term tsynFilter} of the concatenation of two streams equals the concatenation of 
        @{term tsynFilter} of both streams.\<close>
lemma tsynfilter_sconc: "(tsynFilter A)\<cdot>(a1 \<Zcat> a2) = (tsynFilter A)\<cdot>a1 \<Zcat> (tsynFilter A)\<cdot>a2"
  by (simp add: smap_split tsynfilter_insert)

text \<open>@{term tsynFilter} If singleton element is in the filter condition, just do nothing.\<close>
lemma tsynfilter_singleton_msg_in: assumes "a \<in> A"
  shows "(tsynFilter A)\<cdot>(\<up>(TSynMsg a)) = (\<up>(TSynMsg a))"
  by (metis assms lscons_conv sup'_def tsynfilter_sconc_msg_in tsynfilter_strict)

text \<open>@{term tsynFilter} If singleton element is not in the filter condition,
      return empty stream.\<close>
lemma tsynfilter_singleton_msg_nin:assumes "a \<notin> A"
  shows "(tsynFilter A)\<cdot>(\<up>(TSynMsg a)) = (\<up>Eps)"
  by (simp add: assms tsynFilter_def)

text \<open>@{term tsynFilter} ignores empty time slots.\<close>
lemma tsynfilter_singleton_Eps: "(tsynFilter A)\<cdot>(\<up>Eps) = \<up>Eps"
  by (simp add: tsynFilter_def)

text \<open>Length of @{term tsynFilter} is equal to the length of the original stream.\<close>
lemma tsynfilter_slen: "#((tsynFilter A)\<cdot>s) = #s"
  by (simp add: tsynfilter_insert)

text \<open>Abstraction of @{term tsynFilter} equals sfilter executed on abstracted stream.\<close>
lemma tsynfilter_tsynabs: "(tsynFilter A\<cdot>s)\<^sup>- = sfilter A\<cdot>(s\<^sup>-)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (rename_tac x y)
  apply (case_tac "x \<in> A")
  apply (simp add: tsynfilter_sconc_msg_in )
  apply (simp add: tsynfilter_sconc_msg_nin  )
  by (simp add: tsynfilter_sconc_Eps )

text \<open>@{term tsynFilter} leaves the length of the stream unchanged.\<close>
lemma tsynfilter_tsynlen: "tsynLen\<cdot>(tsynFilter A\<cdot>s) \<le> tsynLen\<cdot>s"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by (simp add: tsynfilter_tsynabs tsynlen_insert)  
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    then show ?case 
      apply (simp add: tsynfilter_tsynabs tsynlen_insert)
      by (metis slen_sfilterl1 slen_scons)
  next
    case (Eps s)
    then show ?case 
      by (simp add: tsynfilter_tsynabs tsynlen_insert)
  qed

text \<open>@{term sValues} of @{term tsynFilter} A is subset of @{term image} of 
        @{term tsynFilterElem} of A.\<close>
lemma tsynfilter_sValues: "sValues\<cdot>(tsynFilter A\<cdot>s) \<subseteq> tsynFilterElem A ` sValues\<cdot>s"
  apply (induction s arbitrary: A rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sValues tsynfilter_insert)+

text \<open>@{term tsynValues} of @{term tsynFilter} is subset of @{term tsynValues} of 
        the original stream.\<close>
lemma tsynfilter_tsyndom: "tsynValues\<cdot>(tsynFilter A\<cdot>s) \<subseteq> tsynValues\<cdot>s"
  by (simp add: tsynabs_tsyndom tsynfilter_tsynabs)

text \<open>@{term tsynFilter} test on finite nat tsyn-stream.\<close>
lemma tsynfilter_test_finstream: 
  "(tsynFilter {(1::nat),2})\<cdot>(<[TSynMsg 1, TSynMsg 2, Eps, TSynMsg 3, Eps, TSynMsg 1, Eps, TSynMsg 4]>) 
     = <[TSynMsg 1, TSynMsg 2, Eps, Eps, Eps, TSynMsg 1, Eps, Eps]>"
  by (simp add: tsynfilter_insert)

text \<open>@{term tsynFilter} test on infinitely many time-slots.\<close>
lemma tsynfilter_test_infstream: assumes "c \<noteq> a \<and> c \<noteq> b"
  shows "(tsynFilter {a,b})\<cdot>((<[TSynMsg a, TSynMsg c, Eps, TSynMsg b]>)\<^sup>\<infinity>) = (<[TSynMsg a, Eps, Eps, TSynMsg b]>)\<^sup>\<infinity>"
  by (simp add: assms tsynfilter_insert)

lemma tsynfilter_empty: " #\<^sub>-({} \<ominus>\<^sub>- s) = 0"
  by (simp add: tsynlen_insert tsynfilter_tsynabs)

lemma tsynfilter_empty2: " tsynValues\<cdot>({} \<ominus>\<^sub>- s) = {}"
  by (simp add: tsynabs_tsyndom tsynfilter_tsynabs)


lemma tsynApplyElem_inv_id[simp]: "inv TSynMsg tsyn \<in> range (F) \<Longrightarrow> tsynApplyElem (F \<circ> (inv F)) tsyn = tsyn"
  apply (induction tsyn)
  apply simp_all
  by (metis  f_inv_into_f )

lemma tsymApply_applyF_in[simp]:"tsynApplyElem F1 (tsynApplyElem F2 tsyn) = tsynApplyElem (F1 \<circ> F2) tsyn"
   proof (induction tsyn)
  case Eps
  show ?case by simp
next
  case (Msg a)
  show ?case by simp
qed

lemma tsynApplyElem_def2: "tsynApplyElem = map_tsyn"
  apply (subgoal_tac "\<And> f c. tsynApplyElem f c = map_tsyn f c")
  apply auto
  by(case_tac c, simp_all)

lemma tsynFst_def2: "tsynFst = map_tsyn fst"
  by(rule ext, case_tac x, auto)

lemma tsynSnd_def2: "tsynSnd = map_tsyn snd"
  by(rule ext, case_tac x, auto)



text \<open>@{term tsynMap} insertion lemma.\<close>
lemma tsynmap_insert: "tsynMap f\<cdot>s = smap (tsynApplyElem f)\<cdot>s"
  by (simp add: tsynMap_def)

text \<open>@{term tsynMap} is strict.\<close>
lemma tsynmap_strict [simp]: "tsynMap f\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} distributes over concatenation.\<close>
lemma tsynmap_sconc_msg: "tsynMap f\<cdot>(\<up>(TSynMsg m) \<Zcat> s) = \<up>(TSynMsg (f m)) \<Zcat> tsynMap f\<cdot>s"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} ignores empty time-slots.\<close>
lemma tsynmap_sconc_Eps: "tsynMap f\<cdot>(\<up>Eps \<Zcat> s) = \<up>Eps \<Zcat> tsynMap f\<cdot>s"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} of the concatenation of two streams equals the concatenation of 
        @{term tsynMap} of both streams.\<close>
lemma tsynmap_sconc: "tsynMap f\<cdot>(a1 \<Zcat> a2) = tsynMap f\<cdot>a1 \<Zcat> tsynMap f\<cdot>a2"
  by (simp add: smap_split tsynmap_insert)

text \<open>@{term tsynMap} of a stream containing only one element, is just the stream 
          with the function applied to that element.\<close>
lemma tsynmap_singleton_msg: "tsynMap f\<cdot>(\<up>(TSynMsg a)) = (\<up>(TSynMsg (f a)))"
  by (simp add: tsynMap_def)

text \<open>@{term tsynMap} is Eps-stream if stream was Eps.\<close>
lemma tsynmap_singleton_Eps: "tsynMap f\<cdot>(\<up>Eps) = \<up>Eps"
  by (simp add: tsynMap_def)

text \<open>@{term tsynMap} leaves the length of a stream unchanged.\<close>
lemma tsynmap_slen: "#(tsynMap f\<cdot>s) = #s"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} leaves the length of a tsyn stream unchanged.\<close>
lemma tsynmap_tsynlen: "tsynLen\<cdot>(tsynMap f\<cdot>ts) = tsynLen\<cdot>ts"
proof (induction ts rule: tsyn_ind)
  case adm
  then show ?case by simp
next
  case bot
  then show ?case by simp
next
  case (Eps s)
  then show ?case by (simp add: tsynlen_sconc_Eps tsynmap_sconc_Eps)
next
  case (msg m s)
  then show ?case by (simp add: tsynlen_sconc_msg tsynmap_sconc_msg)
qed

text \<open>Abstraction of @{term tsynMap} equals sMap executed on abstracted stream.\<close>
lemma tsynmap_tsynabs: "(tsynMap f\<cdot>s)\<^sup>- = smap f\<cdot>(s\<^sup>-)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_Eps)

text \<open>Every value produced by @{term tsynMap} of the function f is in @{term image} of @{term tsynApplyElem} f\<close>
lemma tsynmap_sValues: "sValues\<cdot>(tsynMap f\<cdot>s) = tsynApplyElem f ` sValues\<cdot>s"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sValues tsynmap_insert)+

text \<open>Every message produced by @{term tsynMap} of the function f is in @{term image} of f\<close>
lemma tsynmap_tsyndom: "tsynValues\<cdot>(tsynMap f\<cdot>s) = f ` tsynValues\<cdot>s"
  by (simp add: tsynmap_tsynabs tsynabs_tsyndom smap_sValues)

text \<open>Every message produced by @{term tsynMap} of the function f is in @{term range} of f\<close>
lemma tsynmap_tsyndom_range: "tsynValues\<cdot>(tsynMap f\<cdot>s) \<subseteq> range f"
  by (simp add: tsynabs_tsyndom tsynmap_tsynabs)

text \<open>@{term tsynMap} of the function f on @{term tsynMap} of the function g is 
        the function composition of f and g\<close>
lemma tsynmap_tsynmap: "tsynMap f\<cdot>(tsynMap g\<cdot>s) = tsynMap (\<lambda> x. f (g x))\<cdot>s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_Eps)

text \<open>@{term tsynMap} of the identity function leaves the stream unchanged.\<close>
lemma tsynmap_id: "tsynMap (\<lambda>x. x)\<cdot>s = s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_Eps)

lemma tsynmap_tsynmap2[simp]: "tsynMap f\<cdot>(tsynMap g\<cdot>s) = tsynMap (f\<circ>g)\<cdot>s"
  apply(induction s rule: tsyn_ind)
     apply simp_all
  by(simp add: tsynmap_sconc_Eps tsynmap_sconc_msg)+

lemma tsynmap_id2 [simp]: "tsynMap id\<cdot>s = s"
  apply(induction s rule: tsyn_ind)
  apply simp_all
  by(simp add: tsynmap_sconc_Eps tsynmap_sconc_msg)+

lemma tsynmap_funcomp_id:
  assumes "\<forall>a. f (f a) = a"
  shows "tsynMap f\<cdot>(tsynMap f\<cdot>s) = s"
  apply (induction s rule: tsyn_ind)
  apply (rule admI)
  apply (simp add: ch2ch_Rep_cfunR contlub_cfun_arg  )+
  apply (simp add: assms tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_Eps)

lemma tsynmap_inv_id[simp]: "tsynValues\<cdot>tsyn \<subseteq> range F \<Longrightarrow> tsynMap (F \<circ> (inv F))\<cdot>tsyn = tsyn"
  apply (induction tsyn rule: ind)
  apply simp_all
  apply (rename_tac x xs)
  apply (case_tac x)
  apply (auto simp add: tsynmap_sconc_msg tsynmap_sconc_Eps)[2]
  by (auto simp add:  f_inv_into_f)

lemma tsynmap_inv_eq: 
  assumes "surj f"
    and "tsynMap (inv f)\<cdot>s1 = tsynMap (inv f)\<cdot>s2"
  shows "s1 = s2"
  by (metis (no_types, lifting) UNIV_I assms subsetI tsynmap_inv_id tsynmap_tsynmap2)

text \<open>@{term tsynMap} test on finite stream.\<close>
lemma tsynMap_test_finstream: "tsynMap (plus 1)\<cdot>(<[TSynMsg 1, TSynMsg 2, TSynMsg 1, Eps]>) 
  = <[TSynMsg 2, TSynMsg 3, TSynMsg 2, Eps]>"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} test on infinite stream.\<close>
lemma tsynMap_test_infstream: "tsynMap (plus 1)\<cdot>((<[TSynMsg 3, TSynMsg 4, TSynMsg 3]>)\<^sup>\<infinity>) 
  = (<[TSynMsg 4, TSynMsg 5, TSynMsg 4]>)\<^sup>\<infinity>"
  by (simp add: tsynmap_insert)

lemma tsynmap_tick [simp]: "x \<in> sValues\<cdot>(tsynMap F\<cdot>stream) \<Longrightarrow> x \<notin> TSynMsg ` range F \<Longrightarrow> x = Eps"
  by (metis (no_types, lifting) insert_iff subsetCE tsynabs_sValues_subset_eq tsynabs_tsyndom tsynmap_tsyndom_range)

lemma tsynmap_msg [simp]: "tsynMap f\<cdot>(\<up>tsyn) = \<up>(tsynApplyElem f tsyn)"
  apply(cases tsyn)
  by(auto simp add: tsynMap_def)

text\<open>@{term tsynApplyElem} is injective if the applied function is injective.\<close>
lemma tsynapplyelem_inj: 
  assumes "inj f"
  shows "inj (tsynApplyElem f)"
  apply (rule injI)
  apply (case_tac x)
  apply (case_tac y)
    apply (simp add: assms inj_eq)+
  by (metis assms injD tsyn.distinct(1) tsyn2ustreamElem.simps(2) tsynApplyElem.elims)

text\<open>@{term tsynMap} is injective if the mapped function is injective.\<close>
lemma tsynmap_inj:
  assumes "inj f"
  shows "inj (Rep_cfun(tsynMap f))"
  apply (rule injI)
  by (simp add: assms tsynMap_def inj_eq smap_inj tsynapplyelem_inj)

text\<open>If the result of @{term tsynMap} with an injective function is equal the stream is equal.\<close>
lemma tsynmap_inj_eq:
  assumes "inj f"
    and "tsynMap f\<cdot>s = tsynMap f\<cdot>t"
  shows "s = t"
  apply (rule injD)
  using assms tsynmap_inj by blast+

lemma tsynmap_rt: "tsynMap f\<cdot>(srt\<cdot>s) = srt\<cdot>(tsynMap f\<cdot>s)"
  apply(induction s rule:tsyn_ind)
  apply auto[2]
  apply (simp add: tsynmap_sconc_msg; fail)
  by (simp add: tsynmap_sconc_Eps)

lemma map_tsyn_values1: "\<sim> \<notin> sValues\<cdot>(smap (map_tsyn f)\<cdot>s) \<Longrightarrow> \<sim> \<notin> sValues\<cdot>s"
  and map_tsyn_values2: "\<sim> \<notin> sValues\<cdot>s \<Longrightarrow> \<sim> \<notin> sValues\<cdot>(smap (map_tsyn f)\<cdot>s)"
  by (simp add: image_iff smap_sValues)+

lemma tsynMap_def2: "tsynMap f = smap (map_tsyn f)"
  by(simp add: tsynMap_def tsynApplyElem_def2)


  subsection \<open>@{term tsynFilter} and @{term tsynMap}\<close>

text \<open>@{term tsynFilter} and @{term tsynMap}\<close>

lemma tsynmapfilter: assumes "\<And>msg. msg \<notin> S \<Longrightarrow> f msg \<notin> f ` S"
  shows "tsynMap f\<cdot>(S\<ominus>\<^sub>-s) = (f`S) \<ominus>\<^sub>- (tsynMap f\<cdot>s)"
  using assms apply(induction s)
  apply (rule adm_lemmas)+
  apply (simp_all)
  apply (case_tac a, simp add: tsynfilter_sconc_Eps tsynmap_sconc_Eps)
    apply(case_tac "aa\<in>S"; simp add: tsynfilter_sconc_msg_in tsynmap_sconc_msg)
  apply(subst tsynfilter_sconc_msg_nin, simp)
  by(subst tsynfilter_sconc_msg_nin, simp_all add: tsynmap_sconc_Eps)

  subsection \<open>@{term tsynFilter} and @{term sinftimes}\<close>

  text \<open>@{term tsynFilter} and @{term sinftimes}\<close>

lemma tsynfilter_sinftimes_msg_in[simp]: 
  "tsynFilter {a}\<cdot>(sinftimes (\<up>(TSynMsg a))) = sinftimes (\<up>(TSynMsg a))"
apply (rule stream.take_lemma)
apply (induct_tac n, auto)
  apply (subst (1) sinftimes_unfold)
  apply (simp add: tsynfilter_sconc_msg_in)
  by (subst (2) sinftimes_unfold, simp)

lemma tsynfilter_sinftimes_Eps[simp]: 
  "tsynFilter A\<cdot>(sinftimes (\<up>(Eps))) = sinftimes (\<up>(Eps))"
apply (rule stream.take_lemma)
apply (induct_tac n, auto)
  apply (subst (1) sinftimes_unfold)
  apply (simp add: tsynfilter_sconc_Eps)
  by (subst (2) sinftimes_unfold, simp)

lemma tsynfilter_sinftimes_msg_nin:
  "a \<notin> F \<Longrightarrow> (F \<ominus>\<^sub>- (sinftimes (\<up>(TSynMsg a)))) = sinftimes (\<up>(Eps))"
apply (rule stream.take_lemma)
apply (induct_tac n, auto)
apply (subst (1) sinftimes_unfold)
apply (simp add: tsynfilter_sconc_msg_nin)
by (subst (2) sinftimes_unfold, simp)


lemma tsynlen_tsynfilter_sdrop_ile: 
  "#\<^sub>-(tsynFilter X\<cdot>(sdrop n\<cdot>p)) \<le> #\<^sub>-(tsynFilter X\<cdot>p)"
apply (rule spec [where x = "n"])
apply (rule ind [of _ p], auto, simp add: tsynLen_def)
apply (subst lnle_def, simp del: lnle_conv; fail)
  apply (case_tac "x", auto)      
  apply (case_tac a, simp add: tsynfilter_sconc_Eps tsynlen_sconc_Eps)
  apply (case_tac "aa \<in> X", auto)
  apply (simp_all add: tsynfilter_sconc_msg_in tsynlen_sconc_msg tsynfilter_sconc_msg_nin tsynlen_sconc_Eps) 
 apply (erule_tac x="nat" in allE)
  by (rule trans_lnle, auto)

lemma tsynFilter_sdrop_eps:"#\<^sub>-(tsynFilter X\<cdot>(sdrop 1\<cdot>(<[Eps, Eps]>))) =  #\<^sub>-(tsynFilter X\<cdot>(<[Eps, Eps]>))"
  by (metis l2s_single list2s_conc tsynfilter_tsynlen tsynlen_sconc_Eps tsynlen_singleton_Eps tsynlen_tsynfilter_sdrop_ile
      zero_eq)

lemma tsynFilter_sdrop_elem_eps: "#\<^sub>-(tsynFilter {1}\<cdot>(sdrop 1\<cdot>(<[TSynMsg 1, Eps]>))) <  #\<^sub>-(tsynFilter {1}\<cdot>(<[TSynMsg 1, Eps]>))"
  by (simp add: tsynfilter_sconc_msg_in tsynfilter_singleton_Eps tsynlen_insert)


lemma tsynlen_tsynfilter_sdrop: 
  "\<forall>p X. #\<^sub>-(tsynFilter X\<cdot>p) = \<infinity> \<longrightarrow> #\<^sub>-(tsynFilter X\<cdot>(sdrop n\<cdot>p)) = \<infinity>" 
apply (induct_tac n, auto)
  apply (rule_tac x=p in scases, auto)
  apply (case_tac a, simp add: tsynfilter_sconc_Eps tsynlen_sconc_Eps)
  apply (case_tac "aa\<in>X", auto)
  by (simp_all add: tsynfilter_sconc_msg_in tsynlen_sconc_msg tsynfilter_sconc_msg_nin tsynlen_sconc_Eps)

text \<open>@{term tsynFilter} returns \<open>\<epsilon>\<close> on its untimed variant if no element is included in the filter\<close>
lemma tsynfilter_snths_nin_stake: 
  "\<forall>p. (\<forall>n. Fin n < #\<^sub>-p \<longrightarrow> snth n (p\<^sup>-) \<notin> X) \<longrightarrow> (tsynFilter X\<cdot>(stake k\<cdot>p))\<^sup>- = \<epsilon>"
apply (induct_tac k, auto)
apply (rule_tac x=p in scases, auto) 
apply (case_tac a, simp add: tsynfilter_sconc_Eps tsynlen_sconc_Eps)
apply (case_tac "aa\<in>X", auto)
apply (simp add: tsynfilter_sconc_msg_in tsynlen_sconc_msg)
apply (erule_tac x="0" in allE, simp)
apply (case_tac "n", auto, simp add: tsynfilter_singleton_msg_nin)
apply (simp add: tsynfilter_sconc_msg_nin tsynlen_sconc_msg)
by (metis lnat_fin8 snth_scons)

lemma tsynfilter_snths_nin:
   "(\<forall>n. Fin n < #\<^sub>-p \<longrightarrow> snth n p\<^sup>- \<notin> X) \<Longrightarrow> (tsynFilter X\<cdot>p)\<^sup>- = \<epsilon>"
apply (subgoal_tac "(tsynFilter X\<cdot>p)\<^sup>- = (\<Squnion>k. tsyn2ustream\<cdot>(tsynFilter X\<cdot>(stake k\<cdot>p)))")
apply (erule ssubst)
apply (subst lub_eq_bottom_iff, simp)
apply (subst tsynfilter_snths_nin_stake, simp+)
apply (subst contlub_cfun_arg [THEN sym], simp)+
by (simp add: reach_stream)

text \<open>@{term tsynFilter} returns the original tsyn streams if every message is included in the filter\<close>
lemma tsynfilter_snths_in_stake: 
  "\<forall>p. (\<forall>n. Fin n < #p \<longrightarrow> snth n (p\<^sup>-) \<in> X)
    \<longrightarrow> tsynFilter X\<cdot>(stake k\<cdot>p) = stake k\<cdot>p"
  apply (induct_tac k, auto)
  apply (rule_tac x=p in scases, auto)
  apply (case_tac a, simp add: tsynfilter_sconc_Eps)
  apply (case_tac "aa\<in>X", auto)
   apply (case_tac "n", auto, simp add: tsynfilter_singleton_msg_in)
  apply (simp add: tsynfilter_sconc_msg_in)
  apply (erule_tac x="s" in allE, auto)
  apply (erule_tac x="Suc n" in allE, auto)
  by (erule_tac x="0" in allE, simp) 

lemma tsynfilter_snths_in: assumes "(\<forall>n. Fin n < #p \<longrightarrow> snth n (p\<^sup>-) \<in> X)" 
  shows "p = tsynFilter X\<cdot>(p)"
  apply (subst reach_stream [THEN sym], rule sym)
  apply (subst reach_stream [THEN sym],case_tac "#p=\<infinity>")
  apply (metis (no_types, opaque_lifting) approxl1 assms monofun_cfun_arg tsynfilter_snths_in_stake slen_stake_fst_inf ub_stake)
  by (metis (no_types, opaque_lifting) assms fin2stake ninf2Fin tsynfilter_snths_in_stake)

lemma tsynfilter_infinite:
  "#\<^sub>-(tsynFilter X\<cdot>x) = \<infinity> \<Longrightarrow>  #\<^sub>-x = \<infinity>"
by (insert tsynfilter_tsynlen [of X x], auto)

lemma tsynfilter_stake: 
  "\<forall>z. #\<^sub>-(tsynFilter X\<cdot>s) \<le> #\<^sub>-(tsynFilter X\<cdot>((stake n\<cdot>z) \<Zcat> s))"
  apply (induct_tac n, auto)
  apply (rule_tac x=z in scases, auto)
  apply (case_tac a, simp add: tsynlen_sconc_Eps tsynfilter_sconc_Eps)
  apply (case_tac "aa\<in>X", auto)
  apply (simp_all add: tsynlen_sconc_Eps tsynlen_sconc_msg tsynfilter_sconc_msg_in tsynfilter_sconc_msg_nin)
  apply (erule_tac x="sa" in allE)
  by (drule trans_lnle, auto) 

lemma tsynfilter_empty_filter:
  "\<forall>s. #s = Fin k \<and> (tsynFilter S\<cdot>s)\<^sup>- = \<epsilon> \<longrightarrow> 
       (tsynFilter S\<cdot>(s\<Zcat>t))\<^sup>- = (tsynFilter S\<cdot>t)\<^sup>-" 
  apply (induct_tac k, auto)
  apply (rule_tac x=s in scases, auto)
  apply (case_tac a, simp add: tsynlen_sconc_Eps tsynfilter_sconc_Eps)
  apply (case_tac "aa \<in> S", auto)
  by (simp_all add: tsynlen_sconc_Eps tsynlen_sconc_msg tsynfilter_sconc_msg_in tsynfilter_sconc_msg_nin)

text \<open>A tsyn stream can be split by @{term stake} and @{term sdrop} for filtering\<close>
lemma split_tsynfilter: "tsynFilter X\<cdot>x = tsynFilter X\<cdot>(stake n\<cdot>x) \<Zcat> tsynFilter X\<cdot>(sdrop n\<cdot>x)"
apply (rule_tac x=x in spec)
apply (induct_tac n, simp)
apply (rule allI)
apply (rule_tac x=x in scases, simp)
  apply (erule_tac x="s" in allE, auto)
  apply (case_tac a, simp add: tsynlen_sconc_Eps tsynfilter_sconc_Eps)
  apply (case_tac "aa \<in> X", auto)
by (simp_all add: tsynlen_sconc_Eps tsynlen_sconc_msg tsynfilter_sconc_msg_in tsynfilter_sconc_msg_nin)


lemma int_tsynfilter[simp]: "tsynFilter S\<cdot>(tsynFilter M\<cdot>s) = tsynFilter (S \<inter> M)\<cdot>s"
  apply (rule ind [of _ s], auto)
  apply (case_tac a, simp add: tsynfilter_sconc_Eps)
  apply (case_tac "aa \<in> S \<inter> M", simp_all add: tsynfilter_sconc_Eps tsynfilter_sconc_msg_in)
  by (case_tac "aa \<in> M", simp_all add: tsynfilter_sconc_Eps tsynfilter_sconc_msg_in tsynfilter_sconc_msg_nin)


text \<open>After applying @{term "tsynMap f"}, all elements are in the range of @{term f}\<close>
lemma tsynfilter_tsynmap_nrange: 
  "a \<notin> range f \<Longrightarrow> (tsynFilter {a}\<cdot>(tsynMap f\<cdot>x))\<^sup>- = \<epsilon>"
  using tsynfilter_snths_nin 
  by (simp add: sfilter_smap_nrange tsynfilter_tsynabs tsynmap_tsynabs)
  
lemma tsynmap_tsynfilter: "inj f \<Longrightarrow> tsynMap f\<cdot>(A \<ominus>\<^sub>- s) = f ` A \<ominus>\<^sub>- tsynMap f\<cdot>s"
  apply(induction s; simp)
  apply(case_tac a, simp add: tsynfilter_sconc_Eps tsynmap_sconc_Eps)
  apply(case_tac "aa\<in>A"; simp)
  apply(simp add: tsynfilter_sconc_msg_in tsynmap_sconc_msg) 
  by (meson inj_image_mem_iff tsynmapfilter)
                                     
lemma tsynfilter_lub_inf: assumes "\<And>n. \<exists>i. Fin n \<le> #\<^sub>-(A \<ominus>\<^sub>- (Y i))" and "chain Y"
  shows " #\<^sub>-(A \<ominus>\<^sub>- (\<Squnion>i. Y i)) = \<infinity>"
proof(rule ccontr)
  assume as: "#\<^sub>-(A \<ominus>\<^sub>- (\<Squnion>i::nat. Y i)) \<noteq> \<infinity>"
  obtain n where n_def:"#\<^sub>-(A \<ominus>\<^sub>- (\<Squnion>i. Y i)) = Fin n"
    using as lncases by auto
  obtain i where i_def:"Fin (Suc n) \<le>  #\<^sub>-(A \<ominus>\<^sub>- (Y i))"
    using assms(1) by blast
  have "#\<^sub>-(A \<ominus>\<^sub>- (Y i)) \<le> #\<^sub>-(A \<ominus>\<^sub>- (\<Squnion>i::nat. Y i))"
    using assms(2) cont_pref_eq1I is_ub_thelub
    by (metis lnle_def)
  thus False
    using dual_order.trans i_def n_def by fastforce
qed

lemma tsynfilter_conc_slen[simp]: assumes "#(tsynFilter A\<cdot>s2) = \<infinity>" and "#s1 < \<infinity>"
  shows "#(tsynFilter A\<cdot>(s1\<Zcat>s2)) = \<infinity>"
proof -
  have "(tsynFilter A\<cdot>(s1\<Zcat>s2)) = ((tsynFilter A\<cdot>s1) \<Zcat> (tsynFilter A\<cdot>s2))"
    using tsynfilter_sconc assms(2) lnless_def ninf2Fin by fastforce 
  thus ?thesis by (simp add: assms(1) slen_sconc_snd_inf) 
qed

lemma tsynfilter_conc_tsynlen[simp]: assumes " #\<^sub>-(tsynFilter A\<cdot>s2) = \<infinity>" and "#s1 < \<infinity>"
  shows " #\<^sub>-(tsynFilter A\<cdot>(s1\<Zcat>s2)) = \<infinity>"
proof -
  have "(tsynFilter A\<cdot>(s1\<Zcat>s2)) = ((tsynFilter A\<cdot>s1) \<Zcat> (tsynFilter A\<cdot>s2))"
    using tsynfilter_sconc assms(2) lnless_def ninf2Fin by fastforce 
  thus ?thesis 
    by (metis assms(1,2) slen_sconc_snd_inf tsynabs_sconc tsynfilter_slen
        tsynlen_insert)
qed

lemma tsynfilter_conc: assumes "a\<in>A" 
  shows "#s<\<infinity> \<Longrightarrow> #\<^sub>-(A \<ominus>\<^sub>- s) < #\<^sub>-(A \<ominus>\<^sub>- s \<Zcat> \<up>(TSynMsg a))" (is "_ \<Longrightarrow> ?F x")
  proof(induction s rule: tsyn_ind)
    case adm
    then show ?case by auto
  next
    case bot
    then show ?case 
      using assms(1) 
      by (simp add: tsynfilter_singleton_msg_in tsynlen_singleton_msg)
  next
    case (msg m s)
    then show ?case 
      apply(cases "m \<in> A"; case_tac "a\<in>A"; simp_all add: tsynfilter_sconc_Eps tsynfilter_sconc_msg_nin tsynfilter_sconc_msg_in tsynlen_sconc_Eps tsynlen_sconc_msg)
      by (metis dual_order.antisym fold_inf inf_ub not_le_imp_less)+
  next
    case (Eps s)
    then show ?case 
      apply (simp add: tsynfilter_sconc_Eps tsynlen_sconc_Eps)
      by (metis fold_inf lnsuc_le)
  qed

lemma tsynfilter_sinf [simp]: assumes  "(A \<ominus>\<^sub>-s) \<noteq> \<epsilon>"
  shows "A \<ominus>\<^sub>-(s\<^sup>\<infinity>) = ((A \<ominus>\<^sub>-s)\<^sup>\<infinity>)"
by (metis tsynfilter_sconc assms(1) rek2sinftimes sinftimes_unfold)

lemma tsynilter_srt_sinf_slen: assumes "#(A \<ominus>\<^sub>-s) = \<infinity>" 
  shows  "#(A \<ominus>\<^sub>-(srt\<cdot>s)) = \<infinity>"
  apply(cases s rule: scases,simp_all)
  using inf_scase[of s] assms tsynfilter_slen[of A s] 
   apply auto[2]
  apply (case_tac a)
  apply (simp add: tsynfilter_sconc_Eps)
  by(case_tac "aa \<in> A";simp add: tsynfilter_sconc_msg_nin tsynfilter_sconc_msg_in)

lemma tsynfilter_srt_sinf_tsynlen: assumes "#\<^sub>-(A \<ominus>\<^sub>-s) = \<infinity>" 
  shows  "#\<^sub>-(A \<ominus>\<^sub>-(srt\<cdot>s)) = \<infinity>"
  apply(cases s rule: scases,simp_all)
  using inf_scase[of s] assms tsynfilter_slen[of A s] 
   apply auto[2]
  apply (case_tac a)
  apply (simp add: tsynfilter_sconc_Eps tsynlen_sconc_Eps)
  apply(case_tac "aa \<in> A";simp_all add: tsynfilter_sconc_msg_nin tsynfilter_sconc_msg_in )
  by(simp_all add: tsynlen_sconc_Eps tsynlen_sconc_msg)

text \<open>@{term tsynFilter} on boolean streams. Some lemmas:\<close>
lemma tsynfilter_false__ntimes_len [simp]: "#\<^sub>-({True} \<ominus>\<^sub>-((sntimes n (\<up>(TSynMsg False)))\<Zcat>ora)) = #\<^sub>-({True} \<ominus>\<^sub>- ora)"
  apply(induction n, simp)
  by (metis assoc_sconc singletonD sntimes.simps(2)
      tsynfilter_sconc_msg_nin tsynlen_sconc_Eps)

lemma tsynfilter_tsynValuesl3:
  "tsynValues\<cdot>s \<subseteq> X \<longrightarrow> tsynFilter X\<cdot>s = s"
  apply (rule impI)
  apply (rule stream.take_lemma)
  apply (simp add: atomize_imp)
  apply (rule_tac x="s" in spec)
  apply (rule_tac x="X" in spec)
  apply (induct_tac n, simp+)
  apply (rule allI)+
  apply (rule impI)
  apply (rule_tac x="xa" in scases, simp+)
  apply (case_tac a, simp add: tsynfilter_sconc_Eps)
  apply (case_tac "aa\<in>x")
  by (simp_all add: tsynfilter_sconc_msg_nin tsynfilter_sconc_msg_in)

lemma tsynfilter_tsynValuesl4 [simp]:
  "tsynFilter (tsynValues\<cdot>s)\<cdot>s = s"
by (rule tsynfilter_tsynValuesl3 [rule_format, of "s" "tsynValues\<cdot>s"], simp)

lemma tsynfilter_fin_slen: assumes "#(A \<ominus>\<^sub>-s) < \<infinity>" 
  shows "\<exists>n. (A  \<ominus>\<^sub>- (sdrop n\<cdot>s)) = \<bottom>"
  apply(rule ccontr)
  apply auto 
  by (metis assms lnat_well_h2 sdropostake stake_prefix2 tsynfilter_slen
      tsynfilter_strict)

lemma tsynfilter_fin_tsynlen: assumes "#\<^sub>-(A \<ominus>\<^sub>-s) < \<infinity>" 
  shows "\<exists>n. (A  \<ominus>\<^sub>- (sdrop n\<cdot>s))\<^sup>- = \<bottom>"
  apply(rule ccontr)
  apply auto 
  by (metis assms sdrop_smap tsynabs_fin_drop tsynfilter_insert
      tsynlen_insert)

lemma tsynfilter_s_one_dom_inf: assumes "sValues\<cdot>s = {TSynMsg x}" and "#s = \<infinity>"
    shows "s = ((\<up>(TSynMsg x))\<^sup>\<infinity>)"
  by (simp add: assms(1,2) s_one_dom_inf)

lemma tsyndom_tsynfilter[simp]: "tsynValues\<cdot>(A\<ominus>\<^sub>-s) = tsynValues\<cdot>s \<inter> A"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (rule adm_eq)
  apply (intro cont2cont)
  apply (rule cont_compose [where f="\<lambda>x. tsynValues\<cdot>x"])
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: less_set_def le_infI1; fail)
  apply (simp add: less_set_def lub_eq_Union; fail)
    apply (intro cont2cont; fail)
  apply (case_tac "m \<in> A"; simp add: tsynfilter_sconc_msg_nin tsynfilter_sconc_msg_in)
  apply (simp add: tsynfilter_sconc_Eps)
  done

lemma tsyndom_tsynfilter_in: "a \<in> tsynValues\<cdot>(A \<ominus>\<^sub>-s) \<longrightarrow> a \<in> tsynValues\<cdot>s"
  by simp

lemma tsynfilter_bot_dom: "(A \<ominus>\<^sub>-s)\<^sup>- = \<bottom> \<Longrightarrow> tsynValues\<cdot>s \<subseteq> UNIV - A"
  apply(induction s rule: ind)
    apply auto
  by (metis Int_iff emptyE svalues_eps tsynabs_tsyndom
      tsyndom_tsynfilter)

lemma "({False} \<ominus>\<^sub>-(<[TSynMsg True]>))\<^sup>- = \<bottom> \<Longrightarrow> tsynValues\<cdot> (<[TSynMsg True]>) = UNIV - {False}"
  apply (simp add: tsyndom_singleton_msg)
  by auto

lemma  "({} \<ominus>\<^sub>-(<[Eps]>))\<^sup>- = \<bottom> \<Longrightarrow> tsynValues\<cdot> (<[Eps]>) \<subset> UNIV - {}"
  apply (simp add: tsynfilter_singleton_Eps tsyndom_insert) 
  by auto

lemma snth2tsyndom: "Fin n < #\<^sub>-s \<Longrightarrow> snth n (s\<^sup>-) \<in> tsynValues\<cdot>s"
  apply (auto simp add: tsyndom_insert tsynlen_insert)
  by (metis mem_Collect_eq snth2sValues tsynabs_tsyndom tsyndom_insert)

lemma tsynfilter2dom:
  "(tsynFilter {z}\<cdot>x)\<^sup>- \<noteq> \<epsilon> \<Longrightarrow> z \<in> tsynValues\<cdot>x"
  apply (subgoal_tac "\<exists>k. snth k (x\<^sup>-) =  z \<and> Fin k < #\<^sub>-x", erule exE)
  apply (erule conjE)
  apply (drule sym)  
  using snth2tsyndom apply blast
  apply (rule ccontr, simp)
  by (insert tsynfilter_snths_nin [of x "{z}"], auto)

text \<open>Further results concerning @{term tsynFilter}\<close>

lemma tsynfilter_tsyndom_eps[simp]: "tsynValues\<cdot>s \<inter> A = {} \<Longrightarrow> (A \<ominus>\<^sub>- s)\<^sup>- = \<epsilon>"
  using tsynfilter_snths_nin 
  by (metis empty_iff inf_commute int_tsynfilter tsynfilter_tsynValuesl4)

lemma tsyndom_tsynfilter_subset: "tsynValues\<cdot>(A\<ominus>\<^sub>-s)\<subseteq>tsynValues\<cdot>(A \<ominus>\<^sub>- (\<up>u \<Zcat> s))"
  apply(cases u;simp)
  by (simp add: subset_insertI2)

lemma tsyndom_tsynfilter_subset2: assumes "u\<noteq>\<bottom>"
  shows "tsynValues\<cdot>(A\<ominus>\<^sub>-s)\<subseteq>tsynValues\<cdot>(A \<ominus>\<^sub>- (u && s))"
  apply(cases u;simp add: assms)
  apply(case_tac x)
  apply (simp add: lscons_conv)
  by (simp add: le_infI1 tsyndom_sconc)

lemma "tsynValues\<cdot>({1::nat} \<ominus>\<^sub>-(<[TSynMsg 2]>)) \<subset> tsynValues\<cdot>({1} \<ominus>\<^sub>-((updis(TSynMsg 1)) && (<[TSynMsg 2]>)))" 
  apply (simp add: tsyndom_singleton_msg lscons_conv)
  by auto 
lemma "tsynValues\<cdot>({1::nat} \<ominus>\<^sub>-(<[TSynMsg 2]>)) = tsynValues\<cdot>({1} \<ominus>\<^sub>-((updis(TSynMsg 2)) && (<[TSynMsg 2]>)))" 
  by (simp add: tsyndom_singleton_msg lscons_conv)

lemma tsyndom_lub: "chain S \<Longrightarrow> tsynValues\<cdot>(\<Squnion> j. S j) = (\<Union>i. tsynValues\<cdot>(S i))"
apply (simp add: contlub_cfun_arg)
  by (simp add: lub_eq_Union)

lemma tsyndom_tsynfilter2: assumes  "x\<in>A"
shows "x\<in>tsynValues\<cdot>s \<Longrightarrow> x\<in>(tsynValues\<cdot>(A \<ominus>\<^sub>- s))"
  apply(induction s rule: tsyn_ind)
  apply(rule admI)
  apply(rule impI)
  apply (metis (mono_tags, lifting) UN_iff ch2ch_Rep_cfunR contlub_cfun_arg tsyndom_lub)
  apply simp
  by(case_tac "m \<in> A",auto simp add: assms)

lemma tsynfilter_union_tsynlen:
  assumes "A \<inter> B = {}"
  shows " #\<^sub>-(tsynFilter (A\<union>B)\<cdot>s) =  #\<^sub>-(tsynFilter A\<cdot>s) +  #\<^sub>-(tsynFilter B\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all add: tsynfilter_sconc_Eps tsynlen_sconc_Eps)
  apply (subst ladd_insert[symmetric])
  apply (simp add: tsynlen_insert len_stream_def; fail)
  apply (case_tac "m \<in> A"; case_tac "m \<in> B"; simp add: tsynfilter_sconc_msg_nin tsynfilter_sconc_msg_in tsynlen_sconc_msg) 
  using assms apply blast   
  apply (metis ab_semigroup_add_class.add_ac(1) lnat_conc_1 tsynabs_sconc_Eps tsynlen_insert)
  apply (metis (mono_tags, lifting) add.left_commute lnat_conc_1 tsynlen_sconc_Eps)
  by (metis (no_types, opaque_lifting) tsynlen_sconc_Eps)

lemma tsynfilter_subset_len:
  assumes "A \<subseteq> B"
  shows " #\<^sub>-(tsynFilter A\<cdot>s) \<le>  #\<^sub>-(tsynFilter B\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all add: tsynfilter_sconc_Eps tsynlen_sconc_Eps)
  apply (subst lnle_def)
  apply (rule adm_below) 
  apply simp_all
  apply (case_tac "m \<in> A")
  apply (metis (no_types, opaque_lifting) assms lnsuc_lnle_emb tsynfilter_sconc_msg_in
      tsynlen_sconc_msg subsetD)
  by (metis (no_types, lifting) dual_order.trans less_lnsuc tsynfilter_sconc_msg_in
      tsynlen_sconc_Eps tsynlen_sconc_Eps tsynlen_sconc_msg tsynfilter_sconc_msg_nin)

lemma assumes "{1} \<subseteq> {1::nat,2}"
  shows " #\<^sub>-(tsynFilter {1}\<cdot>(<[TSynMsg 1]>)) =  #\<^sub>-(tsynFilter {1::nat,2}\<cdot>(<[TSynMsg 1]>))"
  by (simp add: tsynfilter_singleton_msg_in  tsynlen_insert)
lemma assumes "{} \<subseteq> {1::nat}"
  shows " #\<^sub>-(tsynFilter {}\<cdot>(<[TSynMsg 1]>)) <  #\<^sub>-(tsynFilter {1::nat}\<cdot>(<[TSynMsg 1]>))"
  by (simp add: tsynfilter_singleton_msg_in tsynfilter_singleton_msg_nin tsynlen_insert)


lemma tsynfilter_tsyndom_fin_len:
  assumes "finite (tsynValues\<cdot>s)"
    and "\<And>m. m \<in> tsynValues\<cdot>s \<Longrightarrow> #\<^sub>-(tsynFilter {m}\<cdot>s) < \<infinity>"
  shows "#\<^sub>-s < \<infinity>"
  apply (subst tsynfilter_tsynValuesl4[symmetric])
  apply (insert assms)
  apply (rule_tac F="tsynValues\<cdot>s" in finite_induct)
  apply (simp add: tsynfilter_empty)+
  apply (subst insert_is_Un)
  by (metis antisym_conv3 inf_great sfilter_svalues_fin_len tsynabs_tsyndom tsynfilter_tsynabs tsynfilter_infinite tsynlen_insert)

lemma tsynfilter_tsyndom_inf_len_ex:
  assumes "#\<^sub>-s = \<infinity>"
    and "finite (tsynValues\<cdot>s)"
  shows "\<exists>m \<in> tsynValues\<cdot>s. #\<^sub>-({m} \<ominus>\<^sub>- s) = \<infinity>"
  by (metis assms order_less_irrefl order_neq_le_trans tsynfilter_tsyndom_fin_len tsynfilter_tsynlen)

lemma tsynabs_tsyndom_empty: "s\<^sup>- = \<epsilon> \<Longrightarrow> tsynValues\<cdot>s = {}"
  by (simp add: tsynabs_tsyndom)

lemma tsynabs_empty_ticks_only_inf:
  assumes "s\<^sup>- = \<epsilon>" and " #s=\<infinity>"
  shows "s = ((\<up>Eps)\<^sup>\<infinity>)"
  by (simp add: assms(1,2) tsyn_ticks_only_inf tsynabs_tsyndom)

lemma tsynabs_empty_ticks_only_fin:
  assumes "s\<^sup>- = \<epsilon>" and "#s = Fin n"
  shows "s = sntimes n (\<up>Eps)"
  by (simp add: assms(1,2) tsyn_ticks_only tsynabs_tsyndom)

lemma tsynfilter_tsynmap_image:"inj f \<Longrightarrow> ((tsynFilter S\<cdot>i)\<^sup>- = \<epsilon>) \<longleftrightarrow> ((tsynFilter (f ` S)\<cdot>(tsynMap f\<cdot>i))\<^sup>- = \<epsilon>)"
  by (simp add: sfilter_image tsynfilter_tsynabs tsynmap_tsynabs)

lemma tsynfilter_tsynmap_tsynabs_empty:"((tsynFilter S\<cdot>i)\<^sup>- = \<epsilon>) \<longleftrightarrow> ((tsynMap f\<cdot>((tsynFilter S\<cdot>i)))\<^sup>- = \<epsilon>)"
  by (simp add: sfilter_smap tsynfilter_tsynabs tsynmap_tsynabs)

lemma tsynfilter_redimage:"inj f \<Longrightarrow> f ` {m. fst (f m) = c} \<ominus>\<^sub>- tsynMap f\<cdot>s = {m. fst ( m) = c} \<ominus>\<^sub>- tsynMap f\<cdot>s"
  apply(induction s rule: tsyn_ind)
  apply (simp_all add: tsynfilter_sconc_Eps tsynmap_sconc_Eps)
  apply(case_tac "f m \<in> {m. fst m = c}"; simp add: tsynmap_sconc_msg tsynfilter_sconc_msg_in)
  by (simp add: inj_image_mem_iff tsynfilter_sconc_msg_nin)

lemma tsyndom2snth2: "z \<in> tsynValues\<cdot>s \<Longrightarrow> \<exists>n. snth n s = TSynMsg z \<and> Fin n < #s"
  by (simp add: sValues2snth2 tsyndom_insert)

lemma snth_tsynfilter_ex2: assumes "Fin n < #(tsynFilter A\<cdot>s)" and  "snth n (tsynFilter A\<cdot>s) = TSynMsg m"
  shows "\<exists>n. Fin n < #s \<and> snth n s = TSynMsg m" 
proof (rule ccontr)
  assume h: "\<not>(\<exists>n. Fin n < #s \<and> snth n s = TSynMsg m)"
  hence h': "\<forall>n. Fin n < #s \<Longrightarrow> snth n s \<noteq> TSynMsg m" by simp
  then obtain n where n: "snth n (tsynFilter A\<cdot>s) = TSynMsg m  \<and> Fin n < #(tsynFilter A\<cdot>s)"
    using assms by blast
  hence "snth n (tsynFilter A\<cdot>s) \<in> sValues\<cdot>(tsynFilter A\<cdot>s)"
    using snth2sValues by blast
  hence "snth n (tsynFilter A\<cdot>s) \<in> sValues\<cdot>s"
  by (metis mem_Collect_eq n tsyndom_insert tsyndom_tsynfilter_in)
  hence "\<exists>n. Fin n < #s \<and> snth n s = TSynMsg m"
    using n sValues2snth_strong by auto
    thus False 
    using  h' h by force
qed

lemma tsynfilter_snth_distr: assumes"Fin n < #s" 
    shows "\<up>(snth n (tsynFilter A\<cdot>s)) = tsynFilter A\<cdot>(\<up>(snth n s))"
proof -
  have len: "Fin n < #s \<Longrightarrow> #(tsynFilter A\<cdot>(stake n\<cdot>s)) = n"
    by (simp add: slen_stake tsynfilter_slen)
  have  s: "Fin n < #s \<Longrightarrow> s = (stake n\<cdot>s)  \<Zcat> (\<up>(snth n s)) \<Zcat> (sdrop (Suc n)\<cdot>s)"
    by (metis assoc_sconc split_streaml1 stake_step_last)
  then have "Fin n < #s \<Longrightarrow> tsynFilter A\<cdot>s = tsynFilter A\<cdot>(stake n\<cdot>s) \<Zcat> tsynFilter A\<cdot> (\<up>(snth n s)) \<Zcat> tsynFilter A\<cdot>(sdrop (Suc n)\<cdot>s) " 
    by (metis tsynfilter_sconc)
  then have "Fin n < #s \<Longrightarrow> \<up>(snth n (tsynFilter A\<cdot>s)) = \<up>(snth n ( tsynFilter A\<cdot>(stake n\<cdot>s) \<Zcat> tsynFilter A\<cdot> (\<up>(snth n s)) \<Zcat> tsynFilter A\<cdot>(sdrop (Suc n)\<cdot>s)))" 
    by simp 
  then have "Fin n < #s \<Longrightarrow> \<up>(snth n (tsynFilter A\<cdot>s)) = tsynFilter A\<cdot>(\<up>(snth n s)) "
    using s len 
    by (smt assoc_sconc fin_le_inf less2lnleD sconc_neq slen_stake stake_prefix2 stake_step_last tsynfilter_sconc
        tsynfilter_slen)
  then show ?thesis 
    using assms by blast
qed

lemma snth_tsynfilter: assumes "Fin n < #(tsynFilter A\<cdot>s)" and  "snth n (tsynFilter A\<cdot>s) = TSynMsg m"
  shows "Fin n < #s \<and> snth n s = TSynMsg m" 
proof -
  have "\<up>(snth n (tsynFilter A\<cdot>s)) = tsynFilter A\<cdot>(\<up>(snth n s))"
    by (metis assms tsynfilter_snth_distr tsynfilter_slen)
  then have "tsynFilter A\<cdot>(\<up>(snth n s)) = \<up>(TSynMsg m)"
    using assms by auto
  then have "\<up>(snth n s) = \<up>(TSynMsg m)"
    by (metis not_Msg_eq sup_eq_iff tsynfilter_singleton_Eps tsynfilter_singleton_msg_in tsynfilter_singleton_msg_nin) 
  then show ?thesis 
    by (metis assms(1) sup_eq_iff tsynfilter_slen)
qed


lemma snth_tsynfilter2: assumes "Fin n < #s" and "snth n s = TSynMsg m" and "m \<in> A"
  shows "Fin n < #(tsynFilter A\<cdot>s) \<and> snth n (tsynFilter A\<cdot>s) = TSynMsg m" 
  by (metis assms(1,2,3) smap_snth_lemma tsynFilterElem.simps(2) tsynFilter_def tsynfilter_slen)

lemma tsynfilter_id[simp]: "tsynFilter UNIV = ID"
  apply(rule cfun_eqI, rename_tac s, induct_tac s; simp)
  by(case_tac a; simp add:  tsynfilter_sconc_Eps tsynfilter_sconc_msg_in tsynfilter_sconc_msg_nin)

lemma tsynfitler_univ_tsynlen:
  assumes" A \<union> B = UNIV"
  and"A \<inter> B = {}"
  shows "#\<^sub>-(tsynFilter A\<cdot>b) + #\<^sub>-(tsynFilter B\<cdot>b) = #\<^sub>-b"
  by(subst tsynfilter_union_tsynlen[symmetric],simp_all add: assms)

lemma tsynfilter_bool_tsynlen:"#\<^sub>-(tsynFilter {True}\<cdot>b) + #\<^sub>-(tsynFilter {False}\<cdot>b) = #\<^sub>-b"
  by(simp_all add: tsynfitler_univ_tsynlen UNIV_bool)

lemma tsynlen_infinite_true_or_false:
  "#\<^sub>-b = \<infinity> \<longrightarrow> #\<^sub>-(tsynFilter {True}\<cdot>b) = \<infinity> \<or> #\<^sub>-(tsynFilter {False}\<cdot>b) = \<infinity>"
  apply(subst tsynfilter_bool_tsynlen[symmetric])
  apply auto 
  by (metis inf_great linorder_less_linear plus_lnatInf_r plus_unique_l)

lemma infeps_ustream[simp]:"\<up>\<sim>\<^sup>\<infinity>\<^sup>- = \<epsilon>"
  by(simp add: tsyn2ustream_def)

lemma infeps_tsynlen[simp]:" #\<^sub>-\<up>\<sim>\<^sup>\<infinity> = 0"
  by(simp add: tsynlen_insert)



text \<open>@{term tsynProjFst} insertion lemma.\<close>
lemma tsynprojfst_insert: "tsynProjFst\<cdot>s = smap tsynFst\<cdot>s"
  by (simp add: tsynProjFst_def)

text \<open>@{term tsynProjFst} maps the empty stream on the empty stream.\<close>
lemma tsynprojfst_strict [simp]: "tsynProjFst\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynprojfst_insert)

text \<open>@{term tsynProjFst} distributes over concatenation.\<close>
lemma tsynprojfst_sconc_msg: "tsynProjFst\<cdot>(\<up>(TSynMsg (a, b)) \<Zcat> as) = \<up>(TSynMsg a) \<Zcat> (tsynProjFst\<cdot>as)"
  by (simp add: tsynprojfst_insert)
 
text \<open>@{term tsynProjFst} ignores empty time-slots.\<close>
lemma tsynprojfst_sconc_Eps: "tsynProjFst\<cdot>(\<up>Eps \<Zcat> s) = \<up>Eps \<Zcat> tsynProjFst\<cdot>s"
  by (simp add: tsynprojfst_insert)

text \<open>@{term tsynProjFst} of the concatenation of two streams equals the concatenation of 
        @{term tsynProjFst} of both streams.\<close>
lemma tsynprojfst_sconc: "tsynProjFst\<cdot>(a1 \<Zcat> a2) = tsynProjFst\<cdot>a1 \<Zcat> tsynProjFst\<cdot>a2"
  by (simp add: smap_split tsynprojfst_insert)

text \<open>@{term tsynProjFst} creates a new one element stream where only the first message component
        is used.\<close>
lemma tsynprojfst_singleton_msg: "tsynProjFst\<cdot>(\<up>(TSynMsg a)) = \<up>(TSynMsg (fst a))"
  by (simp add: tsynProjFst_def)

text \<open>@{term tsynProjFst} does nothing on empty time slots.\<close>
lemma tsynprojfst_singleton_Eps: "tsynProjFst\<cdot>(\<up>Eps) = \<up>Eps"
  by (simp add: tsynProjFst_def)

text \<open>@{term tsynProjFst} leaves the length of a stream unchanged.\<close>
lemma tsynprojfst_slen: "#(tsynProjFst\<cdot>s) = #s"
  by (simp add: tsynprojfst_insert)

text \<open>Abstraction of @{term tsynProjFst} equals sprojfst executed on abstracted stream.\<close>
lemma tsynprojfst_tsynabs: "(tsynProjFst\<cdot>s)\<^sup>- = sprojfst\<cdot>(s\<^sup>-)"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by simp
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    obtain a where pair_def: "\<exists>b. m = (a, b)"
      by (meson surj_pair)
    obtain b where m_def: "m = (a, b)"
      using pair_def by blast
    then show ?case
      by (simp add: m_def tsynprojfst_sconc_msg  msg.IH)
  next
    case (Eps s)
    then show ?case
      by (simp add: tsynprojfst_sconc_Eps)
  qed

text \<open>@{term tsynProjFst} leaves the length of a time abstracted stream unchanged.\<close>
lemma tsynprojfst_tsynlen: "tsynLen\<cdot>(tsynProjFst\<cdot>ts) = tsynLen\<cdot>ts"
proof (induction ts rule: tsyn_ind)
  case adm
  then show ?case by simp
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  obtain a  where b_def: "\<exists>b. m = (a, b)" 
    by fastforce
  obtain b where m_def: "m = (a, b)"
    using b_def by auto
  then show ?case 
    by (simp add: m_def tsynprojfst_sconc_msg tsynlen_sconc_msg msg.IH)
next
  case (Eps s)
  then show ?case by (simp add: tsynlen_sconc_Eps tsynprojfst_sconc_Eps)
qed

text \<open>Every value produced by @{term tsynProjFst} is in the image of @{term tsynFst}\<close>
lemma tsynprojfst_sValues: "sValues\<cdot>(tsynProjFst\<cdot>s) = tsynFst ` sValues\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sValues tsynprojfst_insert)+

text \<open>Every message produced by @{term tsynProjFst} is in the image of @{term fst}\<close>
lemma tsynprojfst_tsyndom: "tsynValues\<cdot>(tsynProjFst\<cdot>s) = fst ` tsynValues\<cdot>s"
  by (simp add: tsynabs_tsyndom tsynprojfst_tsynabs sprojfst_def smap_sValues)

text \<open>@{term tsynProjFst} test on finite stream.\<close>
lemma tsynprojfst_test_finstream:
  "tsynProjFst\<cdot>(<[TSynMsg (1, 2), TSynMsg (3, 2), Eps, Eps, TSynMsg (2, 1), Eps]>) 
     = (<[TSynMsg 1, TSynMsg 3, Eps, Eps, TSynMsg 2, Eps]>)"
  by (simp add: tsynprojfst_insert)

text \<open>@{term tsynProjFst} test on infinitely many time-slots.\<close>
lemma tsynprojfst_test_infstream: 
  "tsynProjFst\<cdot>((<[ TSynMsg (1, 2), Eps]>)\<^sup>\<infinity>) = (<[TSynMsg 1, Eps]>)\<^sup>\<infinity>"
  by(simp add: tsynprojfst_insert)

lemma sscanl_arbitrary_output: "sprojfst\<cdot>(sscanl (\<lambda>(_,b). f b) (u1, st)\<cdot>s) 
          = sprojfst\<cdot>(sscanl (\<lambda>(_,b). f b) (u2, st)\<cdot>s)"
proof -
  have "\<forall>a b aa s. sscanl (\<lambda>(a, y). f y) (a, b)\<cdot>s = sscanl (\<lambda>(a, y). f y) (aa, b)\<cdot>s \<or> s = \<epsilon>"
    using streamcases by force
  then show ?thesis
    by (metis (no_types) fair_sscanl slen_empty_eq)
qed


text \<open>@{term tsynProjSnd} insertion lemma.\<close>
lemma tsynprojsnd_insert: "tsynProjSnd\<cdot>s = smap tsynSnd\<cdot>s"
  by (simp add: tsynProjSnd_def)

text \<open>@{term tsynProjSnd} maps the empty stream on the empty stream.\<close>
lemma tsynprojsnd_strict [simp]: "tsynProjSnd\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynprojsnd_insert)

text \<open>@{term tsynProjSnd} distributes over concatenation.\<close>
lemma tsynprojsnd_sconc_msg: 
   "tsynProjSnd\<cdot>(\<up>(TSynMsg (a, b)) \<Zcat> as) = \<up>(TSynMsg b) \<Zcat> (tsynProjSnd\<cdot>as)"
  by (simp add: tsynprojsnd_insert)
 
text \<open>@{term tsynProjSnd} ignores empty time-slots.\<close>
lemma tsynprojsnd_sconc_Eps: "tsynProjSnd\<cdot>(\<up>Eps \<Zcat> s) = \<up>Eps \<Zcat> tsynProjSnd\<cdot>s"
  by (simp add: tsynprojsnd_insert)

text \<open>@{term tsynProjSnd} of the concatenation of two streams equals the concatenation of 
        @{term tsynProjSnd} of both streams.\<close>
lemma tsynprojsnd_sconc: "tsynProjSnd\<cdot>(a1 \<Zcat> a2) = tsynProjSnd\<cdot>a1 \<Zcat> tsynProjSnd\<cdot>a2"
  by (simp add: smap_split tsynprojsnd_insert)

text \<open>@{term tsynProjSnd} creates a new one element stream where only the first message component
        is used.\<close>
lemma tsynprojsnd_singleton_msg: "tsynProjSnd\<cdot>(\<up>(TSynMsg a)) = \<up>(TSynMsg (snd a))"
  by (simp add: tsynProjSnd_def)

text \<open>@{term tsynProjSnd} ignores empty time slots.\<close>
lemma tsynprojsnd_singleton_Eps: "tsynProjSnd\<cdot>(\<up>Eps) = \<up>Eps"
  by (simp add: tsynProjSnd_def)

text \<open>@{term tsynProjSnd} leaves the length of a stream unchanged.\<close>
lemma tsynprojsnd_slen: "#(tsynProjSnd\<cdot>s) = #s"
  by (simp add: tsynprojsnd_insert)

lemma tsynprojsnd_tsynlen: "tsynLen\<cdot>(tsynProjSnd\<cdot>ts) = tsynLen\<cdot>ts"
proof (induction ts rule: tsyn_ind)
  case adm
  then show ?case by simp
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  obtain b  where b_def: "\<exists>a. m = (a, b)" 
    by (meson surj_pair)
  obtain a where m_def: "m = (a, b)"
    using b_def by auto
  then show ?case 
    by (simp add: m_def tsynprojsnd_sconc_msg tsynlen_sconc_msg msg.IH)
next
  case (Eps s)
  then show ?case by (simp add: tsynlen_sconc_Eps tsynprojsnd_sconc_Eps)
qed

text \<open>Abstraction of @{term tsynProjSnd} equals sprojsnd executed on abstracted stream.\<close>
lemma tsynprojsnd_tsynabs: "(tsynProjSnd\<cdot>s)\<^sup>- = sprojsnd\<cdot>(s\<^sup>-)"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by simp
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    obtain a where pair_def: "\<exists>b. m = (a, b)"
      by (meson surj_pair)
    obtain b where m_def: "m = (a, b)"
      using pair_def by blast
    then show ?case
      by (simp add: m_def tsynprojsnd_sconc_msg  msg.IH)
  next
    case (Eps s)
    then show ?case
      by (simp add: tsynprojsnd_sconc_Eps)
  qed

text \<open>Every value produced by @{term tsynProjSnd} is in the image of @{term tsynSnd}\<close>
lemma tsynprojsnd_sValues: "sValues\<cdot>(tsynProjSnd\<cdot>s) = tsynSnd ` sValues\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sValues tsynprojsnd_insert)+

text \<open>Every message produced by @{term tsynProjSnd} is in the image of @{term snd}\<close>
lemma tsynprojsnd_tsyndom: "tsynValues\<cdot>(tsynProjSnd\<cdot>s) = snd ` tsynValues\<cdot>s"
  by (simp add: tsynabs_tsyndom tsynprojsnd_tsynabs sprojsnd_def smap_sValues)

text \<open>@{term tsynProjSnd} test on finite stream.\<close>
lemma tsynprojsnd_test_finstream: 
  "tsynProjSnd\<cdot>(<[TSynMsg (1, 2), TSynMsg (3, 2), Eps, Eps, TSynMsg (2, 1), Eps]>) 
     = (<[TSynMsg 2, TSynMsg 2, Eps, Eps, TSynMsg 1, Eps]>)"
  by (simp add: tsynprojsnd_insert)

text \<open>@{term tsynProjSnd} test on infinitely many time-slots.\<close>
lemma tsynprojsnd_test_infstream: 
  "tsynProjSnd\<cdot>((<[ TSynMsg (1, 2), Eps]>)\<^sup>\<infinity>) = (<[TSynMsg 2, Eps]>)\<^sup>\<infinity>"
  by (simp add: tsynprojsnd_insert)

lemma slen_tsynproj1_tsynproj2: "#(\<Pi>\<^sub>1\<^sub>-x) = #(\<Pi>\<^sub>2\<^sub>-x)"
  by (simp add: tsynProjFst_def tsynProjSnd_def)

lemma tsynlen_tsynproj1_tsynproj2: "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-x) = #\<^sub>-(\<Pi>\<^sub>2\<^sub>-x)"
  by (simp add: tsynprojfst_tsynlen tsynprojsnd_tsynlen) 


declare tsynZip.simps [simp del]

text \<open>@{term tsynZip} is strict.\<close>
lemma tsynzip_strict [simp]: 
  "tsynZip\<cdot>\<epsilon>\<cdot>\<epsilon> = \<epsilon>"
  "tsynZip\<cdot>\<epsilon>\<cdot>x = \<epsilon>"
  "tsynZip\<cdot>y\<cdot>\<epsilon> = \<epsilon>"
  by (fixrec_simp)+

text \<open>@{term tsynZip} distributes over concatenation.\<close>
lemma tsynzip_sconc_msg:
  "tsynZip\<cdot>(\<up>(TSynMsg x) \<Zcat> xs)\<cdot>(\<up>y \<Zcat> ys) = \<up>(TSynMsg (x,y)) \<Zcat> tsynZip\<cdot>xs\<cdot>ys"
  by (metis (no_types, lifting) tsynZip.simps(3) inverseMsg.simps(2) lscons_conv tsyn.distinct(1) 
      undiscr_Discr)

text \<open>@{term tsynZip} distributes over concatenation, having the first Stream consist of one
        Eps-element and the second stream is non-empty.\<close>
lemma tsynzip_sconc_Eps:
  assumes "ys \<noteq> \<epsilon>"
  shows "tsynZip\<cdot>(\<up>Eps \<Zcat> xs)\<cdot>ys = \<up>Eps \<Zcat> tsynZip\<cdot>xs\<cdot>ys"
  by (metis (no_types, opaque_lifting) assms tsynZip.simps(3) lscons_conv scases undiscr_Discr)

text \<open>@{term tsynZip} of the concatenation of two streams equals the concatenation of 
       @{term tsynZip} of both streams.\<close>
lemma tsynzip_sconc:
  assumes "#as < \<infinity>"
    and "as \<noteq> \<epsilon>"
    and "sfoot as = (TSynMsg a)"
    and "tsynLen\<cdot>as = #bs"
  shows "tsynZip\<cdot>(as \<Zcat> xs)\<cdot>(bs \<Zcat> ys) = tsynZip\<cdot>as\<cdot>bs \<Zcat> tsynZip\<cdot>xs\<cdot>ys"
  using assms 
  proof (induction as arbitrary: a bs xs ys rule: tsyn_finind)
    case fin
    then show ?case
      by (simp add: assms)
  next
    case bot
    then show ?case 
      by (simp add: assms)
  next
    case (msg m s)
    hence s_fin: "#s < \<infinity>"
      using leI msg.prems(1) by fastforce
    have s_nempty_sfoot: "s \<noteq> \<epsilon> \<Longrightarrow> sfoot s = sfoot (\<up>(TSynMsg m) \<Zcat> s)"
      by (metis Zero_lnless_infty inf_ub less_lnsuc linorder_not_le lnat.injects msg.prems(1) 
          order_eq_iff sconc_snd_empty sfoot_conc slen_scons slen_zero)
    then show ?case 
      proof (cases rule: scases [of bs])
        case bottom
        then show ?thesis 
          by (metis lnat.con_rews lnzero_def msg.prems(4) only_empty_has_length_0 tsynlen_sconc_msg)
      next
        case (scons a t)
        have tsynlen_slen_eq: "#\<^sub>-s = #t"
          by (metis lnat.sel_rews(2) msg.prems(4) scons slen_scons tsynlen_sconc_msg)
        hence "tsynZip\<cdot>(s \<Zcat> xs)\<cdot>(t \<Zcat> ys) = tsynZip\<cdot>s\<cdot>t \<Zcat> tsynZip\<cdot>xs\<cdot>ys"
          using s_fin msg.IH msg.prems(3) s_nempty_sfoot by fastforce
        then show ?thesis
          by (simp add: scons tsynzip_sconc_msg)
      qed
  next
    case (Eps s)
    hence s_fin: "#s < \<infinity>"
      using leI Eps.prems(1) by fastforce
    have s_nempty_sfoot: "s \<noteq> \<epsilon> \<Longrightarrow> sfoot s = sfoot (\<up>Eps \<Zcat> s)"
      by (metis Zero_lnless_infty inf_ub less_lnsuc linorder_not_le lnat.injects Eps.prems(1) 
          order_eq_iff sconc_snd_empty sfoot_conc slen_scons slen_zero)
    then show ?case 
      proof (cases rule: scases [of bs])
        case bottom
        then show ?thesis 
          using Eps.prems(1) Eps.prems(3) Eps.prems(4) tsynlen_sfoot_msg_geq by force
      next
        case (scons a t)
        have tsynlen_slen_eq: "#\<^sub>-s = #bs"
          by (metis Eps.prems(4) tsynlen_sconc_Eps)
        hence "tsynZip\<cdot>(s \<Zcat> xs)\<cdot>(bs \<Zcat> ys) = tsynZip\<cdot>s\<cdot>bs \<Zcat> tsynZip\<cdot>xs\<cdot>ys" 
          using Eps.IH Eps.prems(3) s_nempty_sfoot s_fin by fastforce
        then show ?thesis 
          by (simp add: scons tsynzip_sconc_Eps)
      qed
  qed

text \<open>@{term tsynZip} zips a non-empty singleton stream to a pair with the first element
        of the second stream.\<close>
lemma tsynzip_singleton_msg_first: "tsynZip\<cdot>(\<up>(TSynMsg a))\<cdot>(\<up>b \<Zcat> bs) = \<up>(TSynMsg (a, b))"
  by (metis lscons_conv sup'_def tsynZip.simps(1) tsynzip_sconc_msg)

text\<open>@{term tsynZip} zips a non-empty tsyn stream to a pair with the element of the second
       singleton stream.\<close>
lemma tsynzip_singleton_msg_second: "tsynZip\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(\<up>b) = \<up>(TSynMsg (a, b))"
  by (metis lscons_conv sup'_def tsynzip_sconc_msg tsynzip_strict(3))

text \<open>@{term tsynZip} Empty singleton streams are zipping to Eps.\<close>
lemma tsynzip_singleton_Eps_first: 
  assumes "s \<noteq> \<epsilon>"
  shows "tsynZip\<cdot>(\<up>Eps)\<cdot>s = \<up>Eps"
  by (metis (no_types, lifting) assms lscons_conv sup'_def tsynZip.simps(1) tsynzip_sconc_Eps)

text\<open>@{term tsynZip} zips a tsyn stream beginning with Eps to a pair of Eps concatenated with
       the zipping of rest of the tsyn stream and the singleton stream\<close>
lemma tsynzip_singleton_Eps_second: "tsynZip\<cdot>(\<up>Eps \<Zcat> as)\<cdot>(\<up>b) = \<up>Eps \<Zcat> tsynZip\<cdot>as\<cdot>(\<up>b)"
  by (simp add: tsynzip_sconc_Eps)

text \<open>@{term tsynZip} keEps the length of the finite stream.\<close>
lemma tsynzip_slen: "#bs = \<infinity> \<Longrightarrow> #(tsynZip\<cdot>as\<cdot>bs) = #as"
  proof (induction as arbitrary: bs rule: tsyn_ind)
    case adm 
    then show ?case 
      apply (rule admI)
      by (simp add: contlub_cfun_fun contlub_cfun_arg len_stream_def)
  next
    case bot
    then show ?case by simp
  next
    case (Eps s)
    then show ?case 
      by (simp add: only_empty_has_length_0 tsynzip_sconc_Eps)
  next
    case (msg m s)
    then show ?case
      by (metis (no_types, lifting) inf_scase slen_scons tsynzip_sconc_msg)
  qed 

text \<open>Abstraction of @{term tsynZip} equals szip executed on abstracted stream.\<close>
lemma tsynzip_tsynabs: "(tsynZip\<cdot>as\<cdot>bs)\<^sup>- = szip\<cdot>(as\<^sup>-)\<cdot>bs"
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rename_tac x y z)
  apply (rule_tac x = z in scases, simp_all)
  apply (simp add: tsynzip_sconc_msg)
  apply (rename_tac x y)
  apply (case_tac "y = \<epsilon>", simp_all)
  by (simp add: tsynzip_sconc_Eps)

text \<open>@{term tsynZip} keEps the length of the finite stream.\<close>
lemma tsynzip_tsynlen: "#bs = \<infinity> \<Longrightarrow> tsynLen\<cdot>(tsynZip\<cdot>as\<cdot>bs) = tsynLen\<cdot>as"
  apply (simp add: tsynLen_def tsynzip_tsynabs)
  by (metis (mono_tags, lifting) inf_ub min.orderE szip_len tsynLen_def tsynlen_insert tsynzip_tsynabs)

text \<open>@{term tsynProjFst} of @{term tsynZip} equals the first stream, if the length of it is
        less than or equal to the length of the second stream.\<close>
lemma tsynzip_tsynprojfst: 
  assumes "#as \<le> #bs"
  shows "tsynProjFst\<cdot>(tsynZip\<cdot>as\<cdot>bs) = as"
  using assms
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rule adm_all)
  apply (rule adm_imp, simp_all)
  apply (rule admI)
  apply (metis dual_order.antisym inf_chainl4 inf_ub l42)
  apply (rename_tac xs ys)
  apply (case_tac "ys = \<epsilon>", simp_all)
  apply (metis lnsuc_lnle_emb srt_decrements_length surj_scons tsynprojfst_sconc_msg 
         tsynzip_sconc_msg)
  apply (rename_tac xs ys)
  apply (case_tac "ys = \<epsilon>", simp_all)
  by (metis (no_types, lifting) less_lnsuc trans_lnle tsynprojfst_sconc_Eps tsynzip_sconc_Eps)

text \<open>Abstraction of @{term tsynProjFst} of @{term tsynZip} equals the abstraction of the first 
        stream if the number of messages of the first stream is less than or equal to the length of 
        the second stream.\<close>
lemma tsynzip_tsynprojfst_tsynabs:
  assumes "tsynLen\<cdot>as \<le> #bs"
  shows "(tsynProjFst\<cdot>(tsynZip\<cdot>as\<cdot>bs))\<^sup>- = as\<^sup>-"
  using assms
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rule adm_all, rule adm_imp, simp_all)
  apply (rule admI)
  apply (meson dual_order.trans is_ub_thelub lnle_def monofun_cfun_arg)
  apply (rename_tac xs ys)
  apply (rule_tac x = ys in scases, simp_all)
  apply (simp add: tsynlen_insert)
  apply (simp add:  tsynlen_sconc_msg tsynprojfst_sconc_msg tsynzip_sconc_msg)
  apply (rename_tac xs ys)
  apply (case_tac "ys = \<epsilon>")
  apply (simp add: tsynlen_insert)
  by (simp add:  tsynlen_sconc_Eps tsynprojfst_tsynabs tsynzip_tsynabs)

text \<open>Abstraction of @{term tsynProjSnd} of @{term tsynZip} equals the second stream if its length
        is less than or equal to the number of messages in the second stream.\<close> 
lemma tsynzip_tsynprojsnd_tsynabs:
  assumes "#bs \<le> tsynLen\<cdot>as"
  shows "(tsynProjSnd\<cdot>(tsynZip\<cdot>as\<cdot>bs))\<^sup>- = bs"
  using assms
  apply (induction bs arbitrary: as rule: ind, simp_all)
  apply (rule adm_all, rule adm_imp, simp_all)
  apply (rule admI)
  apply (metis dual_order.antisym inf_chainl4 inf_ub l42)
  by (simp add: szip_sprojsnd tsynlen_insert tsynprojsnd_tsynabs tsynzip_tsynabs)

text \<open>@{term sValues} of @{term tsynZip} is subset of the @{term image} of @{term TSynMsg} 
        on the Cartesian product of @{term tsynValues} of the first stream 
        and @{term sValues} of the second stream @{term union} Eps.\<close>
lemma tsynzip_sValues: "sValues\<cdot>(tsynZip\<cdot>as\<cdot>bs) \<subseteq> (TSynMsg ` (tsynValues\<cdot>as \<times> sValues\<cdot>bs)) \<union> {Eps}"  
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union, blast)
  apply (rule_tac x = bs in scases, simp_all)
  apply (simp add: tsynzip_sconc_msg, blast)
  by (metis (no_types) insert_absorb2 insert_is_Un insert_mono sValues2un tsynZip.simps(2) tsynzip_sconc_Eps)

text \<open>@{term tsynValues} of @{term tsynZip} is subset of the Cartesian product of @{term tsynValues} 
        of the first stream and @{term sValues} of the second stream.\<close>
lemma tsynzip_tsyndom: "tsynValues\<cdot>(tsynZip\<cdot>as\<cdot>bs) \<subseteq> (tsynValues\<cdot>as \<times> sValues\<cdot>bs)"
  by (simp add: szip_sValues tsynabs_tsyndom tsynzip_tsynabs)

text \<open>@{term tsynZip} test on finite streams.\<close>
lemma tsynzip_test_finstream: 
  "tsynZip\<cdot>(<[TSynMsg 1, Eps, TSynMsg 2, TSynMsg 3, Eps]>)\<cdot>(<[4, 2, 3]>) 
     = <[TSynMsg (1,4), Eps, TSynMsg (2,2), TSynMsg (3,3)]>"
  apply (simp add: tsynzip_sconc_msg tsynzip_sconc_Eps)
  by (metis lscons_conv sup'_def tsynZip.simps(2) tsynzip_sconc_msg)

text \<open>@{term tsynZip} test on infinite streams.\<close>
lemma tsynzip_test_infstream: 
  "tsynZip\<cdot>(<[TSynMsg 1, Eps]>\<^sup>\<infinity>)\<cdot>(\<up>2\<^sup>\<infinity>) = <[TSynMsg (1,2),Eps]>\<^sup>\<infinity>"
  apply (subst rek2sinftimes [of "tsynZip\<cdot>(<[TSynMsg 1, Eps]>\<^sup>\<infinity>)\<cdot>(\<up>2\<^sup>\<infinity>)" "<[TSynMsg (1,2), Eps]>"])
  apply (simp_all)
  apply (subst sinftimes_unfold, simp)
  apply (subst sinftimes_unfold [of "\<up>2"])
  by (simp add: tsynzip_sconc_msg tsynzip_sconc_Eps)

lemma tsynzip_Eps_singeltons: "tsynZip\<cdot>(\<up>\<sim>)\<cdot>(\<up>y) = \<up>\<sim>"
  by (metis sup_conc_eps2 sup_noteps tsynZip.simps(1) tsynzip_sconc_Eps)


lemma tsynzip_Eps_sconc: "tsynZip\<cdot>(\<up>\<sim>)\<cdot>(\<up>y \<Zcat> ys) = \<up>\<sim>"
  by (metis sconc_snd_empty supconc_neps2 tsynZip.simps(1) tsynzip_sconc_Eps)


lemma tsynzip_msg_singeltons: "tsynZip\<cdot>(\<up>(TSynMsg x))\<cdot>(\<up>y) = \<up>(TSynMsg (x, y))"
  by (metis sconc_snd_empty tsynZip.simps(2) tsynzip_sconc_msg)

lemma tsynzip_tsynabs_image: "((TSynMsg ` A) \<ominus> tsynZip\<cdot>as\<cdot>bs)\<^sup>-
                               = A \<ominus> szip\<cdot>(as\<^sup>-)\<cdot>bs"
  apply (induction as arbitrary: bs rule: tsyn_ind)
  apply simp_all
  apply (rename_tac x y z)
  apply (rule_tac x = z in scases, simp_all)
   apply (simp add: tsynzip_sconc_msg)
   apply (case_tac "(x, a)\<in>A")
    apply (simp_all add: image_def)
  apply (rename_tac x y)
  apply (case_tac "y = \<epsilon>")
  by (simp_all add: tsynzip_sconc_Eps)

lemma tsynzip_tsynabs2: "({TSynMsg (d, b)|d. True} \<ominus> tsynZip\<cdot>as\<cdot>bs)\<^sup>-
                               = {(d, b)|d. True} \<ominus> szip\<cdot>(as\<^sup>-)\<cdot>bs"
  apply (induction as arbitrary: bs rule: tsyn_ind)
  apply simp_all
  apply (rename_tac x y z)
  apply (rule_tac x = z in scases, simp_all)
   apply (simp add: tsynzip_sconc_msg)
   apply (case_tac "a=b")
    apply (simp_all)
  apply (rename_tac x y)
  apply (case_tac "y = \<epsilon>")
  by (simp_all add: tsynzip_sconc_Eps)

lemma tsynzip_const_msg_streams: "tsynZip\<cdot>((\<up>(TSynMsg a))\<^sup>\<infinity>)\<cdot>((\<up>False)\<^sup>\<infinity>) =((\<up>(TSynMsg (a,False)))\<^sup>\<infinity>) "
using sinftimes_unfold s2sinftimes tsynzip_sconc_msg
  by (metis (no_types, lifting))

lemma tsynfilter_fitandzip_infFalse: "\<Pi>\<^sub>1\<^sub>-({(d, True)|d. True} \<ominus>\<^sub>- tsynZip\<cdot>((\<up>x)\<^sup>\<infinity>)\<cdot>((\<up>False)\<^sup>\<infinity>)) = ((\<up>\<sim>)\<^sup>\<infinity>)"
  apply (cases x)
  using sinftimes_unfold  
  apply (metis (no_types, lifting) s2sinftimes sinf_notEps sup_noteps tsynfilter_sconc_Eps tsynzip_sconc_Eps
        tsynprojfst_sconc tsynprojfst_singleton_Eps)
  apply (simp add: tsynzip_const_msg_streams)     
proof -
  fix m :: 'a
  have "(m, False) \<notin> {p. \<exists>a. p = (a, True)}"
    by auto
  then show "\<Pi>\<^sub>1\<^sub>-({p. \<exists>a. p = (a, True)} \<ominus>\<^sub>- ((\<up>(TSynMsg (m, False)))\<^sup>\<infinity>)) = ((\<up>\<sim>)\<^sup>\<infinity>)"
    by (metis (lifting) s2sinftimes sinftimes_unfold tsynfilter_sconc_msg_nin tsynprojfst_sconc_Eps)
qed

lemma tsyndom_tsynzip_fst:
  "(u,v) \<in> tsynValues\<cdot>(tsynZip\<cdot>x\<cdot>y) \<Longrightarrow> u \<in> tsynValues\<cdot>x"
  using tsynzip_tsyndom 
  by blast

lemma tsyndom_tsynfilter_tsynzip_in:
  "a \<in> tsynValues\<cdot>(\<Pi>\<^sub>1\<^sub>-(A \<ominus>\<^sub>-tsynZip\<cdot>x\<cdot>y)) \<longrightarrow> a \<in> tsynValues\<cdot>x"
proof
  assume lhs: "a \<in> tsynValues\<cdot>(\<Pi>\<^sub>1\<^sub>-(A \<ominus>\<^sub>- tsynZip\<cdot>x\<cdot>y))"
  then obtain b where
    "(a,b) \<in> tsynValues\<cdot>(A \<ominus>\<^sub>-tsynZip\<cdot>x\<cdot>y)"
    by (metis (mono_tags, lifting) image_iff surjective_pairing tsynprojfst_tsyndom)
  hence "(a,b) \<in> tsynValues\<cdot>(tsynZip\<cdot>x\<cdot>y)"
    by simp
  thus "a \<in> tsynValues\<cdot>x"
    by (rule tsyndom_tsynzip_fst)
qed

lemma tsynZip_nonempty_insert: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> (tsynZip\<cdot>z\<cdot>s) = (
  if (shd z) = Eps then \<up>Eps \<Zcat> tsynZip\<cdot>(srt\<cdot>z)\<cdot>s
  else \<up>(TSynMsg ((invMsg (shd z)), (shd s))) \<Zcat> tsynZip\<cdot>(srt\<cdot>z)\<cdot>(srt\<cdot>s) 
)"
  apply(auto)
  apply (metis TsynStream.tsynZip.simps(1,2) surj_scons  tsynzip_sconc_Eps)
  by (metis TsynStream.tsynZip.simps(1,2) surj_scons tsynzip_sconc_msg)

lemma tsynZip_nonempty_shd: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> shd (tsynZip\<cdot>z\<cdot>s) = (
  if (shd z) = Eps then Eps
  else TSynMsg ((invMsg (shd z)), (shd s))
)"
  by (metis shd1 tsynZip_nonempty_insert)

lemma tsynZip_nonempty_srt: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> srt\<cdot>(tsynZip\<cdot>z\<cdot>s) \<in> {tsynZip\<cdot>(srt\<cdot>z)\<cdot>s, tsynZip\<cdot>(srt\<cdot>z)\<cdot>(srt\<cdot>s)}"
  apply(subst tsynZip_nonempty_insert)
  by auto

lemma tsynZip_nonempty_shd_not_eps: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> shd (tsynZip\<cdot>z\<cdot>s) \<noteq> \<sim> \<Longrightarrow> shd z \<noteq> \<sim>"
  apply(simp add: tsynZip_nonempty_shd)
  by (metis not_Eps_eq)

lemma tsynZip_sdrop_inf: "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity> \<Longrightarrow> \<exists>j \<le> i. sdrop i\<cdot>(tsynZip\<cdot>z\<cdot>s) = tsynZip\<cdot>(sdrop i\<cdot>z)\<cdot>(sdrop j\<cdot>s)"
  apply(induction i, simp_all)
  apply(simp add: sdrop_def)
proof -
  fix ia :: nat
  assume a1: "\<exists>j\<le>ia. iterate ia\<cdot>srt\<cdot>(tsynZip\<cdot>z\<cdot>s) = tsynZip\<cdot>(iterate ia\<cdot>srt\<cdot>z)\<cdot> (iterate j\<cdot>srt\<cdot>s)"
  assume "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity>"
  then have "\<infinity> = #(tsynZip\<cdot>z\<cdot>s)"
    by (metis (no_types) antisym inf_ub tsynlen_slen)
  then show "\<exists>n\<le>Suc ia. srt\<cdot>(iterate ia\<cdot>srt\<cdot>(tsynZip\<cdot>z\<cdot>s)) = tsynZip\<cdot>(srt\<cdot>(iterate ia\<cdot>srt\<cdot>z))\<cdot> (iterate n\<cdot>srt\<cdot>s)"
    using a1 by (metis (no_types) Inf'_neq_0 Suc_leD Suc_le_mono emptyE fair_sdrop insertE only_empty_has_length_0 sdrop_back_rt sdrop_def tsynZip_nonempty_srt)
qed

lemma tsynZip_sfilter_snth: "#\<^sub>-(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) = \<infinity> \<Longrightarrow> x = TSynMsg (xa, y) \<Longrightarrow> snth i (tsynZip\<cdot>z\<cdot>(A \<ominus> s)) = TSynMsg (xa, y) \<Longrightarrow> y \<in> A"
  apply(case_tac "x")
   apply auto
  apply(subgoal_tac "tsynZip\<cdot>z\<cdot>(A \<ominus> s) \<noteq> \<epsilon>")
   defer
  using tsynlen_inf_nbot apply blast
  apply(subgoal_tac "\<exists>j \<le> i. sdrop i\<cdot>(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) = tsynZip\<cdot>(sdrop i\<cdot>z)\<cdot>(sdrop j\<cdot>(A \<ominus> s))")
   defer
  using tsynZip_sdrop_inf apply blast
  apply(simp add: snth_def)
  by (smt Int_iff Product_Type.prod.simps(1) TSynDatatype.inverseMsg.simps(2) TSynDatatype.tsyn.simps(3) TsynStream.tsynZip.simps(2) drop_not_all fin_le_inf inf_less_eq
      rek2sinftimes sValues_sfilter sconc_snd_empty sdrop_back_rt sdrop_sValues sfilter_nin sfilter_sValuesl3 sfilter_sinftimes_nin supconc_neps surj_scons tsynZip_nonempty_shd
      tsynlen_slen)

lemma tsynZip_sfilter_sValues: "#\<^sub>-(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) = \<infinity> \<Longrightarrow> sValues\<cdot>(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) \<subseteq> {x. x = Eps \<or> inv TSynMsg x \<in> {(x, y). y \<in> A}}"
  apply(simp add: sValues_def)
  apply(subst beta_cfun, rule sValues_cont)
  apply(simp add: tsynEps_tsynEps2slen_infinite_msg)
  apply auto
  by (simp add: tsynZip_sfilter_snth)

lemma tsynZip_helper_todo: "#\<^sub>-(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) =  #({x . x \<noteq> \<sim> } \<ominus> tsynZip\<cdot>z\<cdot>(A \<ominus> s))"
  apply(simp only: tsynlen_insert)
  by (simp add: tsynabs_insert)



lemma tsynZip_eps_impl_cp: "s \<noteq> \<epsilon> \<Longrightarrow> z \<noteq> \<epsilon> \<Longrightarrow> tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon>"
proof -
  assume sne: "s \<noteq> \<epsilon>"
    and zne: "z \<noteq> \<epsilon>"
  obtain a as b bs where
    zeq: "z = up\<cdot>a && as"
and seq: "s = up\<cdot>b && bs"
    by (metis scases' sne upE zne)

  have alteq: "tsynZip\<cdot>z\<cdot>s = tsynZip\<cdot>(up\<cdot>a && as)\<cdot>(up\<cdot>b && bs)"
    by(simp only: seq zeq)
  show ?thesis
    by(simp add: alteq tsynZip.simps(3))
qed

lemma tsynZip_eps_impl: "tsynZip\<cdot>z\<cdot>s = \<epsilon> \<Longrightarrow> z = \<epsilon> \<or> s = \<epsilon>"
  using tsynZip_eps_impl_cp by blast

lemma tsynZip_snth_not_eps:
  assumes "#s = \<infinity>"
  and "snth j z \<noteq> Eps"
  and "#\<^sub>-z = \<infinity>"
shows "snth j (tsynZip\<cdot>z\<cdot>s) \<noteq> Eps"
  apply(subgoal_tac "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity>")
  defer
   apply (simp add: assms(1,3) tsynzip_tsynlen)
  apply(simp add: snth_def)
  apply(insert tsynZip_sdrop_inf[of z s j])
  apply auto
  by (metis assms(2) snth_def tsynZip_nonempty_shd tsynlen_inf_drop_ne)

lemma  tsynZip_until_first_msg_only_eps:
  assumes "#s = \<infinity>"
  and "#\<^sub>-z = \<infinity>"
  and "k = (LEAST k. snth k z \<noteq> Eps)"
shows "i < k \<Longrightarrow> snth i (tsynZip\<cdot>z\<cdot>s) = Eps"
proof(induction i)
  case 0
  assume kg0: "0 < k"
  have zip_tslen_inf: "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity>"
    by (simp add: assms(1,2) tsynzip_tsynlen)

  have neps: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon>"
    using zip_tslen_inf by force

  show ?case
    apply(simp add: tsynZip_nonempty_insert[OF neps])
    apply(subst snth_shd[symmetric])
    using assms(3) kg0 not_less_Least by blast
next
  case (Suc i)
  assume kgsi: "Suc i < k"

  have zip_tslen_inf: "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity>"
    by (simp add: assms(1,2) tsynzip_tsynlen)

  show ?case
    by (metis no_msg_before_least[OF assms(3)] kgsi snth_def tsynZip_nonempty_shd tsynZip_sdrop_inf tsynlen_inf_drop_ne zip_tslen_inf)
qed

lemma  tsynZip_until_first_msg_no_consumption:
  assumes "#s = \<infinity>"
  and "#\<^sub>-z = \<infinity>"
  and "k = (LEAST k. snth k z \<noteq> Eps)"
shows "i \<le> k \<Longrightarrow> sdrop i\<cdot>(tsynZip\<cdot>z\<cdot>s) = tsynZip\<cdot>(sdrop i\<cdot>z)\<cdot>s"
  apply(induction i)
   apply(simp add: assms)+
  apply(subst tsynZip_nonempty_insert)
   apply (simp add: assms(1,2) tsynlen_inf_nbot tsynzip_tsynlen)
  apply(insert no_msg_before_least[OF assms(3)])
  by (smt Suc_le_eq TSynDatatype.tsyn.exhaust assms(1,2,3) not_less_Least sdrop_back_rt snth_def srt_supconc tsynZip_nonempty_insert tsynlen_inf_drop_ne
      tsynlen_inf_nbot tsynzip_tsynlen)


lemma
  tsynZip_snth_eps:
  assumes "#s = \<infinity>"
  and "snth j z = Eps"
  and "#\<^sub>-z = \<infinity>"
shows "snth j (tsynZip\<cdot>z\<cdot>s) = Eps"
  apply(subgoal_tac "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity>")
  defer
   apply (simp add: assms(1,3) tsynzip_tsynlen)
  apply(simp add: snth_def)
  apply(insert tsynZip_sdrop_inf[of z s j])
  apply auto
  by (metis assms(2) snth_def tsynZip_nonempty_shd tsynlen_inf_drop_ne)


lemma tsynzip_sconc_Eps_end:
  assumes "#xs < \<infinity>"
    and "#\<^sub>-xs < #ys"
  shows "tsynZip\<cdot>(xs \<Zcat> \<up>Eps)\<cdot>ys = tsynZip\<cdot>xs\<cdot>ys \<Zcat> \<up>Eps"
  using assms apply (induction xs arbitrary: ys rule: tsyn_finind, simp_all)
  using tsynzip_singleton_Eps_first apply force
   apply(case_tac ysa, auto)
    apply (metis bot_is_0 lnat_le_zero)
  apply (metis (no_types, lifting) assoc_sconc fold_inf lnsuc_le tsynlen_sconc_msg tsynzip_sconc_msg)
  apply (simp add: order_less_le tsynzip_sconc_Eps)
  apply(case_tac ysa, auto)
  by (simp add: tsynlen_sconc_Eps tsynzip_sconc_Eps)


lemma tsyndom_tsynboolfilter_in: "a \<in>  tsynValues\<cdot>(tsynBoolFilter\<cdot>y\<cdot>ora) \<longrightarrow>  a \<in> tsynValues\<cdot>y "
  apply (simp add: tsynBoolFilter_def) 
  using tsyndom_tsynfilter_tsynzip_in by auto

lemma strict_tsynboolfilter_fst: "tsynBoolFilter\<cdot>\<epsilon>\<cdot>s = \<epsilon>"
  by (simp add: tsynBoolFilter_def)

lemma strict_tsynboolfilter_snd: "tsynBoolFilter\<cdot>s\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynBoolFilter_def)

lemma tsynboolfilter_cont: "cont (\<lambda> s. tsynBoolFilter\<cdot>s\<cdot>ora)" 
  by (simp add: tsynBoolFilter_def)

lemma tsynboolfilter_single_true: "tsynBoolFilter\<cdot>(\<up>a)\<cdot>(\<up>True) = \<up>a"
  apply (simp add: tsynBoolFilter_def)
  apply(cases a, simp_all add: tsynzip_msg_singeltons tsynzip_Eps_singeltons)
   apply (simp add: tsynfilter_singleton_Eps tsynprojfst_singleton_Eps)
  by (simp add: tsynfilter_singleton_msg_in tsynprojfst_singleton_msg)

lemma tsynboolfilter_single_false: "tsynBoolFilter\<cdot>(\<up>a)\<cdot>(\<up>False) = \<up>\<sim>"
  apply (simp add: tsynBoolFilter_def)
  apply(cases a, simp_all add: tsynzip_msg_singeltons tsynzip_Eps_singeltons)
   apply (simp add: tsynfilter_singleton_Eps tsynprojfst_singleton_Eps)
  by (simp add: tsynfilter_singleton_msg_nin tsynprojfst_singleton_Eps)

lemma tsynboolfilter_Eps_any: "tsynBoolFilter\<cdot>(\<up>\<sim>)\<cdot>(\<up>b) = \<up>\<sim>"
  by (simp add: tsynBoolFilter_def tsynzip_Eps_singeltons tsynfilter_singleton_Eps
        tsynprojfst_singleton_Eps)

lemma tsynboolfilter_Eps_sup: "tsynBoolFilter\<cdot>(\<up>\<sim>)\<cdot>(\<up>b \<Zcat> bs) = \<up>\<sim>"
  by (simp add: tsynBoolFilter_def tsynzip_Eps_sconc tsynfilter_singleton_Eps
        tsynprojfst_singleton_Eps)

lemma tsynboolfilter_Eps_infinite: "#s = \<infinity> \<longrightarrow> tsynBoolFilter\<cdot>(\<up>\<sim>)\<cdot>s = \<up>\<sim>"
  apply (cases s) 
  by (simp_all add: tsynboolfilter_Eps_sup)

lemma tsynboolfilter_Eps_up_and_infinite: "#s = \<infinity> \<longrightarrow> tsynBoolFilter\<cdot>(\<up>\<sim>)\<cdot>(up\<cdot>x && s) = \<up>\<sim>"
  by (metis discr.exhaust tsynboolfilter_Eps_sup lscons_conv)

lemma tsynboolfilter_Eps_sconc_infinite: "#s = \<infinity> \<longrightarrow> tsynBoolFilter\<cdot>(\<up>\<sim>)\<cdot>(\<up>x \<Zcat> s) = \<up>\<sim>"
  by (simp_all add: tsynboolfilter_Eps_sup)

lemma tsynboolfilter_Eps_lscons_infinite: "#s = \<infinity>  \<longrightarrow> x \<noteq> \<bottom> \<longrightarrow> tsynBoolFilter\<cdot>(\<up>\<sim>)\<cdot>(x && s) =  \<up>\<sim>"
  apply (cases x)
  apply (simp add: tsynBoolFilter_def)
  by (simp add: tsynboolfilter_Eps_up_and_infinite) 

lemma tsynboolfilter_Eps_lscons_bot: "#s = \<infinity>  \<longrightarrow> tsynBoolFilter\<cdot>(\<up>\<sim>)\<cdot>(\<bottom> && s) =  \<epsilon>"
  by (simp add: tsynBoolFilter_def)

lemma tsynboolfilter_msg_sup_true: "tsynBoolFilter\<cdot>(\<up>(TSynMsg a))\<cdot>(\<up>True \<Zcat> bs) =  \<up>(TSynMsg a)"
  apply (simp add: tsynBoolFilter_def tsynzip_singleton_msg_first tsynfilter_singleton_msg_in)
  by (simp add: tsynprojfst_singleton_Eps tsynprojfst_singleton_msg)

lemma tsynboolfilter_msg_sup_false: "tsynBoolFilter\<cdot>(\<up>(TSynMsg a))\<cdot>(\<up>False \<Zcat> bs) =  \<up>\<sim>"
  apply (simp add: tsynBoolFilter_def tsynzip_singleton_msg_first  tsynfilter_singleton_msg_nin)
  by (simp add: tsynprojfst_singleton_Eps tsynprojfst_singleton_msg)

lemma tsynboolfilter_msg_stream_true: "bs\<noteq>\<epsilon> \<Longrightarrow> shd bs \<Longrightarrow> tsynBoolFilter\<cdot>(\<up>(TSynMsg a))\<cdot>bs = \<up>(TSynMsg a)" 
  apply (cases bs)
  apply (simp add: tsynBoolFilter_def)
  by (simp add: tsynboolfilter_msg_sup_false tsynboolfilter_msg_sup_true)

lemma tsynboolfilter_msg_stream_false: "bs\<noteq>\<epsilon> \<Longrightarrow> \<not>shd bs \<Longrightarrow> tsynBoolFilter\<cdot>(\<up>(TSynMsg a))\<cdot>bs = \<up>\<sim>" 
  apply (cases bs)
  apply (simp add: tsynBoolFilter_def)
  by (simp add: tsynboolfilter_msg_sup_false tsynboolfilter_msg_sup_true)

lemma tsynboolfilter_msg_up_sup_true: " (undiscr b) \<Longrightarrow> tsynBoolFilter\<cdot>(\<up>(TSynMsg a))\<cdot>(up\<cdot>b && bs) =  \<up>(TSynMsg a)"
  by (metis(full_types) Discr_undiscr lscons_conv tsynboolfilter_msg_sup_true)

lemma tsynboolfilter_msg_up_sup_false: "\<not>(undiscr b) \<Longrightarrow> tsynBoolFilter\<cdot>(\<up>(TSynMsg a))\<cdot>(up\<cdot>b && bs) = \<up>\<sim>"
  by (metis(full_types) Discr_undiscr lscons_conv tsynboolfilter_msg_sup_false)

lemma tsynboolfilter_msg_updis_sup_true: "b \<Longrightarrow> tsynBoolFilter\<cdot>(\<up>(TSynMsg a))\<cdot>(updis b && bs) = \<up>(TSynMsg a)"
  by (simp add: lscons_conv tsynboolfilter_msg_stream_true)

lemma tsynboolfilter_msg_updis_sup_false: "\<not>b \<Longrightarrow> tsynBoolFilter\<cdot>(\<up>(TSynMsg a))\<cdot>(updis b && bs) = \<up>\<sim>"
  by (simp add: lscons_conv tsynboolfilter_msg_stream_false)

lemma tsynboolfilter_msg_sup_lscons: "tsynBoolFilter\<cdot>(\<up>(TSynMsg a))\<cdot>(b && bs) = 
                      (if b = \<bottom> then \<epsilon> else (if undiscr (inv Iup b) then \<up>(TSynMsg a) else \<up>\<sim>))"
  apply (cases b)
   apply (simp add: tsynBoolFilter_def)
  by (simp add: tsynboolfilter_msg_up_sup_false tsynboolfilter_msg_up_sup_true)

lemma tsynboolfilter_msg_true_rec: "tsynBoolFilter\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(\<up>True \<Zcat> bs) = \<up>(TSynMsg a) \<Zcat> tsynBoolFilter\<cdot>as\<cdot>bs"
  by (simp add: tsynBoolFilter_def tsynzip_sconc_msg tsynfilter_sconc_msg_in tsynprojfst_sconc_msg)

lemma tsynboolfilter_msg_false_rec: "tsynBoolFilter\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(\<up>False \<Zcat> bs) = \<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>as\<cdot>bs"
  by (simp add: tsynBoolFilter_def tsynzip_sconc_msg tsynfilter_sconc_msg_nin tsynprojfst_sconc_Eps)

lemma tsynboolfilter_Eps_bool_rec: "tsynBoolFilter\<cdot>(\<up>\<sim> \<Zcat> as)\<cdot>(\<up>b \<Zcat> bs) = \<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>as\<cdot>(\<up>b \<Zcat> bs)"
  by (simp add: tsynBoolFilter_def tsynzip_sconc_Eps tsynfilter_sconc_Eps tsynprojfst_sconc_Eps)

lemma tsynboolfilter_msg_updis_rec: "tsynBoolFilter\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(updis True && bs) = 
 \<up>(TSynMsg a) \<Zcat> tsynBoolFilter\<cdot>as\<cdot>bs"
  apply (simp add: lscons_conv tsynBoolFilter_def) 
  by (simp add: tsynfilter_sconc_msg_in tsynzip_sconc_msg tsynprojfst_sconc_msg)

lemma tsynboolfilter_Eps_updis_true_rec: "tsynBoolFilter\<cdot>(\<up>\<sim> \<Zcat> as)\<cdot>(updis b && bs) = 
         \<up>\<sim>  \<Zcat> tsynBoolFilter\<cdot>as\<cdot>(updis b && bs)"
  apply (simp add: lscons_conv tsynBoolFilter_def)
  by (simp add: tsynzip_sconc_Eps tsynfilter_sconc_Eps tsynprojfst_sconc_Eps)

lemma tsynboolfilter_msg_updis_false_rec: "tsynBoolFilter\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(updis False && bs) = \<up>\<sim>  \<Zcat> tsynBoolFilter\<cdot>as\<cdot>bs"
  apply (simp add: lscons_conv tsynBoolFilter_def)
  by (simp add: tsynfilter_sconc_msg_nin tsynzip_sconc_msg tsynprojfst_sconc_Eps)


lemma tsynboolfilter_inf_true: "tsynBoolFilter\<cdot>s\<cdot>((\<up>True)\<^sup>\<infinity>) = s"
 apply (induction s)
  apply auto
  apply (simp add: tsynBoolFilter_def)
  using sinftimes_unfold tsynboolfilter_msg_true_rec tsynboolfilter_Eps_bool_rec tsynboolfilter_msg_false_rec
  by (metis tsyn2ustreamElem.cases)

lemmas tsynboolfilter_lemmas =
  strict_tsynboolfilter_fst strict_tsynboolfilter_snd tsynboolfilter_single_true tsynboolfilter_single_false
  tsynboolfilter_Eps_any tsynboolfilter_Eps_sup tsynboolfilter_Eps_infinite tsynboolfilter_Eps_up_and_infinite
  tsynboolfilter_Eps_up_and_infinite tsynboolfilter_Eps_sconc_infinite 
  tsynboolfilter_msg_sup_true tsynboolfilter_msg_sup_false
 tsynboolfilter_msg_stream_true tsynboolfilter_msg_stream_false tsynboolfilter_msg_up_sup_true
 tsynboolfilter_msg_up_sup_false tsynboolfilter_msg_updis_sup_true tsynboolfilter_msg_updis_sup_false
  tsynboolfilter_msg_sup_lscons  tsynboolfilter_msg_true_rec 
  tsynboolfilter_msg_false_rec tsynboolfilter_msg_updis_rec tsynboolfilter_Eps_updis_true_rec
  tsynboolfilter_Eps_bool_rec  tsynboolfilter_msg_updis_false_rec
  tsynboolfilter_inf_true tsynboolfilter_Eps_lscons_bot

lemma tsynboolfilter_inf_false_rec: "tsynBoolFilter\<cdot>(\<up>a \<Zcat> s)\<cdot>((\<up>False)\<^sup>\<infinity>) = \<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>s\<cdot>((\<up>False)\<^sup>\<infinity>)"
  apply (subst sinftimes_unfold) 
  apply (cases a; simp add: tsynboolfilter_lemmas)
  by (metis sinftimes_unfold)

lemma tsynboolfilter_inf_const_false: "tsynBoolFilter\<cdot>((\<up>a)\<^sup>\<infinity>)\<cdot>((\<up>False)\<^sup>\<infinity>) = ((\<up>\<sim>)\<^sup>\<infinity>)"
  by (metis tsynboolfilter_inf_false_rec s2sinftimes sinftimes_unfold) 

lemma slen_tsynboolfilter: "#ys = \<infinity> \<longrightarrow> #(tsynBoolFilter\<cdot>xs\<cdot>ys) = #xs"
  apply(simp add: tsynBoolFilter_def)   
  by (metis (no_types, lifting) tsynzip_slen tsynfilter_slen tsynprojfst_slen)

lemma tsynlen_boolfilter: "#\<^sub>-y \<ge> #\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora)"
  apply(simp add: tsynBoolFilter_def)
  by (metis (no_types, lifting) dual_order.trans linorder_linear tsynfilter_tsynlen tsynlen_insert tsynlen_tsynproj1_tsynproj2 tsynprojfst_tsynlen tsynzip_tsynprojfst_tsynabs
      tsynzip_tsynprojsnd_tsynabs)

lemma tsynboolfilter_tsynabs: "(tsynBoolFilter\<cdot>y\<cdot>ora)\<^sup>- =  sboolfilter\<cdot>(y\<^sup>-)\<cdot>ora"
  by (simp add: sboolfilter_def tsynBoolFilter_def tsynzip_tsynabs tsynfilter_tsynabs tsynprojfst_tsynabs )

lemma tsynboolfilter_len_eq_imp_eq: "#ora = \<infinity> \<Longrightarrow> #\<^sub>-x = #\<^sub>-(tsynBoolFilter\<cdot>x\<cdot>ora) \<Longrightarrow> #\<^sub>-x = Fin k 
    \<Longrightarrow> x\<^sup>- = (tsynBoolFilter\<cdot>x\<cdot>ora)\<^sup>-"
  by (metis sboolfilter_len_eq_imp_eq tsynboolfilter_tsynabs tsynlen_insert)

lemma tsynboolfilter_msg_ineq: "\<forall> xs. tsynBoolFilter\<cdot>(\<up>(TSynMsg a)\<Zcat> as)\<cdot>(\<up>False \<Zcat> bs) 
                                \<noteq> tsynBoolFilter\<cdot>(\<up>(TSynMsg a)\<Zcat> as)\<cdot>(\<up>True \<Zcat> xs) "
  apply (simp add: tsynboolfilter_lemmas)
  using inject_scons by blast

lemma tsynboolfilter_shd_inj: "tsynBoolFilter\<cdot>(\<up>(TSynMsg a)\<Zcat> as)\<cdot>(\<up>b \<Zcat> bs) =  tsynBoolFilter\<cdot>(\<up>(TSynMsg a)\<Zcat> as)\<cdot>ora
  \<Longrightarrow> ora = \<up>b \<Zcat> srt\<cdot>ora  "
  apply (cases b; cases "shd ora"; simp add: tsynboolfilter_lemmas)
  apply (metis (full_types) strict_tsynboolfilter_snd supconc_neps2 surj_scons) 
  apply (metis (full_types) strict_tsynboolfilter_snd supconc_neps2 surj_scons tsynboolfilter_msg_ineq
      tsynboolfilter_msg_true_rec) 
  apply (metis (full_types) strict_tsynboolfilter_snd supconc_neps2 surj_scons tsynboolfilter_msg_false_rec
      tsynboolfilter_msg_ineq) 
  by (metis (full_types) strict_tsynboolfilter_snd supconc_neps2 surj_scons)

lemma tsynboolfilter_refold: "(\<up>(TSynMsg m) \<Zcat> (tsynBoolFilter\<cdot>s\<cdot>ora)) 
= (tsynBoolFilter\<cdot>(\<up>(TSynMsg m) \<Zcat>s)\<cdot>((\<up>True) \<Zcat>ora))"
  by (simp add: tsynboolfilter_msg_true_rec)

lemma tsynboolfilter_tsynprojsnd_distr:
  "\<Pi>\<^sub>2\<^sub>-(tsynBoolFilter\<cdot>s\<cdot>ora) = (tsynBoolFilter\<cdot>(\<Pi>\<^sub>2\<^sub>-s)\<cdot>ora)"
  apply (induct s arbitrary: ora rule: tsyn_ind, simp_all add: tsynboolfilter_lemmas)
  apply (case_tac m)
  apply (case_tac ora, simp_all add: tsynprojsnd_sconc_msg tsynprojsnd_sconc_Eps tsynboolfilter_lemmas)
  apply (rename_tac or os)
  apply (case_tac or, simp_all add: tsynprojsnd_sconc_msg tsynprojsnd_sconc_Eps tsynboolfilter_lemmas)
  by (case_tac ora, simp_all add: tsynboolfilter_lemmas tsynprojsnd_sconc_Eps)

lemma tsynboolfilter_live[simp]:
  "#\<^sub>-i = \<infinity> \<longrightarrow> (#\<^sub>-(tsynBoolFilter\<cdot>i\<cdot>ora) = #({True} \<ominus> ora))"
proof
  assume inf_i: "#\<^sub>-i = \<infinity>"
  have inf_u_i: "#(i\<^sup>-) = \<infinity> " 
    using inf_i by (simp add: tsynlen_insert)

  have a1: "#\<^sub>-(tsynBoolFilter\<cdot>i\<cdot>ora)
            = #\<^sub>-(\<Pi>\<^sub>1\<^sub>-({d. snd d} \<ominus>\<^sub>- tsynZip\<cdot>i\<cdot>ora))"
    by (simp add: tsynBoolFilter_def)
  have a2: "... = #(({(d, True)|d. True} \<ominus>\<^sub>- tsynZip\<cdot>i\<cdot>ora))\<^sup>-"
    apply (simp add: slen_sprojfst tsynprojfst_tsynabs tsynlen_insert)
    by (metis (mono_tags, opaque_lifting) prod.collapse prod.inject)
  have a3: "... = #(({TSynMsg (d, True)|d. True} \<ominus> tsynZip\<cdot>i\<cdot>ora)\<^sup>-)" 
    by (metis (no_types, lifting) ext tsynfilter_tsynabs
              tsynzip_tsynabs tsynzip_tsynabs2  tsynlen_insert )
  have b1: "... = #({(d, True)|d. True} \<ominus> szip\<cdot>(i\<^sup>-)\<cdot>ora)"
    using tsynzip_tsynabs2 by (metis (lifting) ext)
  have b2: "... = #(sprojsnd\<cdot>({(d, True)|d. True} \<ominus> szip\<cdot>(i\<^sup>-)\<cdot>ora))"
    by (simp add: slen_sprojsnd)
  have b3: "... = #(sprojsnd\<cdot>({d. snd d} \<ominus> szip\<cdot>(i\<^sup>-)\<cdot>ora))"
    by (metis (mono_tags, opaque_lifting) prod.collapse prod.inject)
  have b4: "... = #({True} \<ominus> ora)"
        using inf_u_i sboolfilter_liveness_helper by fastforce
  from a1 a2 a3 b1 b2 b3 b4
  show "#\<^sub>-(tsynBoolFilter\<cdot>i\<cdot>ora) = #({True} \<ominus> ora)" by simp
qed

lemma tsynboolfilter_strict [simp]:
  "tsynBoolFilter\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
  "tsynBoolFilter\<cdot>y\<cdot>\<bottom> = \<bottom>"
  "tsynBoolFilter\<cdot>\<bottom>\<cdot>ora = \<bottom>"
  by (simp add: strict_tsynboolfilter_fst strict_tsynboolfilter_snd)+

lemma tsynboolfilter_nonempty [simp]:
  assumes "y\<noteq>\<bottom>"
    and "#ora=\<infinity>"
  shows "tsynBoolFilter\<cdot>y\<cdot>ora \<noteq> \<bottom>"
  using assms apply (cases y; cases ora; simp)
  by (case_tac a; case_tac aa; simp add: tsynboolfilter_lemmas)

lemma tsynboolfilter_inf_Eps [simp]:
  assumes "#ora=\<infinity>"
  shows "tsynBoolFilter\<cdot>((\<up>\<sim>)\<^sup>\<infinity>)\<cdot>ora = ((\<up>\<sim>)\<^sup>\<infinity>)"
  using assms 
  by (metis inf_scase s2sinftimes sinftimes_unfold tsynboolfilter_Eps_bool_rec)

lemma tsynboolfilter_live_inf [simp]:
  assumes "#({True} \<ominus> ora) = \<infinity>"
      and "#(i\<^sup>-) = \<infinity>"
  shows "#(tsynBoolFilter\<cdot>i\<cdot>ora)\<^sup>- = \<infinity>"
  using assms 
  by (metis tsynboolfilter_live tsynlen_insert)

lemma tsynfilterelem_image_seq: "tsynFilterElem A ` B \<subseteq> B \<union> {\<sim>}"
  apply(auto simp add: image_def)
  apply(case_tac xa, simp_all)
  by(case_tac "a \<in> A", simp_all)

lemma tsynboolfilter_subset: "sValues\<cdot>(tsynBoolFilter\<cdot>s\<cdot>ora) \<subseteq> sValues\<cdot>s \<union> {\<sim>}"
  apply(simp add: tsynBoolFilter_def)
  apply(simp add: tsynprojfst_sValues tsynfilter_insert smap_sValues)
proof-
  have "sValues\<cdot>(tsynZip\<cdot>s\<cdot>ora) \<subseteq> TSynMsg ` (tsynValues\<cdot>s \<times> sValues\<cdot>ora) \<union> {\<sim>}"
    by (rule tsynzip_sValues)
  then have "tsynFilterElem (Collect snd) ` sValues\<cdot>(tsynZip\<cdot>s\<cdot>ora) \<subseteq> TSynMsg ` (tsynValues\<cdot>s \<times> sValues\<cdot>ora) \<union> {\<sim>}"
    by (meson Un_least order_trans sup_ge2 tsynfilterelem_image_seq)
  then have lhs: "tsynFst ` tsynFilterElem (Collect snd) ` sValues\<cdot>(tsynZip\<cdot>s\<cdot>ora) \<subseteq> TSynMsg ` (tsynValues\<cdot>s) \<union> {\<sim>}"
    by auto

  have rhs: "TSynMsg ` (tsynValues\<cdot>s) \<union> {\<sim>} \<subseteq> insert \<sim> (sValues\<cdot>s)"
    by(auto simp add: image_def tsyndom_insert)

  show "tsynFst ` tsynFilterElem (Collect snd) ` sValues\<cdot>(tsynZip\<cdot>s\<cdot>ora) \<subseteq> insert \<sim> (sValues\<cdot>s)"
    using lhs rhs by order
qed

lemma tsynboolfilter_tsynmap:
  assumes "#s \<le> #ora"
  shows "tsynBoolFilter\<cdot>((tsynMap f)\<cdot>s)\<cdot>ora = (tsynMap f)\<cdot>(tsynBoolFilter\<cdot>s\<cdot>ora)"
  apply(simp add: tsynBoolFilter_def)
  apply(induction s arbitrary: ora, auto)
  apply(case_tac ora, auto)
  apply(case_tac a, auto)
   apply(simp add: tsynmap_sconc_Eps tsynzip_sconc_Eps tsynfilter_sconc_Eps tsynprojfst_sconc_Eps)
  apply(simp add: tsynmap_sconc_msg tsynzip_sconc_msg)
  apply(case_tac aa, auto)
   apply(simp add: tsynfilter_sconc_msg_in tsynprojfst_sconc_msg tsynmap_sconc_msg)
  by(simp add: tsynfilter_sconc_msg_nin tsynprojfst_sconc_Eps tsynmap_sconc_Eps)

lemma smap_tsynBoolFilter:
  assumes "f Eps = Eps"
    and "\<And> m. m\<noteq>Eps \<Longrightarrow> f m \<noteq> Eps "
  shows "(smap f)\<cdot>(tsynBoolFilter\<cdot>y\<cdot>ora) = tsynBoolFilter\<cdot>((smap f)\<cdot>y)\<cdot>ora"
proof (induction y arbitrary: ora rule: tsyn_ind)
  case adm
  then show ?case by simp
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  show ?case
  proof (cases ora)
    case bottom
    then show ?thesis by simp
  next
    case (step a s')
    
    obtain m' where f_m: "f (TSynMsg m) = TSynMsg m'"
      using assms(2)[of "TSynMsg m"] by (cases "f (TSynMsg m)"; simp)
    
    show ?thesis
    proof (cases a)
      case True
      have left: "tsynBoolFilter\<cdot>(\<up>(TSynMsg m) \<Zcat> s)\<cdot>(\<up>True \<Zcat> s') = 
                      \<up>(TSynMsg m) \<Zcat> tsynBoolFilter\<cdot>s\<cdot>s'"
        using tsynboolfilter_msg_true_rec
        by blast
      
      have right: "tsynBoolFilter\<cdot>(smap f\<cdot>(\<up>(TSynMsg m) \<Zcat> s))\<cdot>(\<up>True \<Zcat> s') = 
                       \<up>(TSynMsg m') \<Zcat> tsynBoolFilter\<cdot>(smap f\<cdot>s)\<cdot>s'"
        by (simp add: f_m tsynboolfilter_msg_true_rec)
      
      show ?thesis
        using True f_m left
          local.step msg right
        by force      
    next
      case False
      have left: "tsynBoolFilter\<cdot>(\<up>(TSynMsg m) \<Zcat> s)\<cdot>(\<up>False \<Zcat> s') = 
                       \<up>Eps \<Zcat> tsynBoolFilter\<cdot>s\<cdot>s'"
        using tsynboolfilter_msg_false_rec by blast
      
      have right: "tsynBoolFilter\<cdot>(smap f\<cdot>(\<up>(TSynMsg m) \<Zcat> s))\<cdot>(\<up>False \<Zcat> s') = 
                        \<up>Eps \<Zcat> tsynBoolFilter\<cdot>(smap f\<cdot>s)\<cdot>s'"
        by (simp add: f_m tsynboolfilter_msg_false_rec)
      
      show ?thesis
        using False f_m left
          local.step msg right
        by (simp add:
            assms(1))
    qed
  qed
next
  case (Eps s)
  show ?case
  proof (cases ora)
    case bottom
    then show ?thesis by simp
  next
    case (step a s')
    have left: "tsynBoolFilter\<cdot>(\<up>Eps \<Zcat> s)\<cdot>(\<up>a \<Zcat> s') = 
                \<up>Eps \<Zcat> tsynBoolFilter\<cdot>s\<cdot>(\<up>a \<Zcat> s')"
      using tsynboolfilter_Eps_bool_rec by blast
    
    have right: "tsynBoolFilter\<cdot>(smap f\<cdot>(\<up>Eps \<Zcat> s))\<cdot>(\<up>a \<Zcat> s') = 
                 tsynBoolFilter\<cdot>(\<up>(f Eps) \<Zcat> (smap f\<cdot>s))\<cdot>(\<up>a \<Zcat> s')"      
      by simp
    
    also have "... = tsynBoolFilter\<cdot>(\<up>Eps \<Zcat> smap f\<cdot>s)\<cdot>(\<up>a \<Zcat> s')"
      using assms by simp

    also have "... = \<up>Eps \<Zcat> tsynBoolFilter\<cdot>(smap f\<cdot>s)\<cdot>(\<up>a \<Zcat> s')"
      using tsynboolfilter_Eps_bool_rec by blast
    
    finally have right_simplified: "tsynBoolFilter\<cdot>(smap f\<cdot>(\<up>Eps \<Zcat> s))\<cdot>(\<up>a \<Zcat> s') = 
                                    \<up>Eps \<Zcat> tsynBoolFilter\<cdot>(smap f\<cdot>s)\<cdot>(\<up>a \<Zcat> s')" .
    
    from this step show ?thesis
      by (simp add: Eps assms(1)
          left)
    qed
  qed



text \<open>The helper transition of @{const tsynRemDups_h} outputs either the current input or an empty time slot.\<close>
lemma tsynremdups_h_values: 
  "snd (tsynRemDups_h state input) \<in> {input, \<sim>}"
  by (metis (no_types, lifting) insert_iff snd_eqD tsynRemDups_h.elims)



text \<open>Duplicate removal produces no new messages exept for @{const Eps}.\<close>

lemma tsynremdups_h_snd_eq_init_or_eps:
    "\<And> s m. snd (tsynRemDups_h s m) = snd (tsynRemDups_h \<sim> m) \<or> snd (tsynRemDups_h s m) \<in> {\<sim>}"
    apply (auto simp:)
    by (metis empty_iff insert_iff snd_conv tsyn.distinct(1) tsynRemDups_h.simps(2) tsynremdups_h_values)

lemma tsynremdups_h_nextstate_eq_init_if_init_noneps:
    "\<And> s m. fst (tsynRemDups_h \<sim> m) \<noteq> \<sim> \<Longrightarrow> fst (tsynRemDups_h \<sim> m) = fst (tsynRemDups_h s m)"
    by (metis fst_conv tsynRemDups_h.elims tsynRemDups_h.simps(1))

lemma tsynremdups_h_svalues_subset_init:
  "sValues\<cdot>(sscanlAOne tsynRemDups_h state\<cdot>s) \<subseteq> sValues\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s) \<union> {\<sim>}"
  using tsynremdups_h_snd_eq_init_or_eps tsynremdups_h_nextstate_eq_init_if_init_noneps
  by (meson svalues_sscanlaone_subset_sscanlaone_init)

text \<open>َEvery value produced by @{const tsynRemDups} originates
from the input stream or is an empty time slot @{term \<sim>}.\<close>
lemma tsynremdups_h_snd_eq_input_or_eps:
  "\<And> s m. snd (tsynRemDups_h s m) = m \<or> snd (tsynRemDups_h s m) \<in> {\<sim>}"
  apply (auto simp:)
  by (metis snd_conv tsyn.distinct(1) tsynRemDups_h.elims)

lemma svalues_tsynremdups_subset_input_union_eps:
  "sValues\<cdot>(tsynRemDups\<cdot>s) \<subseteq>  sValues\<cdot>s \<union> {\<sim>} " 
  unfolding tsynRemDups_def
  using svalues_sscanlaone_subset_input_union
  by (metis tsynremdups_h_snd_eq_input_or_eps)

text \<open>Duplcate removal preserves @{term Eps}.\<close>
lemma tsynremdups_sconc_eps: "tsynRemDups\<cdot>(\<up>Eps \<Zcat> s) = \<up>Eps \<Zcat> tsynRemDups\<cdot>s"
  apply (auto simp: tsynRemDups_def)
  using tsynRemDups_h.cases
  by (simp add: sscanlaone_step)

text \<open>Prepending @{term Eps} doesn't change the number of messages of a stream after duplicate removal.\<close>
lemma tsynlen_tsynremdups_cons_eps:
  "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>Eps \<Zcat> s)) = tsynLen\<cdot>(tsynRemDups\<cdot>s)"
  apply (simp add: tsynRemDups_def tsynLen_def)
  proof -
    have "tsynRemDups\<cdot>(\<up>Eps \<Zcat> s) = \<up>Eps \<Zcat> tsynRemDups\<cdot>s"
      using tsynremdups_sconc_eps
      by auto
    hence "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>Eps \<Zcat> s))
         = tsynLen\<cdot>(\<up>Eps \<Zcat> tsynRemDups\<cdot>s)"
      by simp
    also have "... = tsynLen\<cdot>(tsynRemDups\<cdot>s)"
      by (simp add: tsynlen_sconc_Eps)
    then show " (\<Lambda> (s::'a tsyn stream). #(s\<^sup>-))\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>\<sim> \<Zcat> s)) 
                = (\<Lambda> (s::'a tsyn stream). #(s\<^sup>-))\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s)" 
      by (metis \<open>tsynRemDups\<cdot>(\<up>\<sim> \<Zcat> (s::'a tsyn stream)) = \<up>\<sim> \<Zcat> tsynRemDups\<cdot>s\<close> tsynLen_def tsynRemDups_def)
  qed

text \<open>Starting duplicate removal with an initial message produces no more messages than starting with @{const Eps}.\<close>


lemma tsynlen_sup_eps_zero: "\<And>x. x \<in> {\<sim>} \<Longrightarrow> tsynLen\<cdot>(sup' x) = 0"
  apply (auto simp: tsynLen_def)
  by (metis tsynLen_def tsynlen_singleton_Eps)

lemma tsynlen_tail_tsynmsg:
  "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s)
   \<le> tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s)"
  using tsynremdups_h_nextstate_eq_init_if_init_noneps tsynlen_sup_eps_zero tsynremdups_h_snd_eq_init_or_eps
  by (metis tsynlen_sscanlaone_stateleq)

lemma tsynlen_tsynremdups_cons_tsynmsg_le1:
  "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s)) \<le> tsynLen\<cdot>(tsynRemDups\<cdot>s) + 1"
proof -
  have decomp:
    "tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s)
     = sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>(TSynMsg v) \<Zcat> s)"
    by (simp add: tsynRemDups_def)

  also have
    "\<dots> = sup' (snd (tsynRemDups_h \<sim> (TSynMsg v))) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> (TSynMsg v)))\<cdot>s"
    by (simp add: sscanlaone_step)

  moreover have "tsynRemDups_h \<sim> (TSynMsg v) = (TSynMsg v, TSynMsg v)"
    by (simp add:)

  ultimately have
    "tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s) = sup' (TSynMsg v) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s"
    by simp

  hence LHS:
    "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s)) = tsynLen\<cdot>(sup' (TSynMsg v) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s)"
    by simp

  also have
    "tsynLen\<cdot>(sup' (TSynMsg v) \<Zcat>\<Zcat> t) = tsynLen\<cdot>t + 1" for t
    by (simp add: tsynlen_sconc_tsynmsg)

  from this have
    "tsynLen\<cdot>(sup' (TSynMsg v) \<Zcat>\<Zcat> sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s) = tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s) + 1"
    by simp

  also have
    "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s) \<le> tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s)"
    by (rule tsynlen_tail_tsynmsg)

  hence
    "tsynLen\<cdot>(sscanlAOne tsynRemDups_h (TSynMsg v)\<cdot>s) + 1 \<le> tsynLen\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>s) + 1"
    by (simp add: lessequal_addition)

  also have "sscanlAOne tsynRemDups_h \<sim>\<cdot>s = tsynRemDups\<cdot>s"
    by (simp add: tsynRemDups_def)

  finally show ?thesis
    by simp
qed

lemma tsynlen_tsynremdups_le[simp]:
  "tsynLen\<cdot>(tsynRemDups\<cdot>s) \<le> tsynLen\<cdot>s"
proof (induction s)
  case adm
  show ?case
  unfolding adm_def
proof (intro allI impI)
  fix Y :: "nat \<Rightarrow> 'a tsyn stream"
    assume chainY: "chain Y"
    assume IH_all: "\<forall>i. #\<^sub>-(tsynRemDups\<cdot>(Y i)) \<le> #\<^sub>-(Y i)"
    from IH_all have IH: "\<And>i. #\<^sub>-(tsynRemDups\<cdot>(Y i)) \<le> #\<^sub>-(Y i)"
      by blast
    have len_lub_tsrd:
      "#\<^sub>-(tsynRemDups\<cdot>(\<Squnion>i. Y i)) = (\<Squnion>i. #\<^sub>-(tsynRemDups\<cdot>(Y i)))"
      using chainY
      by (simp add: cont2contlubE) 
    have len_lub:
      "#\<^sub>-(\<Squnion>i. Y i) = (\<Squnion>i. #\<^sub>-(Y i))"
      using chainY
      by (simp add: cont2contlubE)
    from IH have lub_ineq:
      "(\<Squnion>i. #\<^sub>-(tsynRemDups\<cdot>(Y i))) \<le> (\<Squnion>i. #\<^sub>-(Y i))"
      using lub_mono monotoneI chain_mono chainY lub_mono2 by auto
    show "#\<^sub>-(tsynRemDups\<cdot>(\<Squnion>i. Y i)) \<le> #\<^sub>-(\<Squnion>i. Y i)"
      unfolding len_lub_tsrd len_lub
      using lub_ineq by simp
  qed
next
  case bottom
  then show ?case
    by (simp add: tsynRemDups_def tsynLen_def sscanlAOne_def)
next
  case (step a s)
  have sscan_step:
    "tsynRemDups\<cdot>(\<up>a \<Zcat> s) =
       sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>a \<Zcat> s)"
    by (simp add: tsynRemDups_def)

  show ?case
  proof (cases a)
    case Eps
    have "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>Eps \<Zcat> s)) \<le> tsynLen\<cdot>(tsynRemDups\<cdot>s)"
      by (simp add: tsynlen_tsynremdups_cons_eps)
    also have "\<dots> \<le> tsynLen\<cdot>s"
      using step.IH .
    also have "\<dots> \<le> tsynLen\<cdot>(\<up>Eps \<Zcat> s)"
      by (simp add: tsynlen_sconc_Eps)
    finally show ?thesis using Eps by blast
    next
    case (Msg v)
    have "tsynLen\<cdot>(tsynRemDups\<cdot>(\<up>(TSynMsg v) \<Zcat> s))
          \<le> tsynLen\<cdot>(tsynRemDups\<cdot>s) + 1"
      by (rule tsynlen_tsynremdups_cons_tsynmsg_le1)
    also have "\<dots> \<le> tsynLen\<cdot>s + 1"
      using step.IH lnat_plus_suc by fastforce
    also have "\<dots> = tsynLen\<cdot>(\<up>(TSynMsg v) \<Zcat> s)"
      by (simp add: tsynlen_sconc_tsynmsg)
    finally show ?thesis
      using Msg by simp
  qed
qed

lemma tsynremdups_strict[simp]: "tsynRemDups\<cdot>\<epsilon> = \<epsilon>" 
  by (simp add: sscanlAOne_def tsynRemDups_def)

lemma tsynremdups_sup[simp]: "tsynRemDups\<cdot>(\<up>a) = \<up>a"
  apply (cases a)
  by (simp_all add: tsynRemDups_def sscanlAOne_def)

lemma tsynremdups_unfold: "tsynRemDups\<cdot>s = sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) \<sim>\<cdot>s"
  by (simp add: tsynRemDups_def sscanlAOne_def apsnd_def map_prod_def)

lemma [simp]: "cont (\<lambda>xa. #(sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) x\<cdot>xa))"
  using cont_compose_mix len_stream_cont by blast

lemma tsynremdups_msg_eq: "tsynRemDups\<cdot>(\<up>(TSynMsg a)\<Zcat>\<up>(TSynMsg a)\<Zcat>s) =  tsynRemDups\<cdot>(\<up>(TSynMsg a)\<Zcat>\<up>\<sim>\<Zcat>s)" 
  by(simp add: tsynRemDups_def sscanlAOne_def)

lemma tsynremdups_msg_neq: 
  "a\<noteq>b \<Longrightarrow> tsynRemDups\<cdot>(\<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b) \<Zcat> s) = \<up>(TSynMsg a) \<Zcat>  tsynRemDups\<cdot>(\<up>(TSynMsg b) \<Zcat> s)" 
  by(simp add: tsynRemDups_def sscanlAOne_def)

lemma tsynremdups_tsynlen_msg_Eps: " #\<^sub>-(\<alpha>\<^sub>-(\<up>(TSynMsg aa) \<Zcat> \<up>\<sim> \<Zcat> y)) =  #\<^sub>-(\<alpha>\<^sub>-(\<up>(TSynMsg aa) \<Zcat> y))"
  by (cases y, simp_all add: tsynremdups_unfold tsynlen_sconc_Eps tsynlen_sconc_msg 
                  tsynlen_singleton_msg tsynlen_singleton_Eps)

lemma tsynremdups_tsynlen_msg_eq: " #\<^sub>-(\<alpha>\<^sub>-(\<up>(TSynMsg aa) \<Zcat> \<up>(TSynMsg aa) \<Zcat> y)) =  #\<^sub>-(\<alpha>\<^sub>-(\<up>(TSynMsg aa) \<Zcat> y))"
  by (cases y, simp_all add: tsynremdups_unfold tsynlen_sconc_Eps tsynlen_sconc_msg 
                  tsynlen_singleton_msg tsynlen_singleton_Eps)

lemma "#\<^sub>-(\<alpha>\<^sub>-(<[Eps]>)) = #\<^sub>-(<[Eps]>)"
  by (simp add: tsynlen_insert)

lemma  "#\<^sub>-(\<alpha>\<^sub>-(<[TSynMsg (1::nat), TSynMsg 1]>)) < #\<^sub>-(<[TSynMsg 1, TSynMsg 1]>)"
  apply (simp add: tsynlen_insert)
  using  sconc_snd_empty 
  by (metis Fin_Suc eq_Suc_0_numeral1 ln_less lnat_1_inf one_lnat_def tsynlen_insert tsynlen_singleton_msg tsynremdups_sup
      tsynremdups_tsynlen_msg_eq)


lemma tsynabs_tsynremdups_msg_eq[simp]: 
"(tsynRemDups\<cdot>(\<up>(TSynMsg a)\<Zcat>\<up>(TSynMsg a)\<Zcat>s))\<^sup>- = (tsynRemDups\<cdot>(\<up>(TSynMsg a)\<Zcat>s))\<^sup>-"
  apply (cases s)
  by (simp add: tsynremdups_unfold)+

lemma tsynabs_tsynremdups_msg_eps[simp]: 
"(tsynRemDups\<cdot>(\<up>(TSynMsg a)\<Zcat>\<up>Eps\<Zcat>s))\<^sup>- = (tsynRemDups\<cdot>(\<up>(TSynMsg a)\<Zcat>s))\<^sup>-"
  apply (cases s)
  by (simp add: tsynremdups_unfold)+

lemma tsynremdups_tsynabs_msg:"(\<alpha>\<^sub>-(\<up>(TSynMsg m) \<Zcat> s))\<^sup>- = srcdups\<cdot>(\<up>m \<Zcat> s\<^sup>-)"
  apply(simp add: sscanlAOne_def tsynRemDups_def)
  by (induct s arbitrary: m rule: tsyn_ind, simp_all)

lemma tsynremdups_tsynabs: "(\<alpha>\<^sub>- s)\<^sup>- = (srcdups\<cdot>(s\<^sup>-))"
  apply (induct s rule:tsyn_ind, simp_all)
   apply (case_tac s, simp_all)
  apply (case_tac a)
    apply (simp_all add: tsynremdups_sconc_eps)
   prefer 2
   apply (case_tac "aa=m", simp_all add: tsynremdups_msg_neq)
  using tsynremdups_tsynabs_msg 
  by blast

lemma tsynremdups_eq2:"a=b \<Longrightarrow> \<alpha>\<^sub>-(\<up>a\<Zcat>\<up>b\<Zcat>s) = \<alpha>\<^sub>-(\<up>b\<Zcat>\<up>Eps\<Zcat>s)"
  by (cases a; cases b; simp add: tsynremdups_msg_eq) 

lemma tsynremdups_slen [simp]: "#(\<alpha>\<^sub>-s) = #s"
proof - 
  have "\<And>a. #(sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) a\<cdot>s) = #s"
    apply (induction s rule: tsyn_ind)
    apply (rule adm_all)+
    apply (rule adm_eq)
    by (simp_all)

  thus ?thesis
    by (simp add: tsynremdups_unfold)
qed

lemma tsynremdups_idem_helper: "(sscanlAOne tsynRemDups_h u)\<cdot>((sscanlAOne tsynRemDups_h u)\<cdot>y) =
         ((sscanlAOne tsynRemDups_h u)\<cdot>y)"
  apply (induct y arbitrary: u rule: tsyn_ind, simp_all)
  apply (simp add: sscanlAOne_def)
  apply (simp add: sscanlaone_step)
  by (simp add: sscanlaone_step)

lemma tsynremdups_idem_helper2: "(sscanlAOne tsynRemDups_h Eps)\<cdot>((sscanlAOne tsynRemDups_h u)\<cdot>y) =
         ((sscanlAOne tsynRemDups_h u)\<cdot>y)"
  apply (induct y arbitrary: u rule: tsyn_ind, simp_all)
  apply (simp add: sscanlAOne_def)
  apply (case_tac u; simp add: sscanlaone_step tsynremdups_idem_helper)
  by (case_tac u; simp add: sscanlaone_step tsynremdups_idem_helper)

lemma tsynremdups_idem: "\<alpha>\<^sub>-(\<alpha>\<^sub>-y) = \<alpha>\<^sub>-y"
    apply (simp add: tsynRemDups_def)
    using tsynremdups_idem_helper  
    by blast

lemma tsynremdups_step: "\<alpha>\<^sub>-(\<up>a \<Zcat> s) = \<up>a \<Zcat> ((sscanlAOne tsynRemDups_h a)\<cdot>s)"
  apply(rule tsyn_ind [of _ s], simp_all add: sscanlAOne_def)
  apply (case_tac "a = TSynMsg m"; simp add: tsynRemDups_def sscanlAOne_def)
  apply (cases a; simp)
  by (cases a; simp add: tsynRemDups_def sscanlAOne_def)

lemma tsynremdups_sscanlAOne_step: "(sscanlAOne tsynRemDups_h u)\<cdot> (\<up>a \<Zcat> s)
        = \<up>(snd(tsynRemDups_h u a)) \<Zcat> (sscanlAOne tsynRemDups_h (fst(tsynRemDups_h u a)))\<cdot>s "
  by (simp add: sscanlAOne_def)

lemma tsynremdups_eq3:"a=b \<Longrightarrow> \<alpha>\<^sub>-(\<up>a\<Zcat>\<up>b\<Zcat>s) = \<up>a\<Zcat>((sscanlAOne tsynRemDups_h b)\<cdot>(\<up>Eps\<Zcat>s))"
  by (cases a; cases b; simp add: sscanlAOne_def tsynRemDups_def)

lemma tsynremdups_eq4:"a=b \<Longrightarrow> \<alpha>\<^sub>-(\<up>a\<Zcat>\<up>b\<Zcat>s) = \<up>a\<Zcat>\<up>Eps\<Zcat>((sscanlAOne tsynRemDups_h b)\<cdot>(s))"
  by (cases a; cases b; simp add: sscanlAOne_def tsynRemDups_def)

lemma tsynremdups_ex:"\<exists>y. \<alpha>\<^sub>-(\<up>a\<Zcat>s) = \<up>a\<Zcat>y"
  apply (simp add: sscanlAOne_def tsynRemDups_def)
  by (metis sscanlAOne_def tsynRemDups_def sscanlaone_step tsynremdups_step)

lemma tsynremdups_shd[simp]:"shd (\<alpha>\<^sub>-(\<up>a\<Zcat>s)) = a"
  apply (simp add: sscanlAOne_def tsynRemDups_def) 
  by (metis snd_conv tsynRemDups_h.elims)

lemma tsynremdups_srt:"srt\<cdot>(\<alpha>\<^sub>-(\<up>a\<Zcat>s)) = (sscanlAOne tsynRemDups_h a)\<cdot>s"
  by (cases a; simp add: sscanlAOne_def tsynRemDups_def) 

lemma tsynremdups_shd2[simp]:"s\<noteq>\<epsilon> \<Longrightarrow> shd (\<alpha>\<^sub>-s) = shd s"
  by (cases s; simp)

lemma tsynremdups_srt2:"s\<noteq>\<epsilon> \<Longrightarrow> srt\<cdot>(\<alpha>\<^sub>-s) = (sscanlAOne tsynRemDups_h (shd s))\<cdot>(srt\<cdot>s)"
  by (cases s; simp add: tsynremdups_srt)

lemma tsynRemDups_h_srt2_msg:"s\<noteq>\<epsilon> \<Longrightarrow> (shd s) = TSynMsg a \<Longrightarrow> srt\<cdot>((sscanlAOne tsynRemDups_h u)\<cdot>s) = (sscanlAOne tsynRemDups_h (shd s))\<cdot>(srt\<cdot>s)"
  by (cases s; simp add: sscanlAOne_def tsynRemDups_def)

lemma tsynRemDups_h_srt2_Eps:"s\<noteq>\<epsilon> \<Longrightarrow> (shd s) = Eps \<Longrightarrow> srt\<cdot>((sscanlAOne tsynRemDups_h u)\<cdot>s) = (sscanlAOne tsynRemDups_h u)\<cdot>(srt\<cdot>s)"
  by (cases s; simp add: sscanlAOne_def tsynRemDups_def)

lemma tsynremdups_imposs_h:"Fin 1 < #\<^sub>-(\<alpha>\<^sub>-s) \<Longrightarrow>  shd((\<alpha>\<^sub>-s)\<^sup>-)\<noteq>shd(srt\<cdot>((\<alpha>\<^sub>-s)\<^sup>-))"
  by (metis tsynremdups_tsynabs srcdups_imposs_h One_nat_def tsynlen_insert tsynremdups_tsynabs)
 
lemma tsynremdups_imposs:"(\<alpha>\<^sub>-(\<up>(TSynMsg a) \<Zcat> s))\<^sup>- \<noteq> \<up>a \<Zcat> \<up>a \<Zcat> y" 
  apply(cases "#((\<alpha>\<^sub>-(\<up>(TSynMsg a) \<Zcat> s))\<^sup>-)  < Fin 1 ")  
  apply (metis One_nat_def bot_is_0 lnat.con_rews neq02Suclnle not_less slen_scons)
  apply(insert tsynremdups_imposs_h[of "\<up>(TSynMsg a)\<Zcat> s"])
  by (metis (no_types, opaque_lifting) len_one_stream linorder_less_linear shd1 srt_supconc sup_conc_eps2 supconc_neps2
      tsynlen_insert)

lemma tsynremdups_imposs2: "(\<alpha>\<^sub>-(\<up>(TSynMsg a) \<Zcat> s))\<^sup>- \<noteq> \<up>a \<Zcat> \<up>a \<Zcat> (\<alpha>\<^sub>- s)\<^sup>-" 
  by (simp add: tsynremdups_imposs)

lemma tsynremdups_imposs3: "\<alpha>\<^sub>-(\<up>(TSynMsg a) \<Zcat> s) \<noteq> \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg a) \<Zcat> y" 
  by (metis tsynabs_sconc_msg tsynremdups_imposs)

lemma tsynremdups_imposs4_h:"\<forall>x. (\<alpha>\<^sub>-(\<up>(TSynMsg a) \<Zcat> s))\<^sup>- \<noteq> \<up>a \<Zcat> \<up>a \<Zcat> x\<^sup>-"
  by (simp add: tsynremdups_imposs)
 
lemma tsynremdups_imposs4: "(\<alpha>\<^sub>-(\<up>(TSynMsg a) \<Zcat> s))\<^sup>- \<noteq> \<up>a \<Zcat> \<up>a \<Zcat> s\<^sup>-"
  by(simp add: tsynremdups_imposs) 

lemma tsynremdups_imposs5: "\<alpha>\<^sub>-(\<up>(TSynMsg a) \<Zcat> s) \<noteq> \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg a) \<Zcat> s"
  by(simp add: tsynremdups_imposs3) 

lemma tsynremdups_anotb_h:"\<alpha>\<^sub>-(\<up>(TSynMsg a)\<Zcat>\<up>(TSynMsg b)) = \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b) \<Longrightarrow> a \<noteq> b"
  by (metis sconc_snd_empty tsynremdups_imposs3)
  
lemma tsynremdups_anotb:"\<alpha>\<^sub>-(\<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b) \<Zcat> s) = \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b) \<Zcat> s \<Longrightarrow> a\<noteq> b"
  using tsynremdups_imposs3 by blast

lemma tsynremdups_prefix_neq_h: " (\<And>u st y. s \<sqsubseteq> y \<Longrightarrow>
           sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (u, st)\<cdot>s) \<noteq> s \<Longrightarrow>
           sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (u, st)\<cdot>y) = y \<Longrightarrow> False) \<Longrightarrow>
       \<up>(TSynMsg m) \<Zcat> s \<sqsubseteq> y \<Longrightarrow>
       \<up>(TSynMsg m) \<Zcat> sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (TSynMsg m, TSynMsg m)\<cdot>s) \<noteq> \<up>(TSynMsg m) \<Zcat> s \<Longrightarrow>
       sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (u, st)\<cdot>y) = y \<Longrightarrow> st \<noteq> TSynMsg m \<Longrightarrow> False"
proof -
  assume IH: "(\<And>u st y.
      s \<sqsubseteq> y \<Longrightarrow>
      sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (u, st)\<cdot>s) \<noteq> s \<Longrightarrow>
      sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (u, st)\<cdot>y) = y \<Longrightarrow> False)"
  assume prefix: "\<up>(TSynMsg m) \<Zcat> s \<sqsubseteq> y"
  assume ms: "\<up>(TSynMsg m) \<Zcat> sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y)
               (TSynMsg m, TSynMsg m)\<cdot>s) \<noteq> \<up>(TSynMsg m) \<Zcat> s"
  assume eqy: "sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (u, st)\<cdot>y) = y"
  assume state: "st \<noteq> TSynMsg m"

  have f1:"s \<sqsubseteq> srt\<cdot>y \<and> shd y = TSynMsg m"
    using less_all_sconsD prefix by (metis less_fst_sconsD supconc_neps surj_scons)
  have f2: "sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (TSynMsg m, TSynMsg m)\<cdot>s) \<noteq> s"
    using ms by force
  have f3: "sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (u, st)\<cdot>y)
          = \<up>(TSynMsg m) \<Zcat> sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y)
              (TSynMsg m, TSynMsg m)\<cdot>(srt\<cdot>y))"
    using state f1 less_fst_sconsD prefix by force
  have f4: "\<up>(TSynMsg m) \<Zcat> s \<sqsubseteq> y \<Longrightarrow>
            \<up>(TSynMsg m) \<Zcat> sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y)
                (TSynMsg m, TSynMsg m)\<cdot>s) \<noteq> \<up>(TSynMsg m) \<Zcat> s \<Longrightarrow>
            sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (u, st)\<cdot>y) = y \<Longrightarrow>
            st \<noteq> TSynMsg m \<Longrightarrow> False"
    using f1 f2 f3 IH by (metis srt_supconc)
  from f4[OF prefix ms eqy state]
  show False .
qed

lemma tsynremdups__unfold_prefix_neq: 
  "x \<sqsubseteq> y \<longrightarrow>
    (\<forall> a. sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) a\<cdot>x \<noteq> x
     \<longrightarrow> sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) a\<cdot>y \<noteq> y)"
    apply auto
    apply (induction x arbitrary: y rule: tsyn_ind)
    apply (rule adm_all)+ 
     apply simp_all
   apply (smt case_prod_beta conc_stream_def inject_scons lessD snd_conv sscanlAsimps_step supconc_neps2 tsynRemDups_h.simps(2))
  by (smt case_prod_beta conc_stream_def inject_scons lessD split_pairs2 sscanlAsimps_step supconc_neps2 tsynRemDups_h.simps(1))

lemma tsynremdups_prefix_neq: assumes "x \<sqsubseteq> y" and  "\<alpha>\<^sub>-x \<noteq> x" shows  "\<alpha>\<^sub>-y \<noteq> y"
    using assms tsynremdups__unfold_prefix_neq
    by (metis tsynremdups_unfold)

lemma tsynremdups_tsynmap_adm [simp]: 
  "adm (\<lambda>a. \<alpha>\<^sub>-(tsynMap f\<cdot>(\<alpha>\<^sub>-a)) = tsynMap f\<cdot>(\<alpha>\<^sub>-a) 
    \<longrightarrow> \<alpha>\<^sub>-(tsynMap f\<cdot>a) = tsynMap f\<cdot>(\<alpha>\<^sub>-a))"
  apply (rule adm_imp, auto) 
  apply(rule adm_upward; rule ccontr)
  using tsynremdups_prefix_neq
  by (metis monofun_cfun_arg)

lemma tsynremdups_tsynmap_com_h:
  "sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) (TSynMsg (f m))\<cdot>
    (tsynMap f\<cdot>(sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) (TSynMsg m)\<cdot>s))
    = tsynMap f\<cdot>(sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) (TSynMsg m)\<cdot>s)
\<Longrightarrow> sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) (TSynMsg (f m))\<cdot>(tsynMap f\<cdot>s)
    = tsynMap f\<cdot>(sscanlA (\<lambda>s i. case tsynRemDups_h s i of (x, y) \<Rightarrow> (x, \<up>y)) (TSynMsg m)\<cdot>s)"
  apply (induction s arbitrary: f m rule: tsyn_ind)
    apply (rule adm_all)+
    apply (rule adm_imp)
     apply(rule adm_upward; rule ccontr)
     apply (metis cont_pref_eq1I tsynremdups__unfold_prefix_neq)
     apply(simp_all)
   apply (case_tac "m=ma")
    apply (simp add: tsynmap_sconc_msg tsynmap_sconc_Eps)
    apply (metis srt_supconc)
   apply (case_tac "f m = f ma")
    apply (simp_all add: tsynmap_sconc_msg tsynmap_sconc_Eps)
  using inject_scons apply blast
  by (metis srt_supconc)+

lemma tsynremdups_tsynmap_com:
  shows "\<alpha>\<^sub>-(tsynMap f\<cdot>(\<alpha>\<^sub>-s)) = tsynMap f\<cdot>(\<alpha>\<^sub>-s) \<Longrightarrow> \<alpha>\<^sub>-(tsynMap f\<cdot>s) = tsynMap f\<cdot>(\<alpha>\<^sub>-s)"
  proof(induction rule: tsyn_ind [of _ s])
    case adm
    then show ?case by simp
  next
    case bot
    then show ?case by simp
  next
    case (msg m s)
    thus ?case
      apply (simp add: tsynmap_sconc_msg tsynremdups_unfold)
      by (metis srt_supconc tsynremdups_tsynmap_com_h)
  next
    case (Eps s)
    then show ?case 
      apply (simp add: tsynremdups_sconc_eps tsynmap_sconc_Eps)
      by (metis srt_supconc)
  qed

lemma tsynremdups_nbot: "s\<noteq>\<bottom>\<Longrightarrow>tsynRemDups\<cdot>s \<noteq> \<bottom>"
  by (metis lscons_conv tsynremdups_ex stream.con_rews(2) surj_scons)

lemma tsynabs_stake_exists: "\<exists>k. ((stake n\<cdot>s)\<^sup>-) = (stake k\<cdot>(s\<^sup>-))" 
proof -
  have "\<exists>k. sfilter {e. e \<noteq> Eps}\<cdot>(stake n\<cdot>s)
            = stake k\<cdot>(sfilter {e. e \<noteq> Eps}\<cdot>s)"
    by (rule sfilter_stake_exists)
  then obtain k where
    F: "sfilter {e. e \<noteq> Eps}\<cdot>(stake n\<cdot>s)
        = stake k\<cdot>(sfilter {e. e \<noteq> Eps}\<cdot>s)"
    by blast
  hence "smap tsyn2ustreamElem\<cdot>(sfilter {e. e \<noteq> Eps}\<cdot>(stake n\<cdot>s))
       = smap tsyn2ustreamElem\<cdot>(stake k\<cdot>(sfilter {e. e \<noteq> Eps}\<cdot>s))"
    by simp
  also have "... = stake k\<cdot>(smap tsyn2ustreamElem\<cdot>(sfilter {e. e \<noteq> Eps}\<cdot>s))"
    by (simp add: smap_stake_distrib)
    finally have
    "(stake n\<cdot>s)\<^sup>-
     = stake k\<cdot>(s\<^sup>-)"
    by (simp add: tsyn2ustream_def)
  thus ?thesis by blast
qed

lemma tsynremdups_fin2: assumes " #\<^sub>-(\<alpha>\<^sub>-s)<\<infinity>" and " #\<^sub>-s=\<infinity>"
  obtains x where "\<alpha>\<^sub>-x = \<alpha>\<^sub>-s" and "#\<^sub>-x < \<infinity>"
  using assms(1) tsynremdups_idem by blast

lemma tsynremdups_fin3: assumes " #\<^sub>-(\<alpha>\<^sub>-s)<\<infinity>" and " #\<^sub>-s=\<infinity>"
  obtains x where "(\<alpha>\<^sub>-x)\<^sup>- = (\<alpha>\<^sub>-s)\<^sup>-" and "x\<^sup>- \<sqsubseteq> s\<^sup>-" and "#\<^sub>-x < \<infinity>"
proof -
  obtain n where a1:"srcdups\<cdot>((stake n\<cdot>s)\<^sup>-) = srcdups\<cdot>(s\<^sup>-)"
    using assms(1) apply (simp add: tsynlen_insert tsynremdups_tsynabs)
    by (metis (no_types, lifting) cfcomp2 fun_approxl2 len_stream_def lnat_well_h2)
  obtain k where a2:"srcdups\<cdot>((stake n\<cdot>s)\<^sup>-) = srcdups\<cdot>(stake k\<cdot>(s\<^sup>-))"
    using tsynabs_stake_exists by metis
  thus ?thesis
    using lnless_def that a1 a2
    by (metis antisym_conv3 inf_great inf_less_eq monofun_cfun_arg slen_stake_fin tsynlen_slen tsynremdups_tsynabs ub_stake) 
qed

lemma tsynremdups_tsynabs_consec_noteq: "Fin (Suc n) <  #\<^sub>-(\<alpha>\<^sub>-xs) \<Longrightarrow> snth n ((\<alpha>\<^sub>-xs)\<^sup>-) \<noteq> snth (Suc n) ((\<alpha>\<^sub>-xs)\<^sup>-)"
  by (simp add: srcdups_consec_noteq tsynlen_insert tsynremdups_tsynabs)

lemma tsynremdups_consec_noteq: "Fin (Suc n) < #(\<alpha>\<^sub>-xs) \<Longrightarrow> snth n (\<alpha>\<^sub>-xs) = TSynMsg a \<Longrightarrow> snth n (\<alpha>\<^sub>-xs) \<noteq> snth (Suc n) (\<alpha>\<^sub>-xs)"
proof
  fix n :: nat
  assume a1: "Fin (Suc n) < #(\<alpha>\<^sub>-xs)" and a2: "snth n (\<alpha>\<^sub>-xs) = TSynMsg a" and a3: "snth n (\<alpha>\<^sub>-xs) = snth (Suc n) (\<alpha>\<^sub>-xs)"
  then obtain b s where "sdrop n\<cdot>(\<alpha>\<^sub>-xs) = \<up>(TSynMsg b) \<Zcat> \<up>(TSynMsg b) \<Zcat> s"
    by (metis drop_not_all snth_def srt_drop stream.sel_rews(2) surj_scons)
  then have p: "\<alpha>\<^sub>-(sdrop n\<cdot>(\<alpha>\<^sub>-xs)) \<noteq> sdrop n\<cdot>(\<alpha>\<^sub>-xs)"
    by (metis tsynremdups_imposs3)
  have not_p: "\<alpha>\<^sub>-(sdrop n\<cdot>(\<alpha>\<^sub>-xs)) = sdrop n\<cdot>(\<alpha>\<^sub>-xs)"
  proof -
    have "\<alpha>\<^sub>-(sdrop n\<cdot>(\<alpha>\<^sub>-xs)) = sdrop n\<cdot>(\<alpha>\<^sub>-(\<alpha>\<^sub>-xs))" using tsynremdups_idem 
    proof - 
      have "xs \<noteq> \<epsilon>" using a1 by auto 
      then have "\<forall> st. sscanlAOne tsynRemDups_h \<sim>\<cdot>(sdrop n\<cdot>(sscanlAOne tsynRemDups_h st\<cdot>xs)) =
      sdrop n\<cdot>(sscanlAOne tsynRemDups_h \<sim>\<cdot>(sscanlAOne tsynRemDups_h st\<cdot>xs)) " 
        apply auto
        apply (induction n arbitrary: xs)
         apply simp
        apply (simp add: sdrop_forw_rt)
        apply (case_tac "shd xs", simp add: tsynRemDups_h_srt2_Eps tsynremdups_idem_helper2) 
        using strict_sdrop  tsynremdups_idem_helper2 
        apply (metis (no_types, lifting))
        apply (simp add: tsynRemDups_h_srt2_msg tsynremdups_idem_helper2) 
        using strict_sdrop  tsynremdups_idem_helper2 
        by (metis (no_types, lifting))
      then show ?thesis by (simp add: tsynRemDups_def)
    qed
  thus "\<alpha>\<^sub>-(sdrop n\<cdot>(\<alpha>\<^sub>-xs)) = sdrop n\<cdot>(\<alpha>\<^sub>-xs)"
      by (simp add: tsynremdups_idem)
  qed
  thus "False"
    using p by auto
qed

(* interessante Aussage..könnte man auf Korrektheit überprüfen
lemma tsynremdups_tsynabs_snth_stake_fin: "\<And>s n.  #\<^sub>-s = Fin k \<Longrightarrow> k > (Suc n) 
            \<Longrightarrow> snth n (tsyn2ustream\<cdot>s) \<noteq> snth (Suc n) (tsyn2ustream\<cdot>s)
            \<Longrightarrow> stake (Suc n)\<cdot>(tsyn2ustream\<cdot>(\<alpha>\<^sub>-s)) \<noteq> tsyn2ustream\<cdot>(\<alpha>\<^sub>-s)" 
 *)

lemma tsynabs_end_sconc: assumes"#s < \<infinity>" 
  shows " (s \<Zcat> \<up>(TSynMsg a))\<^sup>- = (s\<^sup>-) \<Zcat> \<up>a"
proof (cases "#s < \<infinity>")
  case True
  then show ?thesis
    apply (rule finind3, simp)
    by (case_tac aa; simp)
next
  case False
  then show ?thesis using assms
    by blast
qed

lemma tsynremdups_end_neq: "#s < \<infinity> \<Longrightarrow> a \<noteq> b \<Longrightarrow> (\<alpha>\<^sub>-(s \<Zcat> \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b)))\<^sup>- = (\<alpha>\<^sub>-(s \<Zcat> \<up>(TSynMsg a)))\<^sup>- \<Zcat> \<up>b"
  apply (cases "#s < \<infinity>")
  apply (simp add: tsynremdups_tsynabs) using tsynabs_end_sconc 
  apply (metis inf_ub leD less_le srcdups_end_neq tsynabs_sconc tsynabs_sconc_msg tsynabs_singleton_msg
      tsynabs_slen)
  by (simp add: less_le)

lemma tsynremdups_end_neq2: "#s < \<infinity> \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<alpha>\<^sub>-(s \<Zcat> \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b)) = \<alpha>\<^sub>-(s \<Zcat> \<up>(TSynMsg a)) \<Zcat> \<up>(TSynMsg b)"
proof -
  assume fin:"#s < \<infinity>" and neq:"a \<noteq> b"
  have "\<forall> st. sscanlAOne tsynRemDups_h st\<cdot>(s \<Zcat> \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b)) =
          sscanlAOne tsynRemDups_h st\<cdot>(s \<Zcat> \<up>(TSynMsg a)) \<Zcat> \<up>(TSynMsg b)"
    using fin neq proof (induction s rule: finind3)
      case 1
      then show ?case using fin by auto
    next
      case 2
      then show ?case apply auto by (case_tac st; simp add: sscanlAOne_def)
    next
      case (3 t a)
      then show ?case apply auto
        apply(case_tac st)
        by (simp add: sscanlaone_step)+
    qed
    then show ?thesis by (simp add: tsynRemDups_def)
  qed

lemma tsynremdups_end_eq: "(\<alpha>\<^sub>-(s \<Zcat> \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg a)))\<^sup>- = (\<alpha>\<^sub>-(s \<Zcat> \<up>(TSynMsg a)))\<^sup>-"
  apply (cases "#s < \<infinity>")
  apply (simp add: tsynremdups_tsynabs) using tsynabs_end_sconc
  apply (simp add: srcdups_end_eq tsynabs_sconc)
  by (simp add: less_le)

lemma tsynremdups_end_eq2: "\<alpha>\<^sub>-(s \<Zcat> \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg a)) = \<alpha>\<^sub>-(s \<Zcat> \<up>(TSynMsg a)) \<Zcat> \<up>Eps"
proof (cases "#s < \<infinity>")
  case True
  then show ?thesis
    proof -
      assume fin:"#s < \<infinity>" 
      have "\<forall> st. sscanlAOne tsynRemDups_h st\<cdot>(s \<Zcat> \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg a)) =
              sscanlAOne tsynRemDups_h st\<cdot>(s \<Zcat> \<up>(TSynMsg a)) \<Zcat> \<up>Eps"
        using fin proof (induction s rule: finind3)
          case 1
          then show ?case using fin by auto
        next
          case 2
          then show ?case apply auto by (case_tac st; simp add: sscanlAOne_def)
        next
          case (3 t a)
          then show ?case
            apply auto
            apply (case_tac st)
            by (simp add: sscanlaone_step)+
        qed
    then show ?thesis by (simp add: tsynRemDups_def)
    qed
  next
    case False
    then show ?thesis    
      by(simp add: less_le) 
  qed

lemma tsynremdups_end_Eps: "\<alpha>\<^sub>-(s \<Zcat> \<up>Eps) = \<alpha>\<^sub>-s \<Zcat> \<up>Eps"
proof (cases "#s < \<infinity>")
  case True
  then show ?thesis
    proof -
      assume fin:"#s < \<infinity>" 
      have "\<forall> st. sscanlAOne tsynRemDups_h st\<cdot>(s \<Zcat> \<up>Eps) =
              sscanlAOne tsynRemDups_h st\<cdot>s \<Zcat> \<up>Eps"
        using fin proof (induction s rule: finind3)
          case 1
          then show ?case using fin by auto
        next
          case 2
          then show ?case apply auto by (case_tac st; simp add: sscanlAOne_def)
        next
          case (3 t a)
          then show ?case 
            apply auto 
            apply (case_tac st)
            by (simp add: sscanlaone_step)+
        qed
    then show ?thesis by (simp add: tsynRemDups_def)
    qed
  next
    case False
    then show ?thesis    
      by(simp add: less_le) 
qed

lemma tsynremdups_sntimes: "n > 0 \<Longrightarrow> \<alpha>\<^sub>-(sntimes n (\<up>a)) = \<up>a\<Zcat>sntimes (n-1) (\<up>Eps)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
  proof (cases "n > 0")
    case True
    then show ?thesis
      by (metis One_nat_def Suc.IH diff_Suc_1' gr0_implies_Suc sntimes.simps(2) srt_supconc tsynremdups_eq4
          tsynremdups_srt)
    next
    case False
    then show ?thesis
      by auto
  qed
qed

lemma tsynremdups_eq: " \<alpha>\<^sub>-(\<up>a\<Zcat>\<up>a\<Zcat>s) =  \<alpha>\<^sub>-(\<up>a\<Zcat>\<up>Eps\<Zcat>s)" 
  apply (cases a)
  by (simp_all add: tsynremdups_unfold)

lemma tsynremdups_sntimes_prefix: "n > 0 \<Longrightarrow> \<alpha>\<^sub>-((n\<star>\<up>a) \<Zcat> s) 
                            = \<up>a \<Zcat>((n-1)\<star>\<up>\<sim>) \<Zcat> ((sscanlAOne tsynRemDups_h a)\<cdot>s)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n) 
    have IH_alt: "0 < n \<Longrightarrow> sscanlAOne tsynRemDups_h \<sim>\<cdot>(n\<star>\<up>a \<Zcat> s) = \<up>a \<Zcat> sscanlAOne tsynRemDups_h a\<cdot>((n-1)\<star>\<up>a \<Zcat> s) "
      apply (cases a)
      by (simp_all add: sscanlaone_step sntimes_Minus)
    have step: "0 < n \<Longrightarrow> sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>a \<Zcat> (n\<star>\<up>a) \<Zcat> s) = \<up>a \<Zcat>\<up>\<sim> \<Zcat> sscanlAOne tsynRemDups_h a\<cdot>((n-1)\<star>\<up>a \<Zcat> s) "
      apply (cases a)
      by (simp_all add: sscanlaone_step sntimes_Minus)
    have IH2: "sscanlAOne tsynRemDups_h a\<cdot>((n-1)\<star>\<up>a \<Zcat> s) = ((n-1)\<star>\<up>\<sim>) \<Zcat> ((sscanlAOne tsynRemDups_h a)\<cdot>s)"
      by (metis IH_alt Suc.IH inject_scons not_gr_zero sconc_fst_empty sntimes.simps(1) tsynRemDups_def zero_diff)
    then show ?case
      apply (simp add: tsynRemDups_def) 
      using IH_alt IH2 step 
      by (metis diff_0_eq_0 not_gr_zero sconc_scons sntimes_Minus tsynRemDups_def tsynremdups_step)
qed

lemma tsynremdups_sntimes_prefix2: "n > 0 \<Longrightarrow> \<alpha>\<^sub>-((n\<star>\<up>a) \<Zcat> (m\<star>\<up>Eps) \<Zcat> s) 
                            = \<up>a \<Zcat>((n-1+m)\<star>\<up>\<sim>) \<Zcat> ((sscanlAOne tsynRemDups_h a)\<cdot>s)"
  apply (simp add: tsynremdups_sntimes_prefix)
  apply (induct m; simp)
  apply (simp add: sscanlaone_step)
  by (metis (no_types, lifting) Suc_pred add_gr_0 assoc_sconc eq_Suc_0_numeral1 inject_scons sntimes_Minus sntimes_Suc2)


lemma tsynremdups_h_singleton_Eps:"(sscanlAOne tsynRemDups_h Eps)\<cdot>(\<up>c) = \<up>c"
  by (cases c;  simp add: sscanlAOne_def)

lemma tsynremdups_h_singleton_eq: "TSynMsg u=c \<Longrightarrow> (sscanlAOne tsynRemDups_h (TSynMsg u))\<cdot>(\<up>c) =  \<up>Eps"
  by (cases c; simp add: sscanlAOne_def)

lemma tsynremdups_h_singleton_neq: "TSynMsg u \<noteq> c \<Longrightarrow> (sscanlAOne tsynRemDups_h (TSynMsg u))\<cdot>(\<up>c) = \<up>c"
  by (cases c; simp add: sscanlAOne_def)

lemma tsynremdups_h_state_change_neq: "u \<noteq> (TSynMsg a) \<Longrightarrow> sscanlAOne tsynRemDups_h \<sim>\<cdot>(\<up>(TSynMsg a) \<Zcat> s) = sscanlAOne tsynRemDups_h u\<cdot>(\<up>(TSynMsg a) \<Zcat> s)"
  by (cases u; simp add: sscanlAOne_def)


lemma tsynRemDups_h_split_fin: "#s = Fin k \<Longrightarrow>  Suc n < k \<Longrightarrow> snth n s = TSynMsg a \<Longrightarrow>  snth (Suc n) s = TSynMsg b
            \<Longrightarrow> a \<noteq> b \<Longrightarrow> sscanlAOne tsynRemDups_h u\<cdot>s =
    sscanlAOne tsynRemDups_h u\<cdot>(stake (Suc n)\<cdot>s) \<Zcat> sscanlAOne tsynRemDups_h \<sim>\<cdot>(sdrop (Suc n)\<cdot>s)"
proof (induction k arbitrary: u n s a b)
  case 0
  then show ?case
    by auto
next
  case (Suc k)
  then obtain c t where "s = \<up>c \<Zcat> t"
    by (metis Fin_0 Suc_neq_Zero slen_zero surj_scons)
  assume a1: "snth n s = TSynMsg a" and  a2: "snth (Suc n) s = TSynMsg b" and a3: "a \<noteq> b"
  then have "Suc n < Suc k"
    using Suc.prems(2) by blast
  then show ?case
 proof (cases "k > 1")
    case True
    then obtain c d t where "s = \<up>c \<Zcat> \<up>d \<Zcat> t"
    proof -
      assume a1: "\<And>c d t. s = \<up>c \<Zcat> \<up>d \<Zcat> t \<Longrightarrow> thesis"
      have "#(\<epsilon>::'a stream) = \<bottom>"
        using bot_is_0 by auto
      then show ?thesis
        using a1 True inject_lnsuc less2nat_lemma lnat.con_rews lnle_def not_le srt_decrements_length surj_scons 
        by (metis Suc.prems(1) empty_is_shortest lnat_fin4 lnat_po_eq_conv lnat_well_h1)
    qed
    then have "t \<noteq> \<epsilon>"
      using Suc.prems(1) True by force
    then show ?thesis
    proof (cases "n = 0")
      case True
      then have f1: "snth n s = c" and  "snth (Suc n) s = d" and "c \<noteq> d"
        using True Suc.prems(3) Suc.prems(4) Suc.prems(5) \<open>s = \<up>c \<Zcat> \<up>d \<Zcat> t\<close> by auto
      then have f2: "stake (Suc n)\<cdot>s = \<up>c" and "sdrop (Suc n)\<cdot>s = \<up>d \<Zcat> t"  
        using \<open>s = \<up>c \<Zcat> \<up>d \<Zcat> t\<close>  
        by (simp add: True)+
      then show ?thesis
        apply (cases u; simp add: f2)
        using True \<open>s = \<up>c \<Zcat> \<up>d \<Zcat> t\<close> Suc.prems(3,4) f1   
        apply (metis Suc.prems(5) \<open>snth (Suc n) s = d\<close> tsynRemDups_def tsynremdups_msg_neq tsynremdups_sup)
         apply (cases "TSynMsg a = c")
        using True \<open>s = \<up>c \<Zcat> \<up>d \<Zcat> t\<close> Suc.prems(3,4) sdropl6 slen_sup  tsynremdups_h_state_change_neq 
         tsynremdups_h_singleton_eq
        apply (metis (no_types, lifting) \<open>c \<noteq> d\<close> \<open>snth (Suc n) s = d\<close> tsynRemDups_def tsynremdups_eq4
            tsynremdups_h_singleton_neq tsynremdups_step)
         using True \<open>s = \<up>c \<Zcat> \<up>d \<Zcat> t\<close> Suc.prems(3,4) sdropl6 slen_sup  tsynremdups_h_state_change_neq 
         tsynremdups_h_singleton_eq
        using f1 by argo
    next
  case False
      then obtain m where "n = Suc m"
        using not0_implies_Suc by blast
      have "#(\<up>d \<Zcat> t) = Fin k"
        using Suc.prems(1) \<open>s = \<up>c \<Zcat> \<up>d \<Zcat> t\<close> by auto
      moreover have "snth n s = snth m (\<up>d \<Zcat> t)"
        by (simp add: \<open>n = Suc m\<close> \<open>s = \<up>c \<Zcat> \<up>d \<Zcat> t\<close>)
      ultimately have eq_dt:  "\<forall> u. sscanlAOne tsynRemDups_h u\<cdot>(\<up>d \<Zcat> t) =
    sscanlAOne tsynRemDups_h u\<cdot>(stake n\<cdot>(\<up>d \<Zcat> t)) \<Zcat> sscanlAOne tsynRemDups_h \<sim>\<cdot>(sdrop n\<cdot>(\<up>d \<Zcat> t))"
        by (metis Suc.IH Suc.prems(2,3,4,5) Suc_less_SucD \<open>n = Suc m\<close> \<open>s = \<up>c \<Zcat> \<up>d \<Zcat> t\<close> snth_scons)
      then show ?thesis
        apply (simp add: True \<open>s = \<up>c \<Zcat> \<up>d \<Zcat> t\<close> ) 
        by (cases c, cases u; simp add: sscanlaone_step) 
      qed
  next
    case False
    then have "k \<le> 1"
      by auto
    then show ?thesis
    proof (cases "k = 0")
      case True
      then show ?thesis
        using Suc.prems(2) by blast
    next
      case False
      then have "k = 1"
        using \<open>k \<le> 1\<close> by auto
      then obtain c d where "s = \<up>c \<Zcat> \<up>d" 
        by (metis One_nat_def Rep_cfun_strict1 Suc.prems(1) \<open>\<And>thesis. (\<And>a t. s = \<up>a \<Zcat> t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> sconc_snd_empty sfood_id stake_Suc stream.take_0)
      then have "c \<noteq> d"
        using Suc.prems(2,3,4,5) \<open>k = 1\<close> by auto
      then have "c = TSynMsg a" and "d = TSynMsg b"
        using Suc.prems(2,3,4) \<open>k = 1\<close> \<open>s = \<up>c \<Zcat> \<up>d\<close> a1 apply simp 
        by (metis Suc.prems(1,2,4) Suc_less_eq \<open>k = 1\<close> \<open>s = \<up>c \<Zcat> \<up>d\<close> eq_Suc_0_numeral1 fin_le_inf less_one sfoot12 sfoot_exists2
            slen_sup)
      then show ?thesis
        using a3 Suc.prems(2) \<open>k = 1\<close> \<open>s = \<up>c \<Zcat> \<up>d\<close> apply simp
        by (cases u; simp add: sscanlAOne_def)
    qed
  qed
qed


lemma tsynremdups_split_fin: "#s = Fin k \<Longrightarrow>  Suc n < k \<Longrightarrow> snth n s = TSynMsg a \<Longrightarrow>  snth (Suc n) s = TSynMsg b
            \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<alpha>\<^sub>-s = \<alpha>\<^sub>-(stake (Suc n)\<cdot>s) \<Zcat> (\<alpha>\<^sub>-(sdrop (Suc n)\<cdot>s))"
  using tsynRemDups_h_split_fin 
  by (metis tsynRemDups_def)
 
lemma tsynRemDups_h_split_inf: "#s = \<infinity> \<Longrightarrow> snth n s = TSynMsg a \<Longrightarrow> snth (Suc n) s = TSynMsg b
            \<Longrightarrow> a \<noteq> b \<Longrightarrow> sscanlAOne tsynRemDups_h u\<cdot>s =
    sscanlAOne tsynRemDups_h u\<cdot>(stake (Suc n)\<cdot>s) \<Zcat> sscanlAOne tsynRemDups_h \<sim>\<cdot>(sdrop (Suc n)\<cdot>s)"
proof (induction n arbitrary: s a b u)
  case 0
    assume a1: "snth 0 s = TSynMsg a" and  a2: "snth (Suc 0) s = TSynMsg b" and a3: "a \<noteq> b"
    then obtain a b t where "s = \<up>(TSynMsg a ) \<Zcat> \<up>(TSynMsg b) \<Zcat> t" and "a \<noteq> b"
      using a1 a2 a3 inf_scase shd1 snth_scons snth_shd 
      by (metis (no_types, lifting) "0.prems"(1))
      then show ?case
        by (cases u; simp add: sscanlAOne_def)
  next
    case (Suc n)
    obtain c t where "s = \<up>c \<Zcat> t"
    using Suc.prems(1) inf_scase by blast
  then have "#t = \<infinity>"
    using Suc.prems(1) by auto
  moreover have "snth n t = TSynMsg a" and  "snth (Suc n) t = TSynMsg b" and "a \<noteq> b"
    using Suc.prems(2,3,4) \<open>s = \<up>c \<Zcat> t\<close> 
    by simp+
  ultimately have "\<forall> u. sscanlAOne tsynRemDups_h u\<cdot>t =
            sscanlAOne tsynRemDups_h u\<cdot>(stake (Suc n)\<cdot>t) \<Zcat> sscanlAOne tsynRemDups_h \<sim>\<cdot>(sdrop (Suc n)\<cdot>t)"
    using Suc.IH by blast
  then show ?case
    apply (simp add: \<open>s = \<up>c \<Zcat> t\<close>)
    by (cases u, cases c; simp add: sscanlaone_step)
qed

lemma tsynremdups_split_inf: "#s = \<infinity> \<Longrightarrow> snth n s = TSynMsg a \<Longrightarrow>  snth (Suc n) s = TSynMsg b
            \<Longrightarrow> a \<noteq> b \<Longrightarrow>  \<alpha>\<^sub>-s =  \<alpha>\<^sub>-(stake (Suc n)\<cdot>s) \<Zcat> (\<alpha>\<^sub>-(sdrop (Suc n)\<cdot>s))"
  using tsynRemDups_h_split_inf
  by (metis tsynRemDups_def)

lemma tsynremdups_split2: "Fin (Suc n) < #s \<Longrightarrow> snth n s = TSynMsg a \<Longrightarrow>  snth (Suc n) s = TSynMsg b
            \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<alpha>\<^sub>-s =  \<alpha>\<^sub>-(stake (Suc n)\<cdot>s) \<Zcat> (\<alpha>\<^sub>-(sdrop (Suc n)\<cdot>s))"
  by (metis less2nat ninf2Fin not_le tsynremdups_split_fin tsynremdups_split_inf)

text\<open>@{term tsynfoot}: Get the last message of a finite tsyn stream with at least one message\<close>
definition tsynfoot :: "'a tsyn stream \<Rightarrow> 'a tsyn " where
"tsynfoot s = TSynMsg (sfoot (s\<^sup>-))"

lemma tsynabs_end_Eps: "(s \<Zcat> \<up>\<sim>)\<^sup>- = s\<^sup>-"
proof (cases  "#s=\<infinity>")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis 
    apply (induction s rule: finind3)
    using False inf_less_eq leI apply blast
     apply simp
    by (simp add: tsynabs_sconc)
qed

lemma tsynabs_end_msg: "#s\<noteq>\<infinity> \<Longrightarrow> (s \<Zcat> \<up>(TSynMsg a))\<^sup>- = s\<^sup>- \<Zcat> \<up>a"
proof (cases  "#s=\<infinity>")
  case True
  then show "#s\<noteq>\<infinity> \<Longrightarrow> (s \<Zcat> \<up>(TSynMsg a))\<^sup>- = s\<^sup>- \<Zcat> \<up>a"  by simp
next
  case False
  then show ?thesis 
    apply (induction s rule: finind3)
    using False inf_less_eq leI apply blast
     apply simp
    by (simp add: tsynabs_sconc)
qed

lemma tsynfoot_end_Eps: "tsynfoot (s \<Zcat> \<up>Eps) = tsynfoot s"
  by (simp add: tsynfoot_def tsynabs_end_Eps)

lemma tsynfoot_singleton_msg[simp]: "tsynfoot (\<up>(TSynMsg a)) = TSynMsg a"
  by (simp add: tsynfoot_def)

lemma tsynremdups_bool_prefix:
  fixes xs :: "bool tsyn stream" and ys :: "bool tsyn stream"
  assumes "lshd\<cdot>((\<alpha>\<^sub>-xs)\<^sup>-) = lshd\<cdot>((\<alpha>\<^sub>-ys)\<^sup>-)" and "#\<^sub>-(\<alpha>\<^sub>-xs) \<le> #\<^sub>-(\<alpha>\<^sub>-ys)"
  shows "(\<alpha>\<^sub>-xs)\<^sup>- \<sqsubseteq> (\<alpha>\<^sub>-ys)\<^sup>-"
  using srcdups_bool_prefix 
  by (metis assms(1,2) tsynlen_insert tsynremdups_tsynabs)


lemma tsynremdups_snth_stake_inf: "#\<^sub>-s = \<infinity> \<Longrightarrow> snth n (s\<^sup>-) \<noteq> snth (Suc n) (s\<^sup>-)
       \<Longrightarrow> srcdups\<cdot>(stake (Suc n)\<cdot>(s\<^sup>-)) \<noteq> (\<alpha>\<^sub>-s)\<^sup>-" 
  by (simp add: tsynlen_insert tsynremdups_tsynabs srcdups_snth_stake_inf)

lemma tsynremdups_sfoot:
  "s\<^sup>- \<noteq> \<epsilon> \<Longrightarrow> #s < \<infinity> \<Longrightarrow> sfoot (tsynRemDups\<cdot>s)\<^sup>- = sfoot (s\<^sup>-)"
  by (metis inf_ub leD order_neq_le_trans srcdups_sfoot tsynabs_slen
      tsynremdups_tsynabs)

lemma tsynremdups_dom [simp]: "tsynValues\<cdot>(tsynRemDups\<cdot>xs) = tsynValues\<cdot>xs"
  by (simp add: tsynabs_tsyndom tsynremdups_tsynabs) 

lemma tsynremdups_sconc_duplicates:
  assumes "#xs < \<infinity>" and "xs \<noteq> \<epsilon>" and "(tsynRemDups\<cdot>xs)\<^sup>- = (tsynRemDups\<cdot>(xs \<Zcat> ys))\<^sup>-"
  shows "tsynValues\<cdot>ys \<subseteq> {sfoot (xs\<^sup>-)}"
  by (metis (no_types, lifting) Un_upper2 assms(1,3) inf_ub leD order_neq_le_trans srcdups_sconc_duplicates
      subset_empty subset_singleton_iff svalues_eps tsynabs_sconc tsynabs_slen tsynabs_tsyndom tsyndom_sconc
      tsynremdups_dom tsynremdups_tsynabs)

lemma tsynlen_stake_step_msg: "stake 1\<cdot>(sdrop i\<cdot>s) = \<up>(TSynMsg aa) \<Longrightarrow> #\<^sub>-(stake (Suc i)\<cdot>s) = lnsuc\<cdot>(#\<^sub>-(stake i\<cdot>s))"
  by (metis One_nat_def Suc_def2 slen_lnsuc slen_stake_fin stake_add tsynabs_end_msg tsynlen_insert)

lemma tsynremdups_split:
  assumes "#\<^sub>-(tsynRemDups\<cdot>s) < \<infinity>" and "#\<^sub>-s = \<infinity>"
  obtains n where "s\<^sup>- = (stake n\<cdot>(s\<^sup>-)) \<Zcat> ((\<up>(snth n (s\<^sup>-)))\<^sup>\<infinity>)"
  using assms 
  by (metis srcdups_split tsynlen_insert tsynremdups_tsynabs)

lemma tsynremdups_tsynlen_leq: " #\<^sub>-(\<alpha>\<^sub>-(\<up>a \<Zcat>s)) \<le>  lnsuc\<cdot>(#\<^sub>-(\<alpha>\<^sub>-s))"
  apply (induct s arbitrary: a rule:tsyn_ind, simp_all)
    apply (rule adm_all) 
    apply (rule admI)
    apply (simp add: contlub_cfun_arg lub_mono2)   
  apply (case_tac a, simp_all add: tsynlen_singleton_msg tsynremdups_sconc_eps tsynlen_singleton_Eps tsynlen_sconc_Eps)
   apply (case_tac a, simp_all add:  tsynremdups_sconc_eps tsynlen_sconc_Eps)
   apply (case_tac "m=aa", simp_all add: tsynremdups_tsynlen_msg_eq tsynlen_sconc_Eps)
   apply (simp add: tsynremdups_msg_neq tsynlen_sconc_msg)
  apply (case_tac a, simp_all add: tsynremdups_sconc_eps tsynlen_sconc_Eps)
  by (simp add: tsynremdups_tsynlen_msg_Eps tsynlen_sconc_Eps)

lemma tsynremdups_tsynlen_mono: "#\<^sub>-(\<alpha>\<^sub>-s) \<le> #\<^sub>-(\<alpha>\<^sub>-(\<up>a \<Zcat>s))"
  apply (induct s arbitrary: a rule:tsyn_ind, simp_all)
    apply (rule adm_all)    
    apply (subst lnle_def, simp del: lnle_conv; fail)    
  apply (case_tac a, simp_all add: tsynremdups_sconc_eps tsynlen_sconc_Eps)
   apply (case_tac "aa=m", simp_all add: tsynremdups_tsynlen_msg_Eps tsynremdups_msg_eq tsynlen_sconc_Eps)
   apply (simp add: tsynremdups_tsynlen_leq tsynremdups_msg_neq tsynlen_sconc_msg)
  apply (case_tac a, simp_all add: tsynremdups_sconc_eps tsynlen_sconc_Eps)
  by (simp add: tsynremdups_tsynlen_msg_Eps tsynlen_sconc_Eps)

lemma tsynlen_stake_step:
  "#\<^sub>-(stake (Suc i)\<cdot>s) = #\<^sub>-(stake i\<cdot>s) \<or> #\<^sub>-(stake (Suc i)\<cdot>s) = lnsuc\<cdot>(#\<^sub>-(stake i\<cdot>s))"
  apply(case_tac "stake 1\<cdot>(sdrop i\<cdot>s)", simp)
   apply (metis sdrop_stakel1 srt_drop stake2shd stream.sel_rews(2) sup_noteps)
  apply(case_tac "a", simp_all)
   apply (metis One_nat_def sconc_snd_empty sdropl6 sdropostake slen_sup stake_conc_split tsynabs_end_Eps tsynlen_insert)
  apply(subgoal_tac "sa = \<epsilon>", simp)
   apply(subgoal_tac "#\<^sub>-(stake i\<cdot>s \<Zcat> \<up>(TSynMsg aa)) = lnsuc\<cdot>(#\<^sub>-(stake i\<cdot>s))")
    apply (metis One_nat_def stake_conc_split)
   apply(simp add: slen_lnsuc tsynabs_end_msg tsynlen_insert)
  by (metis sdropl6 sdropostake slen_sup)

lemma tsynremdups_proj2_tsynlen_h: "#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(\<up>(TSynMsg m) \<Zcat> s))) \<le> #\<^sub>-(\<alpha>\<^sub>-(\<up>(TSynMsg m) \<Zcat> s))" 
proof -
  have "\<forall> u v a b. #\<^sub>-(sscanlA (\<lambda>s i. apsnd sup' (tsynRemDups_h s i)) (TSynMsg b)\<cdot>(\<Pi>\<^sub>2\<^sub>-s))
       \<le> #\<^sub>-(sscanlA (\<lambda>s i. apsnd sup' (tsynRemDups_h s i)) (TSynMsg (a, b))\<cdot>s)"
    apply auto 
    apply (induct s rule:tsyn_ind, simp_all)
      apply (rule adm_all)+    
      apply (subst lnle_def, simp del: lnle_conv)
      apply (simp add: tsynlen_insert)
    apply (case_tac m) 
    apply (case_tac "(a, b) = m")
      apply (simp_all add: tsynlen_sconc_msg tsynprojsnd_sconc_msg tsynprojsnd_sconc_Eps tsynlen_sconc_Eps)
      using less_lnsuc trans_lnle by blast
    
    thus ?thesis
      apply (cases m)
      apply (simp add: sscanlAOne_def tsynRemDups_def tsynprojsnd_sconc_msg)
      by (simp add: tsynlen_sconc_msg)
  qed

lemma tsynremdups_proj2_tsynlen: "#\<^sub>-(\<alpha>\<^sub>-y) \<ge> #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))"
  apply (induct y rule: tsyn_ind, simp_all)
  apply (subst lnle_def, simp del: lnle_conv; fail)
  apply (simp add: tsynremdups_proj2_tsynlen_h)
  by (simp add: tsynlen_sconc_Eps tsynprojsnd_sconc_Eps tsynremdups_sconc_eps)

lemma proj1_tsynremdups_proj2_tsynlen: "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))"
  by (simp add: tsynprojfst_tsynlen tsynremdups_proj2_tsynlen)

lemma
  fixes y :: "(nat \<times> bool) tsyn stream"
  defines "y \<equiv> <[ TSynMsg (1, True), TSynMsg (2, True), TSynMsg (3, False) ]>"
  shows   "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) > #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))"
proof -
  have "\<alpha>\<^sub>- y = y" by (simp add: y_def tsynremdups_unfold)  
  moreover have "\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>- y) = <[ TSynMsg True,  \<sim>, TSynMsg False ]>"
    apply (simp add: y_def tsynremdups_unfold tsynprojsnd_sconc_msg) 
    by (simp add: tsynprojsnd_singleton_msg)
  ultimately show ?thesis
    by (simp add: y_def tsynlen_sconc_msg tsynlen_singleton_msg tsynprojfst_singleton_msg 
        tsynprojfst_sconc_msg tsynlen_sconc_Eps) 
qed

lemma
  fixes y :: "(nat \<times> bool) tsyn stream"
  defines "y \<equiv> <[ TSynMsg (1, True), TSynMsg (2, False), TSynMsg (3, True) ]>"
  shows   "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))"
  apply (simp add: y_def tsynremdups_unfold tsynprojsnd_sconc_msg 
        tsynprojfst_singleton_msg tsynprojsnd_singleton_msg tsynprojfst_sconc_msg)
  by (simp add: tsynlen_sconc_msg tsynlen_singleton_msg)


lemma tsynlen_tsynremdups_filter_mono:
  "#\<^sub>-(\<alpha>\<^sub>-(A \<ominus>\<^sub>- s)) \<le> #\<^sub>-(\<alpha>\<^sub>- s)" 
  by (simp add: tsynremdups_tsynabs tsynfilter_tsynabs slen_srcdups_filter_mono  tsynlen_insert)

lemma tsynlen_remdups_boolfilter_leq: " #\<^sub>-(\<alpha>\<^sub>-y) \<ge> #\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora))"
  apply (simp add: tsynlen_insert tsynremdups_tsynabs tsynboolfilter_tsynabs)
  using slen_srcdups_sboolfilter_leq 
  by blast

lemma  " #\<^sub>-(\<up>(TSynMsg (1::nat))) > #\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>(\<up>(TSynMsg (1::nat)))\<cdot>(\<up>False)))"
  by (simp add: tsynboolfilter_single_false tsynlen_insert)
lemma  " #\<^sub>-(\<up>(TSynMsg (1::nat))) = #\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>(\<up>(TSynMsg (1::nat)))\<cdot>(\<up>True)))"
  by (simp add: tsynboolfilter_single_true tsynlen_insert)

lemma tsynprojfst_tsynremdups_tsynbolfilter_id_if_fin_len_tsynabs_eq:
  "#(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y))\<^sup>- \<noteq> \<infinity> \<Longrightarrow>
   #(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y))\<^sup>- = #(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))\<^sup>- \<Longrightarrow>
  #(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))\<^sup>- = #(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora)))\<^sup>- \<Longrightarrow>
   (\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y))\<^sup>- = (\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora)))\<^sup>-"
  by (metis (no_types, lifting) sprojfst_srcdups_sboolfilter_id_if_fin_len_eq tsynboolfilter_tsynabs tsynprojfst_tsynabs
      tsynprojsnd_tsynabs tsynremdups_tsynabs)

lemma tsynprojfst_tsynremdups_tsynbolfilter_id_if_fin_tsynlen_eq:
  "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) < \<infinity> \<Longrightarrow>
   #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) \<Longrightarrow>
   #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora))) \<Longrightarrow>
   (\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y))\<^sup>- = (\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora)))\<^sup>-"
  by (metis tsynprojfst_tsynremdups_tsynbolfilter_id_if_fin_len_tsynabs_eq order_less_le tsynlen_insert)

lemma assumes "y=<[TSynMsg (1,True), TSynMsg (1,True)]>" and "ora = <[False, True]> \<Zcat> (sinftimes (\<up>True))" 
  shows "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora))) = #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) \<Longrightarrow> \<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora)) \<noteq> \<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)"  
  using assms
  apply (simp add: tsynboolfilter_lemmas tsynremdups_sconc_eps tsynprojfst_sconc_Eps tsynprojfst_sconc_msg
   tsynremdups_step sscanlAOne_def tsynlen_sconc_Eps tsynlen_sconc_msg tsynprojfst_singleton_msg tsynprojfst_singleton_Eps)
  using tsynlen_singleton_msg tsynlen_singleton_Eps inject_scons by blast

lemma "y=<[TSynMsg (1::nat), TSynMsg 2]> \<Longrightarrow> ora = <[False, True]> \<Zcat> (sinftimes (\<up>True))
        \<Longrightarrow> \<not>(((\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora))\<^sup>-) \<sqsubseteq> ((\<alpha>\<^sub>-y))\<^sup>-)"
  by (simp add: tsynboolfilter_lemmas tsynremdups_sconc_eps tsynRemDups_def sscanlAOne_def tsynprojfst_sconc_Eps tsynprojfst_sconc_msg)

lemma
  tsynRemDups_h_intro_inj_f_eps_msg:
  assumes f_inj: "inj f"
    and f_eps: "f \<sim> = \<sim>"
  shows "tsynRemDups_h \<sim> (f (TSynMsg x)) = ((f (TSynMsg x)), f (TSynMsg x))"
  apply(subgoal_tac "\<exists>v. f (TSynMsg x) = TSynMsg v", erule exE, simp)
  by (metis f_eps f_inj inj_def not_Eps_eq)

lemma
  tsynRemDups_h_intro_inj_f_msg_msg1:
  assumes f_inj: "inj f"
    and f_eps: "f \<sim> = \<sim>"
  shows "tsynRemDups_h (f (TSynMsg x)) (f (TSynMsg x)) = ((f (TSynMsg x)), \<sim>)"
  apply(subgoal_tac "\<exists>v. f (TSynMsg x) = TSynMsg v", erule exE, simp)
  by (metis f_eps f_inj inj_def not_Eps_eq)

lemma
  tsynRemDups_h_intro_inj_f_msg_msg2:
  assumes f_inj: "inj f"
    and f_eps: "f \<sim> = \<sim>"
    and neq: "x \<noteq> y"
  shows "tsynRemDups_h (f (TSynMsg x)) (f (TSynMsg y)) = ((f (TSynMsg y)), (f (TSynMsg y)))"
  apply(subgoal_tac "\<exists>vx. f (TSynMsg x) = TSynMsg vx", erule exE)
   apply(subgoal_tac "\<exists>vy. f (TSynMsg y) = TSynMsg vy", erule exE)
  apply(simp, metis TSynDatatype.tsyn.inject f_inj inj_eq neq)
  by (metis f_eps f_inj inj_def not_Eps_eq)+

lemma
  tsynRemDups_smap:
  assumes f_inj: "inj f"
    and f_eps: "f \<sim> = \<sim>"
  shows "smap f\<cdot>(tsynRemDups\<cdot>s) = tsynRemDups\<cdot>(smap f\<cdot>s)"
proof -
  have f_inj_cp: "\<And>x y. x \<noteq> y \<Longrightarrow> f x \<noteq> f y"
    apply(insert f_inj, simp add: inj_def)
    by blast

  have "\<And>a. smap f\<cdot>(sscanlAOne tsynRemDups_h a\<cdot>s) = sscanlAOne tsynRemDups_h (f a)\<cdot>(smap f\<cdot>s)"
  proof (induction s arbitrary: a)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by(simp add: sscanlAOne_def)
  next
    case IH: (step b s)
    show ?case
      apply(simp add: sscanlaone_step)
      apply(case_tac b, simp add: IH f_eps)
      apply(case_tac a, simp add: IH f_eps)
       apply(case_tac "a = b", simp)
        apply(simp add: IH f_eps tsynRemDups_h_intro_inj_f_eps_msg[OF assms])
      apply(simp add: IH f_eps tsynRemDups_h_intro_inj_f_eps_msg[OF assms]
          tsynRemDups_h_intro_inj_f_msg_msg1[OF assms])
      by(simp add: tsynRemDups_h_intro_inj_f_msg_msg2[OF assms])
  qed

  thus ?thesis
    by(simp add: tsynRemDups_def f_eps)
qed

lemma
  tsynremdups_tsynlen_smap_leq:
  assumes f_eps: "f \<sim> = \<sim>"
    and f_msg: "\<And>x. f (TSynMsg x) \<noteq> \<sim>"
  shows "#\<^sub>-(\<alpha>\<^sub>-(smap f\<cdot>s)) \<le> #\<^sub>-(\<alpha>\<^sub>-s)"
proof -
  have "\<And>a. #\<^sub>-(sscanlAOne tsynRemDups_h (f a)\<cdot>(smap f\<cdot>s)) \<le> #\<^sub>-(sscanlAOne tsynRemDups_h a\<cdot>s)"
  proof(induction s arbitrary: a)
    case adm
    then show ?case
      apply(rule adm_all)
      apply (subst lnle_def)
      apply (rule adm_below)
      by (simp_all)
  next
    case bottom
    then show ?case
      by (simp add: sscanlAOne_def)
  next
    have 1: "\<And>x. tsynRemDups_h \<sim> (f (TSynMsg x)) = (f (TSynMsg x), (f (TSynMsg x)))"
      by (metis tsynRemDups_h.elims)

    have 2: "\<And>x. tsynRemDups_h (f (TSynMsg x)) (f (TSynMsg x)) = ((f (TSynMsg x)), \<sim>)"
      by (metis tsynRemDups_h.elims)

    case (step b s)
    then show ?case
      apply (simp add: sscanlaone_step)
      apply(case_tac b, simp add: f_eps tsynlen_sconc_Eps)
      apply(case_tac a, simp add: f_eps tsynlen_sconc_Eps 1)
       apply (metis tsynRemDups_h.elims f_msg lnsuc_lnle_emb tsynlen_sconc_msg)
      apply(case_tac "a = b", simp add: 2 tsynlen_sconc_Eps)
      apply(case_tac "(f a) = (f b)", simp add: 2 tsynlen_sconc_Eps)
       apply (metis (no_types, lifting) less_lnsuc trans_lnle tsynlen_sconc_msg)
      apply(simp add: 2 tsynlen_sconc_Eps)
      by (metis (no_types, lifting) tsynRemDups_h.elims f_msg lnsuc_lnle_emb split_pairs2 tsynlen_sconc_msg)

  qed

  thus ?thesis
    apply(simp add: tsynRemDups_def)
    by (metis f_eps)
qed


lemma tsyn_stake_inf:"\<exists>y::'a tsyn stream. stake i\<cdot>s \<sqsubseteq> y \<and> #y = \<infinity> \<and> #\<^sub>-y < \<infinity>"
  apply(rule_tac x="(stake i\<cdot>s)\<Zcat>((\<up>Eps)\<^sup>\<infinity>)" in exI)
  apply auto  
   apply (simp add: slen_sconc_snd_inf)
  apply(induction i arbitrary: s,simp_all)
  apply(case_tac s;simp)
  apply(case_tac a;simp)
  apply(simp add: tsynlen_sconc_Eps)
  by(simp add: tsynlen_sconc_msg)

lemma tsyn_abp_adm:
  assumes "P \<equiv> \<lambda>x. (f\<cdot>x)\<^sup>- = x\<^sup>-"
  and "\<And>s. (#s = \<infinity> \<and> #\<^sub>-s < \<infinity>) \<Longrightarrow> P s"
  and "\<And>s.  #\<^sub>-s = \<infinity> \<Longrightarrow> #\<^sub>-(f\<cdot>s) = \<infinity>"
shows "#s = \<infinity> \<Longrightarrow> P s "
  using assms(2)
  apply(simp add: assms(1))
  apply(cases "tsynLen\<cdot>s = \<infinity>") defer
  using tsynlen_not_inf_eq_inf apply blast
   apply(subgoal_tac "chain(\<lambda>i. stake i\<cdot>s)")
    apply(subgoal_tac "(f\<cdot>(\<Squnion>x. stake x\<cdot>s))\<^sup>- \<sqsubseteq> (\<Squnion>x. stake x\<cdot>s)\<^sup>-")
      apply auto
     apply(subgoal_tac "(\<Squnion>x. stake x\<cdot>s) = s")
      apply simp
  using assms(3) 
  using eq_tsynlen_eq_and_less apply metis
  using stream.reach apply blast
  apply(rule admD,simp_all)
proof(rule ccontr)
  fix i
  assume a2:"(\<And>s. #s = \<infinity> \<and> #\<^sub>-s < \<infinity> \<Longrightarrow> (f\<cdot>s)\<^sup>- = s\<^sup>-)"
  assume a4:"(f\<cdot>(stake i\<cdot>s))\<^sup>- \<notsqsubseteq> (stake i\<cdot>s)\<^sup>-"
  then obtain y where y_def:" y = stake i\<cdot>s\<Zcat>((\<up>Eps)\<^sup>\<infinity>)"
    by blast
  have y_len:"#y = \<infinity> \<and> #\<^sub>-y < \<infinity>"
    apply(simp add: y_def)
   apply auto  
   apply (simp add: slen_sconc_snd_inf)
    apply(induction i arbitrary: s,simp_all)
  apply(case_tac s;simp)
  apply(case_tac a;simp)
  apply(simp add: tsynlen_sconc_Eps)
  by(simp add: tsynlen_sconc_msg)
  then have "(f\<cdot>(stake i\<cdot>s))\<^sup>- \<sqsubseteq> (y)\<^sup>-"
    using a2 y_def 
    by (metis monofun_cfun_arg sconc_prefix)
  then have "(stake i\<cdot>s)\<^sup>-  \<sqsubseteq> (f\<cdot>(stake i\<cdot>s))\<^sup>-" 
    using a4 monofun_cfun_arg stream_order_pre_total y_def y_len sconc_prefix by blast
  then obtain rt where rt_def:"(stake i\<cdot>s)\<^sup>- \<Zcat> rt = (f\<cdot>(stake i\<cdot>s))\<^sup>- \<and> rt\<noteq> \<epsilon>" 
    using approxl3 a4 by (metis sconc_snd_empty) 
  then have "(stake i\<cdot>s)\<^sup>- \<Zcat> rt \<sqsubseteq> (y)\<^sup>-" 
    using \<open>(f\<cdot>(stake i\<cdot>s))\<^sup>- \<sqsubseteq> y\<^sup>-\<close> by presburger
  then show "False"
    apply(simp add: y_def)
    apply(subgoal_tac "((stake i\<cdot>s \<Zcat> (\<up>\<sim>\<^sup>\<infinity>))\<^sup>-) = ((stake i\<cdot>s)\<^sup>-) ")
     apply (simp add: a4 rt_def)
    apply(subst tsynabs_sconc) 
     apply (simp add: lnless_def)
    by simp
qed


lemma weak_mono2cont:
  fixes spf :: "'in::countable tsyn stream \<Rightarrow> 'out::countable tsyn stream"
  assumes weak: "\<And>i. #\<^sub>\<surd> i \<le> #\<^sub>\<surd> (spf i)" and mono: "monofun spf"
  shows "cont spf"
  using weak_len_mono2cont tlen_len_stream by (metis mono tlen_tsyn.elims weak)

definition snthTsyn :: "nat \<Rightarrow> 'a tsyn stream \<rightarrow> 'a stream" where
"snthTsyn n \<equiv> tsyn2ustream oo (tsnth n)"

fun tsyn2eventElem :: "'a tsyn \<Rightarrow> 'a event stream" where
"tsyn2eventElem (TSynMsg m) = updis (EventMsg m) && \<up>Tick" |
"tsyn2eventElem Eps = \<up>Tick"

definition tsyn2event::"'a tsyn stream \<rightarrow> 'a event stream" where
"tsyn2event \<equiv> smapAlt tsyn2eventElem"


definition tsyntakewhile::"('a \<Rightarrow> bool) \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
"tsyntakewhile f = stakewhile (case_tsyn f True)"

definition tsyntwbl::"('a \<Rightarrow> bool) \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
"tsyntwbl f = stwbl (case_tsyn f True)"

definition tsyndropwhile::"('a \<Rightarrow> bool) \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
"tsyndropwhile f = sdropwhile (case_tsyn f True)"

definition tsynrtdw::"('a \<Rightarrow> bool) \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
"tsynrtdw f = srtdw (case_tsyn f True)"


lemma
  tsynboolfilter_inf_Eps_suffix:
  assumes "#s \<noteq> \<infinity>"
    and "#ora = \<infinity>"
  shows "tsynBoolFilter\<cdot>(s \<Zcat> ((\<up>\<sim>)\<^sup>\<infinity>))\<cdot>ora = tsynBoolFilter\<cdot>s\<cdot>ora \<Zcat> ((\<up>\<sim>)\<^sup>\<infinity>)"
  apply(insert assms)
  apply(induct s arbitrary: ora, auto)
   apply(rule admI)
   apply (metis inf_chainl4 l42)
  apply(case_tac ora, auto)
  apply(case_tac aa, simp_all)
  apply (metis (no_types, opaque_lifting) assoc_sconc not_Eps_eq slen_sconc_snd_inf tsynboolfilter_Eps_bool_rec tsynboolfilter_refold)
  by (metis (no_types, lifting) assoc_sconc slen_sconc_snd_inf tsyn2eventElem.cases tsynboolfilter_Eps_bool_rec tsynboolfilter_msg_false_rec)

lemma
  tsynboolfilter_sdrop:
  assumes "Fin e = #\<^sub>-(stake n\<cdot>input)"
  shows "sdrop n\<cdot>(tsynBoolFilter\<cdot>input\<cdot>ora) = tsynBoolFilter\<cdot>(sdrop n\<cdot>input)\<cdot>(sdrop e\<cdot>ora)"
  using assms apply(induction n arbitrary: e, simp)
proof-
  fix n e
  assume IH: "\<And>e. Fin e = #\<^sub>-(stake n\<cdot>input) \<Longrightarrow> sdrop n\<cdot>(tsynBoolFilter\<cdot>input\<cdot>ora) = tsynBoolFilter\<cdot>(sdrop n\<cdot>input)\<cdot>(sdrop e\<cdot>ora)"
  assume e_def: "Fin e = #\<^sub>-(stake (Suc n)\<cdot>input)"

  obtain e' where e'_def: "Fin e' = #\<^sub>-(stake n\<cdot>input)"
    by (metis LNat.LNat.lnat.exhaust slen_stake_fin tsynEps_tsynEps2slen_infinite_msg)

  have e_rel_e': "e = e' \<or> e = Suc e'"
    using e_def e'_def tsynlen_stake_step
    by (metis Fin_Suc inject_Fin)

  then have e'_leq_e: "e' \<le> e"
    by auto

  show "sdrop (Suc n)\<cdot>(tsynBoolFilter\<cdot>input\<cdot>ora) = tsynBoolFilter\<cdot>(sdrop (Suc n)\<cdot>input)\<cdot>(sdrop e\<cdot>ora)"
    apply(subst sdrop_back_rt)
    apply(subst IH[OF e'_def])
    apply(case_tac "sdrop n\<cdot>input", auto)
     apply (metis (no_types, lifting) srt_drop strict_sdrop tsynboolfilter_strict(3))
    apply(case_tac "sdrop e'\<cdot>ora", auto)
     apply (metis e'_leq_e sconc_fst_empty sconc_snd_empty sdropl5 strictI tsynboolfilter_strict(2))
    apply(case_tac a, auto simp add: tsynboolfilter_Eps_bool_rec)
    apply (metis LNat.lnat.inject One_nat_def e'_def e_def slen_sup srt_drop srt_supconc stake_conc_split stake_prefix2 tsynabs_end_Eps
        tsynlen_insert)
    apply(case_tac aa, auto simp add: tsynboolfilter_msg_false_rec tsynboolfilter_msg_true_rec)
     apply(subgoal_tac "e = Suc e'", auto simp add: sdrop_back_rt)
     apply (metis LNat.lnat.inject One_nat_def e'_def e_def lnat_fin4 slen_sup stake_prefix2 tsynlen_stake_step_msg)
    apply(subgoal_tac "e = Suc e'", auto simp add: sdrop_back_rt)
    by(metis LNat.lnat.inject One_nat_def e'_def e_def lnat_fin4 slen_sup stake_prefix2 tsynlen_stake_step_msg)
qed


lemma tsynBoolFilter_intro_snth:
  assumes "\<And>i. snth i output \<in> {\<sim>, snth i input}"
    and "#({(x, y) . x \<noteq> \<sim> \<and> x = y } \<ominus> szip\<cdot>input\<cdot>output) = \<infinity>"
  shows "\<exists>ora. #({True} \<ominus> ora) = \<infinity> \<and> output = tsynBoolFilter\<cdot>input\<cdot>ora"
proof-
  define ora where "ora = smap (\<lambda>(x, y). x = y)\<cdot>({(x, y) . x \<noteq> \<sim>} \<ominus> szip\<cdot>input\<cdot>output)"

  have output_inf: "#output = \<infinity>"
    and input_inf: "#input = \<infinity>"
    by (metis (no_types, lifting) assms(2) szip_len[of "input" "output"] min.commute min.left_idem minf_inf2 sfilterl4)+

  then have szip_inf: "#(szip\<cdot>input\<cdot>output) = \<infinity>"
    by simp

  have in_out_len: "#input = #output"
    by (simp add: output_inf input_inf)

  have out_eps_if_in_eps: "\<And>i. snth i input = \<sim> \<Longrightarrow> snth i output = \<sim>"
    by (metis assms(1) insert_absorb2 singleton_iff)

  have filter_subsets: "{(x, y) . x \<noteq> \<sim> \<and> x = y } \<subseteq> {(x, y) . x \<noteq> \<sim> }"
    by blast

  have szip_filtered_inf: "#({(x, y) . x \<noteq> \<sim> } \<ominus> szip\<cdot>input\<cdot>output) = \<infinity>"
    by (metis (mono_tags, lifting) assms(2) filter_subsets inf_less_eq sfilter_subset_len)

  have ora_inf: "#ora = \<infinity>"
    by(simp add: ora_def szip_filtered_inf[simplified])


  have live_h2: "\<And>i. \<exists>j\<ge>i. snth j (szip\<cdot>input\<cdot>output) \<in> {(x, y) . x \<noteq> \<sim> \<and> x = y }"
    using assms(2) sfilter_inf_snthI by blast
  then have "\<And>i. \<exists>j\<ge>i. snth j ({(x, y) . x \<noteq> \<sim> \<and> x = y } \<ominus> szip\<cdot>input\<cdot>output) \<in> {(x, y) . x \<noteq> \<sim> \<and> x = y }"
    using snth_sfilter_ex3[OF szip_inf] by presburger
  then have "\<And>i. \<exists>j\<ge>i. snth j ({(x, y) . x \<noteq> \<sim> } \<ominus> szip\<cdot>input\<cdot>output) \<in> {(x, y) . x \<noteq> \<sim> \<and> x = y }"
    using snth_sfilter_ex3_subset filter_subsets assms(2) by blast
  then have "\<And>i. \<exists>j\<ge>i. snth j (smap (\<lambda>m. m \<in> {(x, y) . x \<noteq> \<sim> \<and> x = y })\<cdot>({(x, y) . x \<noteq> \<sim> } \<ominus> szip\<cdot>input\<cdot>output))"
    apply(subst smap_snth_in[symmetric])
    using fin_le_inf szip_filtered_inf apply presburger
    by simp
  then have live_h3: "\<And>i. \<exists>j\<ge>i. snth j (smap (\<lambda>(x, y). x \<noteq> \<sim> \<and> x = y)\<cdot>({(x, y) . x \<noteq> \<sim> } \<ominus> szip\<cdot>input\<cdot>output))"
    by simp
  
  have live_h: "\<And>i. \<exists>j\<ge>i. snth j (smap (\<lambda>(x, y). x = y)\<cdot>({(x, y) . x \<noteq> \<sim> } \<ominus> szip\<cdot>input\<cdot>output))"
  proof-
    fix i
    obtain j where ij: "j\<ge>i" and "snth j (smap (\<lambda>(x, y). x \<noteq> \<sim> \<and> x = y)\<cdot>({(x, y) . x \<noteq> \<sim> } \<ominus> szip\<cdot>input\<cdot>output))"
      using live_h3 by blast
    then have "snth j (smap (\<lambda>(x, y). x = y)\<cdot>({(x, y) . x \<noteq> \<sim> } \<ominus> szip\<cdot>input\<cdot>output))"
      by (metis (no_types, lifting) fin_le_inf smap_snth_lemma split_beta szip_filtered_inf)
    thus "\<exists>j\<ge>i. snth j (smap (\<lambda>(x, y). x = y)\<cdot>({(x, y). x \<noteq> \<sim>} \<ominus> szip\<cdot>input\<cdot>output))"
      apply(rule_tac x="j" in exI)
      using ij by fastforce
  qed

  have live: "#({True} \<ominus> ora) = \<infinity>"
      apply(subst ora_def)
      apply(rule sfilter_inf_snthE)
      using ora_def ora_inf apply blast
      using live_h by simp

  have shd_input_shd_zip: "\<exists>m. shd input = TSynMsg m \<longrightarrow> (\<exists>x. shd (szip\<cdot>input\<cdot>output) = (TSynMsg m, x))"
    by (metis Inf'_neq_0 input_inf output_inf slen_sprojfst slen_zero split_pairs2 sprojfst_shd sprojfst_szipl1)

  have shd_input_shd_zip2: "\<exists>m n . shd input = TSynMsg m \<longrightarrow> shd output = TSynMsg n \<longrightarrow> shd (szip\<cdot>input\<cdot>output) = (TSynMsg m, TSynMsg n)"
    by (metis Inf'_neq_0 Stream.slen_empty_eq input_inf output_inf shd_input_shd_zip snd_conv sprojsnd_shd sprojsnd_szipl1 strict_rev_szip)

  have shd_ora_eq: "shd input \<noteq> \<sim> \<Longrightarrow> shd ora = (shd input = shd output)"
    apply(simp add: ora_def)
    apply(subst smap_hd_rst)
     apply(rule shd_filter, simp add: input_inf output_inf, simp)
    using shd_input_shd_zip
     apply (metis (mono_tags, lifting) Inf'_neq_0 assms(2) case_prodI2 output_inf sfilterl4 slen_zero split_pairs2 sprojfst_shd sprojfst_szipl1)
    apply auto
     apply (smt case_prod_beta inf_scase input_inf mem_Collect_eq output_inf sfilter_in shd1 split_pairs2 szip_scons)
  proof-
    fix y a b
    assume a1: "shd output = TSynMsg y"
    assume a2: "shd input = TSynMsg y"
    assume a3: "shd ({(x::'a tsyn, y::'a tsyn). \<exists>y::'a. x = TSynMsg y} \<ominus> szip\<cdot>input\<cdot>output) = (a, b)"

    have "shd ({(x::'a tsyn, y::'a tsyn). \<exists>y::'a. x = TSynMsg y} \<ominus> szip\<cdot>input\<cdot>output) = shd (szip\<cdot>input\<cdot>output)"
      apply(rule shd_filter_shd)
       apply(simp add: input_inf output_inf)
      apply(subst snth_shd[symmetric])
      apply(subst szip_nth)
      by(simp_all add: input_inf output_inf a2)

    then have 1: "shd (szip\<cdot>input\<cdot>output) = (a, b)"
      using a3 by simp

    then have a_eq: "a = shd input"
      by (metis Inf'_neq_0_rev Stream.slen_empty_eq fst_eqD input_inf output_inf sprojfst_shd sprojfst_szipl1 strict_rev_szip)
    have b_eq: "b = shd output"
      by (metis Inf'_neq_0_rev Stream.slen_empty_eq 1 input_inf output_inf snd_eqD sprojsnd_shd sprojsnd_szipl1 strict_rev_szip)

    show "a = b"
      by(simp add: a_eq b_eq a1 a2)
  qed


  have input_tlen_inf: "#\<^sub>-input = \<infinity>"
  proof-
    have "\<And>i. \<exists>j\<ge>i. snth j (szip\<cdot>(input)\<cdot>(output)) \<in> {(x, y). (\<exists>y. x = TSynMsg y) \<and> x = y}"
      using szip_sproj sfilter_inf_snthI[OF assms(2)[simplified]] by simp
    then have "\<And>i. \<exists>j\<ge>i. snth j (szip\<cdot>(input)\<cdot>(output)) \<in> {(x, y). (\<exists>y. x = TSynMsg y)}"
      by fastforce
    then have "\<And>i. \<exists>j\<ge>i. fst (snth j (szip\<cdot>(input)\<cdot>(output))) \<in> {x. (\<exists>y. x = TSynMsg y)}"
      by force
    then have "\<And>i. \<exists>j\<ge>i. (snth j (sprojfst\<cdot>(szip\<cdot>(input)\<cdot>(output)))) \<in> {x. (\<exists>y. x = TSynMsg y)}"
      using szip_inf by force
    then have 1: "\<And>i. \<exists>j\<ge>i. snth j input \<in> {x. (\<exists>y. x = TSynMsg y)}"
      by (simp add: output_inf sprojfst_szipl1)

    show ?thesis
      apply(simp add: tsynlen_insert tsyn2ustream_def)
      apply(rule sfilter_inf_snthE, simp add: input_inf, simp)
      using 1 by simp
  qed

  have ia: "shd output = shd (tsynBoolFilter\<cdot>input\<cdot>ora)"
    apply(case_tac "shd input = \<sim>")
     apply auto
     apply (metis assms(1) empty_iff inf_scase input_inf insert_iff ora_inf shd1 snth_shd tsynboolfilter_Eps_bool_rec)
    apply(case_tac "shd output", auto)
    using shd_ora_eq apply (metis (full_types) Inf'_neq_0_rev input_inf ora_inf shd1 slen_zero surj_scons tsyn.simps(3) tsynboolfilter_msg_false_rec)
    apply(subgoal_tac "y = a")
    using shd_ora_eq apply (smt Inf'_neq_0_rev input_inf ora_inf shd1 slen_zero surj_scons tsyn.simps(3) tsynboolfilter_refold)
    by (metis assms(1) empty_iff insert_iff snth_shd tsyn.simps(3) tsyn2ustreamElem.simps(2))

  have strengthen: "(\<forall>n. snth n output = snth n (tsynBoolFilter\<cdot>input\<cdot>ora)) = (\<forall>n j. j \<le> n \<longrightarrow> snth j output = snth j (tsynBoolFilter\<cdot>input\<cdot>ora))"
    by blast

  have iS: "\<And>n. (\<forall>j\<le>n. snth j output = snth j (tsynBoolFilter\<cdot>input\<cdot>ora)) \<Longrightarrow> (\<forall>j\<le>Suc n. snth j output = snth j (tsynBoolFilter\<cdot>input\<cdot>ora))"
  proof-
    fix n
    assume a: "\<forall>j\<le>n. snth j output = snth j (tsynBoolFilter\<cdot>input\<cdot>ora)"

    have out_pref_eq: "stake (Suc n)\<cdot>output = stake (Suc n)\<cdot>(tsynBoolFilter\<cdot>input\<cdot>ora)"
      apply(rule snths_eq)
       apply (auto simp add: in_out_len ora_inf output_inf slen_stake_fst_inf slen_tsynboolfilter)
      by(simp add: a)

    then have tbf_split: "tsynBoolFilter\<cdot>input\<cdot>ora = stake (Suc n)\<cdot>output \<Zcat> (sdrop (Suc n)\<cdot>(tsynBoolFilter\<cdot>input\<cdot>ora))"
      by simp

    have "tsynBoolFilter\<cdot>input\<cdot>ora = stake (Suc n)\<cdot>(tsynBoolFilter\<cdot>input\<cdot>ora) \<Zcat> \<up>(snth (Suc n) (tsynBoolFilter\<cdot>input\<cdot>ora)) \<Zcat> (sdrop (Suc (Suc n))\<cdot>(tsynBoolFilter\<cdot>input\<cdot>ora))"
      apply(rule split_stream_snth)
      by (simp add: input_inf ora_inf slen_tsynboolfilter)

    then have "tsynBoolFilter\<cdot>input\<cdot>ora = stake (Suc n)\<cdot>output \<Zcat> \<up>(snth (Suc n) (tsynBoolFilter\<cdot>input\<cdot>ora)) \<Zcat> (sdrop (Suc (Suc n))\<cdot>(tsynBoolFilter\<cdot>input\<cdot>ora))"
      by(simp add: out_pref_eq[symmetric])



    have case_2: "\<And>m. snth (Suc n) input = TSynMsg m \<Longrightarrow> snth (Suc n) output = snth (Suc n) (tsynBoolFilter\<cdot>input\<cdot>ora)"
    proof-
      fix m
      assume a1: "snth (Suc n) input = TSynMsg m"

      define t where "t = snth (Suc n) output"

      obtain irt where sdrop_input_eq: "sdrop (Suc n)\<cdot>input = \<up>(TSynMsg m) \<Zcat> irt"
        by (metis a1 fin_le_inf input_inf sdrop_snth_split)

      obtain ort where sdrop_output_eq: "sdrop (Suc n)\<cdot>output = \<up>t \<Zcat> ort"
        by (metis t_def fin_le_inf output_inf sdrop_snth_split)

      have zip_suc_n_eq: "snth (Suc n) (szip\<cdot>input\<cdot>output) = (TSynMsg m, t)"
        by (simp add: a1 t_def input_inf output_inf szip_nth)

      obtain e where e_def: "Fin e = #\<^sub>-(stake (Suc n)\<cdot>input)"
        by (metis LNat.LNat.lnat.exhaust slen_stake_fin tsynEps_tsynEps2slen_infinite_msg)


      have snth_e_ora_snth_suc_n: "snth e ({(x, y). \<exists>y. x = TSynMsg y} \<ominus> szip\<cdot>input\<cdot>output) = snth (Suc n) (szip\<cdot>input\<cdot>output)"
        using e_def zip_suc_n_eq
      proof(induct n arbitrary: e)
        case cse: 0
        fix e
        assume a1: "Fin e = #\<^sub>-(stake (Suc 0)\<cdot>input)"
        assume a2: "snth (Suc 0) (szip\<cdot>input\<cdot>output) = (TSynMsg m, t)"

        have 1: "Fin e = #\<^sub>-(\<up>(shd input))"
          using a1 by (metis sdrop_input_eq stake2shd strict_sdrop supconc_neps)
  
        have 2: "shd input = \<sim> \<Longrightarrow> shd (szip\<cdot>input\<cdot>output) \<notin> {(x, y). \<exists>y. x = TSynMsg y}"
          by (smt case_prodD fin_le_inf input_inf mem_Collect_eq not_Msg_eq output_inf snth_shd szip_nth)
  
        have 3: "shd input \<noteq> \<sim> \<Longrightarrow> shd (szip\<cdot>input\<cdot>output) \<in> {(x, y). \<exists>y. x = TSynMsg y}"
          by (smt case_prod_conv fin_le_inf input_inf mem_Collect_eq output_inf snth_shd szip_nth tsyn2ustreamElem.cases)
  
        show "snth e ({(x, y). \<exists>y. x = TSynMsg y} \<ominus> szip\<cdot>input\<cdot>output) = snth (Suc 0) (szip\<cdot>input\<cdot>output)"
          apply(cases "shd input = \<sim>")
           apply(subgoal_tac "Fin e = 0", auto)
          using sfilter_shd_snth_1 2 a2 apply (metis (mono_tags, lifting) case_prodI mem_Collect_eq)
          using 1 apply (simp add: tsynlen_singleton_Eps)
          apply(subgoal_tac "e = 1", auto)
          using sfilter_shd_in_snth_1 3 a2 apply (metis (mono_tags, lifting) case_prodI mem_Collect_eq tsyn.simps(3))
          using 1 by (metis Fin_0 Fin_Suc inject_Fin sconc_snd_empty tsynlen_sconc_msg tsynlen_strict)
      next
        case cse: (Suc n)
        fix e
  
        assume a1: "Fin e = #\<^sub>-(stake (Suc (Suc n))\<cdot>input)"
        assume a2: "snth (Suc (Suc n)) (szip\<cdot>input\<cdot>output) = (TSynMsg m, t)"
  
        have "stake (Suc (Suc n))\<cdot>input = (stake (Suc n)\<cdot>input) \<Zcat> \<up>(snth (Suc n) input)"
          by(simp add: stake_step_last input_inf)
  
        then have 1: "Fin e = #\<^sub>-(stake (Suc n)\<cdot>(input)) + #\<^sub>-(\<up>(snth (Suc n) input))"
          using a1 tsynlen_insert
          by (metis (no_types, lifting) sconc_slen2 slen_stake_fin tsyn2ustream_conc)
  
        have 2: "snth (Suc n) input = \<sim> \<Longrightarrow> snth (Suc n) (szip\<cdot>input\<cdot>output) \<notin> {(x, y). \<exists>y. x = TSynMsg y}"
          by (smt case_prodD fin_le_inf input_inf mem_Collect_eq not_Msg_eq output_inf snth_shd szip_nth)
  
        have 3: "snth (Suc n) input \<noteq> \<sim> \<Longrightarrow> snth (Suc n) (szip\<cdot>input\<cdot>output) \<in> {(x, y). \<exists>y. x = TSynMsg y}"
          by (smt case_prod_conv fin_le_inf input_inf mem_Collect_eq output_inf snth_shd szip_nth tsyn2ustreamElem.cases)
  
        have 4: "#\<^sub>-(stake (Suc n)\<cdot>input) = #({(x, y). \<exists>y. x = TSynMsg y} \<ominus> stake (Suc n)\<cdot>(szip\<cdot>input\<cdot>output))"
        proof-
          have "sprojfst\<cdot>(szip\<cdot>input\<cdot>output) = input"
            using output_inf sprojfst_szipl1 by blast
          then have "stake (Suc n)\<cdot>input = sprojfst\<cdot>(stake (Suc n)\<cdot>(szip\<cdot>input\<cdot>output))"
            by (metis (no_types) sprojfst_sconc slen_sprojfst slen_stake_fst_inf split_streaml1 stake_prefix2 szip_inf)
          then have h1: "#({e. \<exists>y. e = TSynMsg y} \<ominus> stake (Suc n)\<cdot>input) = #({e. \<exists>y. e = TSynMsg y} \<ominus> sprojfst\<cdot>(stake (Suc n)\<cdot>(szip\<cdot>input\<cdot>output)))"
            by argo
  
          have h2: "{(m::'a tsyn, x::'a tsyn). m \<in> {e. \<exists>y. e = TSynMsg y}} = {(x, y). \<exists>m. x = TSynMsg m}"
            by auto
  
          have "#({e. \<exists>y. e = TSynMsg y} \<ominus> stake (Suc n)\<cdot>input) = #({(x, y). \<exists>m. x = TSynMsg m} \<ominus> stake (Suc n)\<cdot>(szip\<cdot>input\<cdot>output))"
            using h1 h2 sfilter_tpl_sprojfst[of "{e::'a tsyn. \<exists>y::'a. e = TSynMsg y}" "stake (Suc n)\<cdot>(szip\<cdot>input\<cdot>output)"]
              slen_sprojfst[of "{(x, y). x \<in> {e::'a tsyn. \<exists>y::'a. e = TSynMsg y}} \<ominus> stake (Suc n)\<cdot>(szip\<cdot>input\<cdot>output)"]
            by argo
  
          thus ?thesis
            by(simp add: tsynlen_insert tsyn2ustream_def)
        qed
  
        show "snth e ({(x, y). \<exists>y. x = TSynMsg y} \<ominus> szip\<cdot>input\<cdot>output) = snth (Suc (Suc n)) (szip\<cdot>input\<cdot>output)"
          apply(cases "snth (Suc n) input = \<sim>")
           apply(subgoal_tac "Fin e = #\<^sub>-(stake (Suc n)\<cdot>(input))", auto)
            apply(rule sfilter_snth_snth_suc)
          using 4 apply argo
          using 2 apply simp
          using a2 apply simp
          using 1 apply (metis add.right_neutral tsynlen_singleton_Eps)
          apply(rule sfilter_snth_in_snth_suc)
            apply (metis "1" "4" lnat_plus_commu lnat_suc_plus one_lnat_def tsynlen_singleton_msg)
          using "3" apply force
          using a2 by auto
      qed

      have snth_e_ora_eps: "t = \<sim> \<Longrightarrow> \<not>snth e ora"
        apply(simp add: ora_def)
        apply(subst smap_snth_lemma)
        using szip_filtered_inf apply auto[1]
        using snth_e_ora_snth_suc_n by (simp add: zip_suc_n_eq)
      
      have snth_e_ora_msg: "t \<noteq> \<sim> \<Longrightarrow> snth e ora"
        apply(simp add: ora_def)
        apply(subst smap_snth_lemma)
        using szip_filtered_inf apply auto[1]
        using snth_e_ora_snth_suc_n apply(auto simp add: t_def zip_suc_n_eq)
        by (metis a1 assms(1) insert_iff not_Eps_eq singleton_iff tsyn.inject)

      show "snth (Suc n) output = snth (Suc n) (tsynBoolFilter\<cdot>input\<cdot>ora)"
        apply(simp add: t_def[symmetric])
        apply(case_tac t)
         apply(subgoal_tac "\<exists>orart. sdrop e\<cdot>ora = \<up>False \<Zcat> orart")
          apply(auto simp add: snth_def tsynboolfilter_sdrop[OF e_def] sdrop_input_eq tsynboolfilter_msg_false_rec)
         apply (metis (full_types) fin_le_inf ora_inf sdrop_snth_split snth_e_ora_eps)
         apply(subgoal_tac "\<exists>orart. sdrop e\<cdot>ora = \<up>True \<Zcat> orart")
          apply(auto simp add: snth_def tsynboolfilter_sdrop[OF e_def] sdrop_input_eq tsynboolfilter_msg_true_rec)
         apply (metis a1 assms(1) empty_iff insert_iff t_def tsyn.inject tsyn.simps(3))
        by (metis (full_types) fin_le_inf ora_inf sdrop_snth_split snth_e_ora_msg tsyn.simps(3))
    qed

    have "snth (Suc n) output = snth (Suc n) (tsynBoolFilter\<cdot>input\<cdot>ora)"
      apply(case_tac "snth (Suc n) input = \<sim>")
       apply auto
       apply(simp add: out_eps_if_in_eps)
       apply(simp add: tsynBoolFilter_def tsynProjFst_def tsynFilter_def smaps2smap)
       apply(subst smap_snth_lemma, simp add: input_inf ora_inf tsynfilter_slen tsynzip_slen)
       apply(subst tsynFst.simps(1)[symmetric], rule arg_cong[of _ _ tsynFst])
       apply(subst tsynFilterElem.simps(1)[symmetric, of "Collect snd"])
       apply(rule arg_cong[of _ _ "tsynFilterElem (Collect snd)"])
       apply(rule tsynZip_snth_eps[symmetric])
         apply(simp add: ora_inf, simp, simp add: input_tlen_inf)
      using case_2 by blast

    thus "\<forall>j\<le>Suc n. snth j output = snth j (tsynBoolFilter\<cdot>input\<cdot>ora)"
      using a le_Suc_eq by presburger
  qed

  have i: "\<And>n. (\<forall> j \<le> n. snth j output = snth j (tsynBoolFilter\<cdot>input\<cdot>ora))"
    apply(induct_tac n)
     apply auto[1]
     apply (rule ia)
    using iS by blast

  show ?thesis
    apply(rule_tac x="ora" in exI)
    apply(rule conjI)
     apply(rule live)
    apply(rule snths_eq)
    apply (simp add: input_inf ora_inf output_inf slen_tsynboolfilter)
    apply (simp add: output_inf)
    apply(subst strengthen)
    apply(auto)
    by (simp add: i)
  qed


end

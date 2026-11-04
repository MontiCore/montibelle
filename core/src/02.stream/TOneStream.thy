theory TOneStream
imports EventStream TsynStream inc.TOneDatatype

begin

definition toneValues :: "'a tone stream \<rightarrow> 'a set" where
"toneValues \<equiv> \<Lambda> s. {m | m. (TOneMsg m) \<in> sValues\<cdot>s}"

definition tone2ustream:: "'a tone stream \<rightarrow> 'a stream" where
"tone2ustream \<equiv> smap inverseTOne"


definition toneMap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tone stream \<rightarrow> 'b tone stream" where
"toneMap f = smap (map_tone f)"

definition toneFilter :: "'a set \<Rightarrow> 'a tone stream \<rightarrow> 'a tone stream" where
"toneFilter F \<equiv> sfilter (TOneMsg`F)"

definition snthTOne :: "nat \<Rightarrow> 'a tone stream \<rightarrow> 'a stream" where
"snthTOne n \<equiv> \<Lambda> s. \<up>(snth n (tone2ustream\<cdot>s))"

fun tone2eventElem :: "'a tone \<Rightarrow> 'a event stream" where
"tone2eventElem (TOneMsg m) = updis (EventMsg m) && \<up>Tick"

definition tone2event::"'a tone stream \<rightarrow> 'a event stream" where
"tone2event \<equiv> smapAlt tone2eventElem"

definition tone2tsyn :: "'a tone stream \<rightarrow> 'a tsyn stream" where
"tone2tsyn \<equiv> smap (TSynMsg o inverseTOne)"

definition tonetakewhile::"('a \<Rightarrow> bool) \<Rightarrow> 'a tone stream \<rightarrow> 'a tone stream" where
"tonetakewhile f = stakewhile (\<lambda>x. f ((inv TOneMsg) x))"

definition tonetwbl::"('a \<Rightarrow> bool) \<Rightarrow> 'a tone stream \<rightarrow> 'a tone stream" where
"tonetwbl f = stwbl (\<lambda>x. f ((inv TOneMsg) x))"

definition tonedropwhile::"('a \<Rightarrow> bool) \<Rightarrow> 'a tone stream \<rightarrow> 'a tone stream" where
"tonedropwhile f = sdropwhile (\<lambda>x. f ((inv TOneMsg) x))"

definition tonertdw::"('a \<Rightarrow> bool) \<Rightarrow> 'a tone stream \<rightarrow> 'a tone stream" where
"tonertdw f = srtdw (\<lambda>x. f ((inv TOneMsg) x))"

definition toneprojFst:: "('a \<times> 'b) tone stream \<rightarrow> 'a tone stream" where
"toneprojFst = toneMap fst"

definition toneprojSnd:: "('a \<times> 'b) tone stream \<rightarrow> 'b tone stream" where
"toneprojSnd = toneMap snd"

definition tonezip::"'a tone stream \<rightarrow> 'b tone stream \<rightarrow> ('a \<times> 'b) tone stream" where
"tonezip = (\<Lambda>  as bs. smap (\<lambda> (a,b). TOneMsg (((inv TOneMsg) a),((inv TOneMsg) b)))\<cdot>(szip\<cdot>as\<cdot>bs))"

definition tonescanl::"('state \<Rightarrow> 'msg \<Rightarrow> 'state \<times> 'o tone stream) \<Rightarrow> 'state \<Rightarrow> 'msg tone stream \<rightarrow> 'o tone stream" where
"tonescanl f = sscanlA (\<lambda>state msg. (f state ((inv TOneMsg) msg)))"


text \<open>@{term toneValues} insertion lemma.\<close>
lemma tonedom_insert: "toneValues\<cdot>s = {m | m. (TOneMsg m) \<in> sValues\<cdot>s}"
  by (metis (no_types) Abs_cfun_inverse2 toneValues_def tsyndom_cont)

text \<open>@{term toneValues} maps the empty stream on the empty set.\<close>
lemma tonedom_strict [simp]: "toneValues\<cdot>\<epsilon> = {}"
  by (simp add: tonedom_insert)


text \<open>@{term toneValues} and sValues only differ by the TOneMsg constructor.\<close>
lemma tonedom_sValues: "TOneMsg ` toneValues\<cdot>s = sValues\<cdot>s"
proof -
    have inv: "\<forall>y \<in> sValues\<cdot>s. \<exists>x. y = TOneMsg x"
      by (meson inverseTOne.cases)

    have "TOneMsg ` toneValues\<cdot>s \<subseteq> sValues\<cdot>s"
      apply(simp add: tonedom_insert)
      by blast
    also have "sValues\<cdot>s \<subseteq> TOneMsg ` toneValues\<cdot>s"
      apply(simp add: tonedom_insert image_def)
      using inv by fastforce
    finally show "TOneMsg ` toneValues\<cdot>s = sValues\<cdot>s"
      by blast
  qed

lemma tonedom_inv_sValues: "toneValues\<cdot>s = (inv TOneMsg) ` sValues\<cdot>s"
  by (metis TOneDatatype.inj_tone image_inv_f_f tonedom_sValues)

lemma tonedom_sValues_tone2ustream: "toneValues\<cdot>s = sValues\<cdot>(tone2ustream\<cdot>s)"
  by(simp add: tone2ustream_def smap_sValues inverseTOne_inv_TOneMsg tonedom_inv_sValues)

end

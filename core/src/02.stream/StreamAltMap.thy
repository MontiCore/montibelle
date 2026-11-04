theory StreamAltMap
imports Stream
begin

definition smapAlt:: "('a \<Rightarrow> 'b stream) \<Rightarrow> 'a stream \<rightarrow> 'b stream" where
"smapAlt f \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                       (f a) \<Zcat> (h\<cdot>(srt\<cdot>s))))"

lemma smapAlt_cont[simp]: "cont (\<lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a.
                       (f a) \<Zcat> (h\<cdot>(srt\<cdot>s))))"
  by(intro cont2cont)

lemma strict_smapAlt[simp]: "smapAlt f\<cdot>\<epsilon> = \<epsilon>"
by (subst smapAlt_def [THEN fix_eq2], simp)

lemma smapAlt_scons[simp]: "smapAlt f\<cdot>(\<up>a \<Zcat> s) = (f a) \<Zcat> smapAlt f\<cdot>s"
  by (subst smapAlt_def [THEN fix_eq2], simp)

end
theory TOneDatatype
imports Classes

begin
default_sort type


datatype 'a tone = TOneMsg 'a

fun inverseTOne :: "'a tone \<Rightarrow> 'a" where
"inverseTOne (TOneMsg m) = m"

lemma inverseTOne_inv_TOneMsg: "inverseTOne = (inv TOneMsg)"
  by (metis inv_equality inverseTOne.elims inverseTOne.simps)

instance tone :: (countable) countable
  by countable_datatype

datatype_compat tone

lemma inj_tone [simp]: "inj_on TOneMsg A"
  by (rule inj_onI) simp

instantiation tone:: (countable) discrete_cpo
begin
definition "((\<sqsubseteq>) :: 'a tone \<Rightarrow> 'a tone \<Rightarrow> bool) = (=)"

instance
  by standard (simp add: below_tone_def)
end

instantiation tone:: (countable) tlen
begin
  fun tlen_tone:: "'a tone \<Rightarrow> lnat" where
  "tlen_tone _ = 1" 

instance 
  apply(intro_classes)
  apply (simp add: cont2mono; fail)
  apply(rule exI, simp add: lnzero_def one_def)
  done
end

instance tone:: (countable) tlen_one
  apply(intro_classes)
  by(simp)

end
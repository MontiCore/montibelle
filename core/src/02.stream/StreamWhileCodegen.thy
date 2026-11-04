theory StreamWhileCodegen
  imports StreamCodegen
begin



definition stakewhile_nc :: "('a::{countable} \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> 'a stream"
  where "stakewhile_nc f \<equiv> Rep_cfun (stakewhile f)"

lemma [code_abbrev]: "stakewhile_nc f s = stakewhile f\<cdot>s"
  by (simp add: stakewhile_nc_def)

lemma stakewhile_nc_empty [code]: "stakewhile_nc f \<epsilon> = \<epsilon>"
  and stakewhile_nc_if [code]: "stakewhile_nc f (updis h && rt) = (if (f h) then \<up>h \<Zcat> (stakewhile_nc f) rt else \<epsilon>)"
   apply (simp add: stakewhile_nc_def)+
  by (simp add: upstream_abbrev)


end

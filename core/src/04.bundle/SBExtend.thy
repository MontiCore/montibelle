theory SBExtend

imports SB stream.StreamFilter stream.StreamWhile

begin

lift_definition sbSetCh::"'cs \<Rightarrow>M stream \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow>  'cs\<^sup>\<Omega>" is
"\<lambda>cs s sb. if(sValues\<cdot>s \<subseteq> ctype (Rep cs)) then Abs_lsb(\<lambda>c. if (c=cs) then s else sb\<^enum>c) else undefined"
  apply(intro cont2cont)
  by(simp add: lsb_well_def)

lift_definition sbNTimes ::"nat \<Rightarrow> 'cs\<^sup>\<Omega> \<Rightarrow>  'cs\<^sup>\<Omega>" is
"\<lambda>n sb c. sntimes n (sb\<^enum>c)"
  apply(simp add: lsb_well_def)
  using sbgetch_ctypewell sntimes_sValues1 by blast

lift_definition sbInfTimes ::"'cs\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<Omega>" is
"\<lambda>sb c. sinftimes (sb\<^enum>c)"
  by(simp add: lsb_well_def)

lift_definition sbFilter::"M set \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow>  'cs\<^sup>\<Omega>" is 
"\<lambda>A sb. Abs_lsb (\<lambda>c. sfilter A\<cdot>(sb\<^enum>c))"
  apply(intro cont2cont)
  by(simp add: lsb_well_def le_infI1)

lift_definition sbTakeWhile::"(M \<Rightarrow> bool) \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" is
"\<lambda>P sb. Abs_lsb (\<lambda>c. stakewhile P\<cdot>(sb\<^enum>c))"
  apply(intro cont2cont)
  apply(simp add: lsb_well_def)
  by (meson order.trans sValues_prefix sbgetch_ctypewell stakewhile_below)

lemma sdropwhile_values [simp]:"sValues\<cdot>(sdropwhile P\<cdot>s) \<subseteq> sValues\<cdot>s"
  apply(induction s rule: ind, auto)
  by (metis (no_types, lifting) insert_iff sdropwhile_f sdropwhile_t srcdups_dom srcdups_dom_h subsetD)

lift_definition sbDropWhile::"(M \<Rightarrow> bool) \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" is
"\<lambda>P sb. Abs_lsb (\<lambda>c. sdropwhile P\<cdot>(sb\<^enum>c))"
  apply(intro cont2cont)
  apply(simp add: lsb_well_def)
  by (meson order_trans sbgetch_ctypewell sdropwhile_values)

lift_definition sbRcdups::"'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" is
"\<lambda>sb. Abs_lsb (\<lambda>c. srcdups\<cdot>(sb\<^enum>c))"
  apply(intro cont2cont)
  by(simp add: lsb_well_def)

end

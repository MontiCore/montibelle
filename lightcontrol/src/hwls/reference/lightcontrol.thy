theory lightcontrol
  imports stream.StreamAutomaton stream.TsynStream
begin

fun Or_HLR::" (bool stream \<times> bool stream)  \<Rightarrow> bool stream \<Rightarrow> bool"where
"Or_HLR (in1,in2) out = (out = smap (\<lambda>(a,b). a \<or> b)\<cdot>(szip\<cdot>in1\<cdot>in2))"

definition or_HLR2::"((bool stream \<times>  bool stream) \<rightarrow> bool stream) set"where
"or_HLR2 = {f . \<forall> i. Or_HLR i (f\<cdot>i)}"

fun And_HLR::" (bool stream \<times> bool stream)  \<Rightarrow> bool stream \<Rightarrow> bool"where
"And_HLR (in1,in2) out = (out = smap (\<lambda>(a,b). a \<and> b)\<cdot>(szip\<cdot>in1\<cdot>in2))"

definition and_HLR2::"((bool stream \<times>  bool stream) \<rightarrow> bool stream) set"where
"and_HLR2 = {f . \<forall> i. And_HLR i (f\<cdot>i)}"

fun Not_HLR::"bool stream  \<Rightarrow> bool stream \<Rightarrow> bool"where
"Not_HLR (in1) out = (out = smap Not\<cdot>in1)"

definition not_HLR2::"(bool stream  \<rightarrow> bool stream) set"where
"not_HLR2 = {f . \<forall> i. Not_HLR i (f\<cdot>i)}"

fun strongNot_HLR::"bool stream \<Rightarrow> bool stream \<Rightarrow> bool"where
"strongNot_HLR in1 out = (out = \<up>True\<Zcat>(smap Not\<cdot>in1))"

definition snot_HLR2::"(bool stream  \<rightarrow> bool stream) set"where
"snot_HLR2 = {f . \<forall> i. strongNot_HLR i (f\<cdot>i)}"

fun lightcontrol_HLR::"(bool stream \<times>  bool stream) \<Rightarrow> bool stream \<Rightarrow> bool"where
"lightcontrol_HLR (switchstatus,alarmstatus) OnOffCmd = (\<forall>t. Suc t <#(alarmstatus,switchstatus)\<longrightarrow> snth (Suc t) alarmstatus \<and> snth t alarmstatus \<longrightarrow> snth (Suc t) OnOffCmd \<noteq> snth t OnOffCmd)"

definition lightcontrol_HLR1::"((bool stream \<times>  bool stream) \<rightarrow> bool stream) set"where
"lightcontrol_HLR1 = {f . \<forall> i. lightcontrol_HLR i (f\<cdot>i)}"

fun flasher_HLR::"bool stream \<Rightarrow> bool stream \<Rightarrow> bool"where
"flasher_HLR in1 out = ((\<forall> t. Suc t <#in1 \<longrightarrow> (snth (Suc t) in1 \<longrightarrow> snth (Suc t) out \<noteq> snth t out)) \<and> (shd out = shd in1) \<and> #out = #in1)"

definition flasher_HLR2::"(bool stream  \<rightarrow> bool stream) set"where
"flasher_HLR2 = {f . \<forall> i. flasher_HLR i (f\<cdot>i)}"

definition lightcontrol_HLR2::"((bool stream \<times>  bool stream) \<rightarrow> bool stream) set"where
"lightcontrol_HLR2 = {f | f.  \<exists>not\<in>not_HLR2. \<exists>flasher\<in>flasher_HLR2. \<exists>and\<in>and_HLR2. \<exists>or\<in>or_HLR2. \<forall>i1 i2. f\<cdot>(i1,i2) = or\<cdot>(and\<cdot>(i1,(not\<cdot>i2)),flasher\<cdot>(i2))}"


lemma smap_szip[simp]:"szip\<cdot>(smap f\<cdot>s1)\<cdot>(smap g\<cdot>s2) = smap (\<lambda>(a,b). ((f a), (g b)))\<cdot>(szip\<cdot>s1\<cdot>s2)"
  apply(induction s1 arbitrary: s2;simp)
  by(case_tac s2;simp)
 
lemma smap_srt[simp]:"srt\<cdot>(smap f\<cdot> s) = smap f\<cdot>(srt\<cdot>s)"
  by(cases s;simp)
 
lemma szip_srt[simp]:"srt\<cdot>(szip\<cdot>s1\<cdot>s2) = szip\<cdot>(srt\<cdot>s1)\<cdot>(srt\<cdot>s2)"
  by(cases s1;cases s2;simp)

lemma flasher_pred_shd:
  assumes "And_HLR (alarmstatus,flasherin) flasherout"
  assumes "strongNot_HLR flasherout flasherin"
  shows "shd flasherout = shd alarmstatus"
  using assms apply simp
  apply(cases alarmstatus;simp)
  apply(cases flasherin;simp)
  done

lemma flasherin_len:
  assumes "And_HLR (alarmstatus,flasherin) flasherout"
  assumes "strongNot_HLR flasherout flasherin"
  assumes "t<#alarmstatus"
  shows "#flasherin = lnsuc\<cdot>(#(alarmstatus))"
  using assms apply simp
  apply(subgoal_tac "#(smap Not\<cdot>(smap (\<lambda>(x, y). x \<and> y)\<cdot>(szip\<cdot>alarmstatus\<cdot>flasherin))) = #(alarmstatus,flasherin)")
  apply auto 
  apply (metis min_rek slen_scons slen_smap szip_len)
  by (simp add: len_prod_def2)

lemma flasherout_len:
  assumes "And_HLR (alarmstatus,flasherin) flasherout"
  assumes "strongNot_HLR flasherout flasherin"
  assumes "t<#alarmstatus"
  shows "#flasherout = (#(alarmstatus))"
  using assms apply simp
  by (metis min_rek slen_scons slen_smap szip_len)

lemma flasher_pred_h:
  assumes "And_HLR (alarmstatus,flasherin) flasherout"
  assumes "strongNot_HLR flasherout flasherin"
  assumes "Suc t<#alarmstatus"
  shows "snth (Suc t) alarmstatus \<Longrightarrow> snth (Suc t) flasherout \<noteq> snth t flasherout"
  using assms(1,2,3)
  apply(simp add: smapsmap2smap o_def case_prod_beta')
  apply(subgoal_tac "Fin (Suc t) < #flasherin")
   apply(subgoal_tac "Fin (Suc t) < #flasherout")
    apply(subst smap_snth_lemma,simp_all)
  apply(subst smap_snth_lemma,simp_all) 
  using convert_inductive_asm apply blast 
   apply(subst szip_nth,simp_all)
   apply(subst szip_nth,simp_all)
 apply(subst szip_nth,simp_all)  
  using convert_inductive_asm apply blast
  using convert_inductive_asm apply blast
 apply(subst szip_nth,simp_all) 
  using convert_inductive_asm apply blast
  using convert_inductive_asm apply blast
  apply (metis (no_types, lifting) assms(1,2) convert_inductive_asm flasherout_len fst_eqD slen_smap smap_snth_lemma snd_eqD snth_scons szip_nth)
    apply(cases alarmstatus;simp)
  apply(cases flasherin;simp)
  apply(cases alarmstatus;simp)
  apply(cases flasherin;simp)
  by (metis (lifting) assms(1,2,3) convert_inductive_asm flasherout_len slen_scons slen_smap szip_len)


lemma or_snth:
  assumes "Or_HLR (s1,s2) s3"
and "t<#(s1,s2)"
shows "snth t s3 = ((snth t s1)\<or>(snth t s2))"
  using assms apply simp
  by (simp add: len_prod_def2 smap_snth_lemma case_prod_beta' szip_nth) 

lemma and_snth:
  assumes "And_HLR (s1,s2) s3"
and "t<#(s1,s2)"
shows "snth t s3 = ((snth t s1)\<and>(snth t s2))"
  using assms apply simp
  by (simp add: len_prod_def2 smap_snth_lemma case_prod_beta' szip_nth) 


lemma not_snth:
  assumes "Not_HLR (s1) s2"
and "t<#s1"
shows "snth t s2 = (\<not>snth t s1)"
  using assms apply simp
  by (simp add: len_prod_def2 smap_snth_lemma case_prod_beta' szip_nth) 


lemma and_len:"And_HLR (s1,s2) s3 \<Longrightarrow> #s3 = #(s1,s2)"
  by (simp add: len_prod_def2)

lemma strongnot_len:"strongNot_HLR s1 s2 \<Longrightarrow> #s2 = lnsuc\<cdot>(#s1)"
  by simp


lemma flasher_pred:
  assumes "And_HLR (alarmstatus,flasherin) flasherout"
  assumes "strongNot_HLR flasherout flasherin"
  shows "flasher_HLR alarmstatus flasherout"
  apply simp
  using assms flasher_pred_h flasher_pred_shd
  by (metis and_len flasherout_len len_prod_minl order_le_neq_trans)


lemma lightcontrol_pred:
  assumes "And_HLR (switchstatus,fstnotout) fstandout"
  assumes "Not_HLR alarmstatus fstnotout"
  assumes "flasher_HLR alarmstatus flasherout"
  assumes "Or_HLR (fstandout,flasherout) OnOffCmd"
  shows "lightcontrol_HLR (switchstatus,alarmstatus) OnOffCmd"
  apply simp
  apply rule
  apply rule
  apply rule
proof-
  fix t
  assume a1:" Fin (Suc t)< #(alarmstatus, switchstatus)"
  assume a2:"snth (Suc t) alarmstatus \<and> snth t alarmstatus"
  have length1:"Fin (Suc t)< #(fstnotout, fstandout)"
    using a1 assms
    by (simp add: len_prod_def2)
  have length2:"Fin (Suc t)<#flasherout"
    using a1 assms(3) by(simp add: len_prod_def)
  have "\<not>snth (Suc t) fstnotout \<and> \<not>snth t fstnotout"
    using a1 a2 not_snth  assms(2) len_prod_lsmaller linorder_not_less 
    by (metis convert_inductive_asm)
  then have "\<not>snth (Suc t) fstandout \<and> \<not> snth t fstandout"
    using a1 a2 and_snth  assms(1) linorder_not_less
    by (metis and_len convert_inductive_asm len_prod_rsmaller length1)
  then have onoff_snth:"(snth (Suc t) OnOffCmd = snth (Suc t) flasherout) \<and>( snth t OnOffCmd = snth t flasherout)"
    apply(subst or_snth[of fstandout flasherout])
    using assms(4) apply simp
    using length1 length2 apply(simp add: len_prod_def2)
    apply(subst(4) or_snth[of fstandout flasherout])
    using assms(4) apply simp
    using length1 length2 apply(simp add: len_prod_def2) 
    using convert_inductive_asm apply blast
    by(simp)
  have flasherout:"snth (Suc t) flasherout \<noteq> snth t flasherout"
    using a2 assms(3) length2 by force
  then show "snth (Suc t) OnOffCmd = (\<not> snth t OnOffCmd)"
    by(simp add: onoff_snth)
qed


lemma "{f | f. \<forall>i. Or_HLR i (f\<cdot>i)} \<noteq>{}"
  apply(simp)
  apply(rule_tac x="(\<Lambda> (a,b). smap (\<lambda>(x,y). x \<or> y)\<cdot>(szip\<cdot>a\<cdot>b))" in exI)
  by simp


lemma "{f | f. \<forall>i. And_HLR i (f\<cdot>i)} \<noteq>{}"
  apply simp
  apply(rule_tac x="(\<Lambda> (a,b). smap (\<lambda>(x,y). x \<and> y)\<cdot>(szip\<cdot>a\<cdot>b))" in exI)
  by simp

lemma "{f | f. \<forall>i. Not_HLR i (f\<cdot>i)} \<noteq>{}"
  by auto

lemma sscanlaone_len[simp]:"#(sscanlAOne t s\<cdot>i) = #i"
proof(induction i arbitrary: s)
  case adm
  then show ?case
    by(simp add: len_stream_def)
next
  case bottom
  then show ?case by(simp add: sscanlAOne_def)
next
  case (step a i)
  then show ?case by(simp add: sscanlAOne_def)
qed

lemma lightcontrol_consistent_h:"snth (Suc t) (\<mu> i. \<up>b \<Zcat> smap Not\<cdot>i) = (\<not> snth t (\<mu> i. \<up>b \<Zcat> smap Not\<cdot>i))"
  apply(induction t arbitrary: b)
   apply (subst fix_eq,simp)
   apply (subst fix_eq,simp)
   apply (subst fix_eq,simp)
  apply (subst fix_eq,simp)
  apply (subst fix_eq,simp)
  by(simp add: smapsmap2smap)

lemma "{f | f. \<forall>i. lightcontrol_HLR i (f\<cdot>i)} \<noteq>{}"
  apply(auto)
  apply(rule_tac x="(\<Lambda> _. fix\<cdot>(\<Lambda> i. (\<up>True) \<Zcat> (smap Not\<cdot>i)))" in exI)
  apply simp
  using lightcontrol_consistent_h 
  by presburger


end

theory BundleMergeUntimed
imports eventcomponent.GeneralBundleMerge bundle.Timeconverter

begin

default_sort type


lemma "mergeTimed \<then> {e2ustream}  \<subseteq> {e2ubundle} \<then> mergeUntimed"
  oops


definition chan_chtime::"timeType \<Rightarrow> 'ch1::chan \<Rightarrow> 'ch2::chan" where
"chan_chtime tt c = Abs (changeTimeType tt (Rep c))"

definition msgWithChan_chtime:: "timeType \<Rightarrow> 'ch1::chan msgWithChan \<Rightarrow> 'ch2::chan msgWithChan" where
"msgWithChan_chtime tt msg = Abs_msgWithChan (apfst (chan_chtime tt) (Rep_msgWithChan msg))"

definition egetch::"'ech \<Rightarrow> 'ech::echan\<^sup>\<Omega> \<rightarrow> msg event stream" where
"egetch c = (\<Lambda> sb. smap (\<lambda> msg. case msg of (Timed (TLive m)) \<Rightarrow> m | _ \<Rightarrow> undefined)
                        \<cdot>(sb \<^enum> c))"

definition e2ubundle::"'ech::echan\<^sup>\<Omega> \<rightarrow> 'uch::uchan\<^sup>\<Omega>" where
"e2ubundle \<equiv> if changeTimeType TTLive ` chDom TYPE('uch::uchan) = chDom TYPE('ech::echan)
  then (\<Lambda> sb. Abs_lsb (\<lambda> c::'uch. 
    smap Untimed\<cdot>(
      e2ustream\<cdot>(
        egetch (chan_chtime TTLive c)\<cdot>sb))))
  else undefined"

lemma 
  assumes "changeTimeType TTLive ` chDom TYPE('uch::uchan) = chDom TYPE('ech::echan)"
  shows  "mergeTimed \<then> {e2ustream} \<then> {smap (msgWithChan_chtime TUntimed)}  \<subseteq> {e2ubundle} \<then> mergeUntimed"
  oops

lemma 
  fixes inputConv::"'inputTimed::pcpo \<rightarrow> 'inputUntimed::pcpo"
        and outputConv::"'outputTimed::pcpo \<rightarrow> 'outputUntimed::pcpo"
      assumes "\<And> inputUntimed spfUntimed. spfUntimed \<in> spsUntimed \<Longrightarrow> P inputUntimed (spfUntimed\<cdot>inputUntimed)"
        and "spfTimed \<in> spsTimed"

        and "spsTimed \<then> {outputConv} \<subseteq> {inputConv} \<then> spsUntimed"

shows "P (inputConv\<cdot>sb) (outputConv\<cdot>(spfTimed\<cdot>sb))"
proof(insert assms(1)[where inputUntimed="inputConv\<cdot>sb"])
  have h1:"outputConv oo spfTimed \<in> {inputConv} \<then> spsUntimed"
    using assms(2,3) by (simp add: seqcomp_image2 subsetD)
  then obtain spfUntimed where spfUntimed_def:"spfUntimed \<in> spsUntimed \<and> 
      outputConv oo spfTimed = spfUntimed oo inputConv"
    using seqcomp_image by blast
  have "\<exists>spfUntimed\<in> spsUntimed. spfUntimed\<cdot>(inputConv\<cdot>sb) = outputConv\<cdot>(spfTimed\<cdot>sb)"
    using spfUntimed_def by (metis cfcomp2)
  thus ?thesis
    using assms by metis
qed






typedef 'cs::chan untimed = "changeTimeType TUntimed ` range (Rep::'cs \<Rightarrow> channel)"
  by simp
(*
instantiation untimed :: (one_chan) chan 
begin

definition chanDom_untimed::"'a untimed myself \<Rightarrow> channel set" where
"chanDom_untimed _ = changeTimeType TUntimed ` chanDom (DUMMY::'a myself)"

lemma chdom_untimedempty[simp]:"chDom TYPE('a) = {} \<longleftrightarrow> chanDom (x::'a untimed myself) = {}"
  by(simp add: chanDom_untimed_def chandomchdomeq)+

lemma ctype_untimednempty[simp]:"ctype (Rep (c::'a)) \<noteq> {} \<longleftrightarrow> ctype (changeTimeType TUntimed (Rep c)) \<noteq> {}"
  using ctype_nempty by auto

instance
  apply(standard)
  oops
     apply(simp add: chanDom_untimed_def chanDom Rep_untimed_def univ_untimed)
  apply (rule)
  apply(auto)[1]
  apply(case_tac "Rep xb";simp)
  apply (metis (no_types, lifting) changeTimeType.simps image_iff repinrange untimed_surj)
      apply(case_tac "Rep xb";simp add: cEmpty_def ctype_empty_iff)
  apply(auto)[1]
     apply(case_tac "Rep xb";simp)
     apply (metis (mono_tags, lifting) Rep_untimed_def bundlemerge_untimed.ctype_nempty cEmpty_def 
chDom_def changeTimeType.simps chdom_in dom2ctypeempty imageI mem_Collect_eq untimed_surj)
  apply auto
    apply(simp add: cEmpty_def)
    apply (metis bundlemerge_untimed.ctype_nempty dom2ctypeempty dom2ctypenempty untimed.exhaust)
   apply(rule injI)
   apply(simp add: Rep_untimed_def)
   apply(case_tac x;case_tac y;simp)
   apply(case_tac "Rep xa";simp)
   apply(case_tac "Rep xb";simp) 

  subgoal sorry
  sorry

end *)
(*

instance untimed ::(one_chan) uchan
  apply(standard)
  sorry

instance untimed ::(finite) finite
  apply(standard)
  sorry (*
  by (simp add: univ_untimed) *)
*)


definition sbTimed2Untimed::"'cs::tchan sb \<rightarrow> 'cs untimed sb" where
"sbTimed2Untimed = undefined"

definition sUntimed2Event::"('m stream \<rightarrow> 'm event stream) set" where
"sUntimed2Event = undefined"




end
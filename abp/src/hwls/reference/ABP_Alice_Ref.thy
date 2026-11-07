theory ABP_Alice_Ref
  imports
    (* core *)
    stream.TsynStream
    tscomponent.TsLocale

    sps_Bob_HLR.def_Bob_HLR
    bundle_Bob_HLR.def_Bob_HLR_Input
    bundle_Bob_HLR.def_Bob_HLR_Output

    move_to_core.TsynStreamExtension
begin


fun Alice_h :: "(nat list \<times> bool) \<Rightarrow> (nat tsyn \<times> bool tsyn) \<Rightarrow> ((nat list \<times> bool) \<times> ((nat \<times> bool) tsyn)) set" where
A1:"Alice_h ([], Ack) (Eps, Eps) = {( ([], Ack), Eps)}" |
A2:"Alice_h ([], Ack) (TSynMsg Data, Eps) = {(([Data], Ack),TSynMsg (Data, Ack))}" |
A9:"Alice_h ([], Ack) (Eps, TSynMsg a) = 
 (if a = Ack then {(([], (\<not>Ack)),Eps)} else {(([], Ack),Eps)})" |
A10:"Alice_h ([], Ack) (TSynMsg Data, TSynMsg a) = 
 (if a = Ack then {(([Data],\<not>Ack), TSynMsg (Data, \<not>Ack))} else {(([], Ack),Eps)})"|
A3:"Alice_h (Buf # Bufs, Ack) (Eps, Eps) = {((Buf # Bufs, Ack), TSynMsg (Buf, Ack))}" |
A4:"Alice_h ([Buf], Ack) (Eps, TSynMsg a) = (if a = Ack then {(([], \<not>Ack), Eps)} else {undefined})" |
A5:"Alice_h (Buf1 # Buf2 # Bufs, Ack) (Eps, TSynMsg a) = 
 (if a = Ack then {((Buf2 # Bufs, \<not>Ack), TSynMsg (Buf2, \<not>Ack))} else {undefined})" |
A6:"Alice_h (Buf # Bufs, Ack) (TSynMsg Data, Eps) = {((Buf # Bufs @ [Data], Ack),TSynMsg (Buf, Ack))}" |
A7:"Alice_h ([Buf], Ack) (TSynMsg Data, TSynMsg a) = 
 (if a = Ack then {( ([Data], \<not>Ack), TSynMsg (Data, \<not>Ack))} else {undefined})" |
A8:"Alice_h (Buf1 # Buf2 # Bufs, Ack) (TSynMsg Data, TSynMsg a) = 
 (if a = Ack then {((Buf2 # Bufs @ [Data], \<not>Ack), TSynMsg (Buf2, \<not>Ack))} else {undefined})" 



definition Alice_init :: "((nat list \<times> bool) \<times> (nat \<times> bool) tsyn) set" where
"Alice_init = {(([],True),Eps)}"


interpretation Alice: tsStrongGen "(\<lambda> (). Alice_h)" "(\<lambda> (). Alice_init)" finA foutA
  by standard

lemma Alice_h_not_empty: "Alice_h state msg \<noteq> {}"
  apply (case_tac state; case_tac msg)
  apply (case_tac a; case_tac b; case_tac aa; case_tac ba; auto)
     apply (case_tac ac; case_tac ab; case_tac list; auto)
  apply (case_tac ad; case_tac ab; case_tac list; auto)
   apply (case_tac ac; case_tac ab; case_tac list; auto)
  by (case_tac ad; case_tac ab; case_tac list; auto)

lemma Alice_h_singleton:
  "is_singleton (Alice_h state msg)"
  apply (case_tac state; case_tac msg)
  apply (case_tac a; case_tac b; case_tac aa; case_tac ba; auto)
     apply (case_tac list; case_tac ab; case_tac ac; auto)
    apply (case_tac list; case_tac ab; case_tac ac; auto)
   apply (case_tac list; case_tac ab; case_tac ac; auto)
  by (case_tac list; case_tac ab; case_tac ac; auto)

lemma Alice_stateSem_singleton: "is_singleton (Alice.StateSems_stream param listxbool)"
  apply (rule is_singletonI')
   apply (simp add: statesem_notempty) 
  apply (rule cfun_eqI)
proof -
  fix x y xa
  assume x:"x \<in> Alice.StateSems_stream param listxbool"
  assume y:"y \<in> Alice.StateSems_stream param listxbool"
  show " x\<cdot>xa = y\<cdot>xa"
    using x y
    apply simp
  proof (induction xa arbitrary : x y listxbool)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step a xa)
    obtain nspf_x ns_x out_x where
    step_x_def: "x\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_x \<Zcat> nspf_x\<cdot>xa" and
        nspf_x:  "nspf_x \<in> Alice.StateSems_stream param ns_x"and
       trans_x:  "(ns_x,out_x) \<in> (Alice.transitionC param listxbool a)"
      using Alice.statesems_stream_step
      by (metis old.unit.exhaust step.prems(1))

    obtain nspf_y ns_y out_y where 
    step_y_def: "y\<cdot>(\<up>a \<Zcat> (xa)) = \<up>out_y \<Zcat> nspf_y\<cdot>xa" and
        nspf_y:  "nspf_y \<in> Alice.StateSems_stream param ns_y"and
       trans_y:  "(ns_y,out_y) \<in> (Alice.transitionC param listxbool a)"
      using Alice.statesems_stream_step
      by (metis old.unit.exhaust step.prems(2))


  have transition_unique: "out_x = out_y \<and> ns_x = ns_y"
    using trans_x trans_y Alice_h_singleton
    unfolding Alice.transitionC_def is_singleton_def
    by (metis case_unit insert_not_empty
        old.prod.inject
        singleton_iff)

      from step.IH transition_unique  nspf_x nspf_y  step_x_def step_y_def
      show ?case
        apply auto
        by (metis step.IH)
  qed 
qed



lemma alice_step_simp0 :assumes"spf\<in> Alice.StateSems_stream param ([], bool)"
  shows "spf\<cdot>(\<up>(Eps,Eps) \<Zcat> s) = \<up>(Eps) \<Zcat> spf\<cdot>(s)"
proof - 

    obtain nspf ns out where 
    step_def: "spf\<cdot>(\<up>(Eps,Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf\<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([], bool) (Eps, Eps))"
      using Alice.statesems_stream_step   assms  by blast

    from this have out:"out = ( Eps)" using Alice.transitionC_def Alice_h.simps
      by (metis case_unit insert_not_empty prod.inject singleton_iff)

    from assms nspf trans have ns: "ns = ([], bool)"using Alice.transitionC_def
      by simp  

    from ns nspf assms have eq: "spf = nspf"      
      by (metis (mono_tags, lifting) Abs_unit_cases Alice_stateSem_singleton
          is_singleton_def singleton_iff)

  from this step_def nspf ns show "spf\<cdot>(\<up>(Eps,Eps) \<Zcat> s) = \<up>(Eps) \<Zcat> spf\<cdot>(s)"
    using eq out by blast
qed

lemma alice_step_simp1:assumes"spf\<in> Alice.StateSems_stream param ([], bool)"
  assumes "spf2 \<in> Alice.StateSems_stream param ([Data], bool)"
  shows "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> s) = \<up>(TSynMsg (Data, bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([], bool) (TSynMsg Data, Eps))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Data, bool))" using Alice.transitionC_def trans
      by (auto simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = ([Data], bool)" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
        apply auto
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> s) = \<up>(TSynMsg (Data, bool)) \<Zcat> spf2\<cdot>(s)"
  by (simp add: step_def) 
qed

lemma alice_step_simp2:assumes"spf\<in> Alice.StateSems_stream param (Buf # Bufs, bool)"
  shows "spf\<cdot>(\<up>(Eps, Eps) \<Zcat> s) = \<up>(TSynMsg (Buf, bool)) \<Zcat> spf\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(Eps, Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ((Buf # Bufs), bool) (Eps, Eps) )"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Buf, bool))" using Alice.transitionC_def trans
      by (auto simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = (Buf # Bufs, bool)" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf" using Alice_stateSem_singleton
        apply auto
       by (metis is_singleton_def singleton_iff)
  
     ultimately show "spf\<cdot>(\<up>(Eps, Eps) \<Zcat> s) = \<up>(TSynMsg (Buf, bool)) \<Zcat> spf\<cdot>(s)"
       by (simp add: step_def)

qed

lemma alice_step_simp3:assumes"spf\<in> Alice.StateSems_stream param ([Buf], bool)"
  assumes "spf2\<in> Alice.StateSems_stream param ([], \<not>bool)"
  assumes "a = bool"
  shows "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([Buf], bool) (Eps, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = Eps" using Alice.transitionC_def assms
      by (auto simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = ([], \<not>bool)"
      by (auto simp add: Alice.transitionC_def)

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)

     ultimately show "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def) 
qed

lemma alice_step_simp4:assumes"spf\<in> Alice.StateSems_stream param (Buf1 # Buf2 # Bufs, bool)"
  assumes "spf\<in> Alice.StateSems_stream param (Buf2 # Bufs, \<not>bool)"
  assumes "a = bool"
  shows "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Buf2, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param (Buf1 # Buf2 # Bufs, bool) (Eps, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Buf2, \<not>bool))" using Alice.transitionC_def assms
      by (auto simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = (Buf2 # Bufs, \<not>bool)"
      by (auto simp add: Alice.transitionC_def)

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis alice_step_simp2 prod.inject shd1
           tsyn.inject)

     ultimately show "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Buf2, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def) 
qed

lemma alice_step_simp5:assumes"spf\<in> Alice.StateSems_stream param (Buf # Bufs, bool)"
  assumes "spf2\<in> Alice.StateSems_stream param (Buf # Bufs @ [Data], bool)"
  shows "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> s) = \<up>(TSynMsg (Buf, bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param (Buf # Bufs, bool) (TSynMsg Data, Eps))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Buf, bool))" using Alice.transitionC_def
      by (simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = (Buf # Bufs @ [Data], bool)" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
        apply auto
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, Eps) \<Zcat> s) = \<up>(TSynMsg (Buf, bool)) \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def) 
qed

lemma alice_step_simp6:assumes"spf\<in> Alice.StateSems_stream param ([Buf], bool)"
  assumes "spf2\<in> Alice.StateSems_stream param ([Data], \<not>bool)"
  assumes "a = bool"
  shows "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Data, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([Buf], bool) (TSynMsg Data, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Data, \<not>bool))" using Alice.transitionC_def assms
      by (simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = ([Data], \<not>bool)" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Data, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def) 

qed

lemma alice_step_simp7:assumes"spf\<in> Alice.StateSems_stream param (Buf1 # Buf2 # Bufs, bool)"
  assumes "spf2\<in> Alice.StateSems_stream param ((Buf2 # Bufs @ [Data], \<not>bool))"
  assumes "a = bool"
  shows "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Buf2, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param (Buf1 # Buf2 # Bufs, bool) (TSynMsg Data, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = (TSynMsg (Buf2, \<not>bool))" using Alice.transitionC_def assms (3)
      by (simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = ((Buf2 # Bufs @ [Data], \<not>bool))" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Buf2, \<not>bool)) \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def ) 

qed



lemma alice_step_simp8:assumes"spf\<in> Alice.StateSems_stream param ([], bool)"
  assumes "spf2\<in> Alice.StateSems_stream param (([], \<not>bool))"
  assumes "a = bool"
  shows "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(Eps , TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([], bool) (Eps, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = Eps" using Alice.transitionC_def assms (3)
      by (simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = (([], \<not>bool))" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def ) 

qed


lemma alice_step_simp9:assumes"spf\<in> Alice.StateSems_stream param (([], bool))"
  assumes "a = (\<not>bool)"
  shows "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(Eps , TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([], bool) (Eps, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out = Eps" using Alice.transitionC_def assms
      by (simp add: Alice_h_not_empty)
      
    moreover from assms nspf trans have "ns = (([], bool))" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)
  
     ultimately show "spf\<cdot>(\<up>(Eps, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf\<cdot>(s)"
       using step_def by blast

qed

lemma alice_step_simp10:assumes"spf\<in> Alice.StateSems_stream param (([], bool))"
  assumes "a = (bool)"
  assumes " spf2 \<in> Alice.StateSems_stream param ([Data],\<not>bool)"
  shows "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Data,(\<not>bool))) \<Zcat> spf2\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data , TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([], bool) (TSynMsg Data, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out =(TSynMsg (Data,  \<not>bool))" using Alice.transitionC_def assms 
      by (simp add: Alice_h_not_empty)

    moreover from assms nspf trans have "ns = (([Data], \<not>bool))" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf2" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>(TSynMsg (Data, (\<not>bool))) \<Zcat> spf2\<cdot>(s)"
    by (simp add: step_def ) 

qed

lemma alice_step_simp11:assumes"spf\<in> Alice.StateSems_stream param (([], bool))"
  assumes "a = (\<not>bool)"
  shows "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf\<cdot>(s)"
proof -
    obtain nspf ns out where
    step_def: "spf\<cdot>(\<up>(TSynMsg Data , TSynMsg a) \<Zcat> (s)) = \<up>out \<Zcat> nspf\<cdot>s" and
        nspf:  "nspf \<in> Alice.StateSems_stream param ns"and 
       trans:  "(ns,out) \<in> (Alice.transitionC param ([], bool) (TSynMsg Data, TSynMsg a))"
      using Alice.statesems_stream_step assms by blast

    from trans have "out =Eps" using Alice.transitionC_def assms 
      by (simp add: Alice_h_not_empty)

    moreover from assms nspf trans have "ns = (([], bool))" using Alice.transitionC_def 
        by simp

     moreover from this  assms nspf have "nspf = spf" using Alice_stateSem_singleton
       by (metis is_singleton_def singleton_iff)
  
  ultimately show "spf\<cdot>(\<up>(TSynMsg Data, TSynMsg a) \<Zcat> s) = \<up>Eps \<Zcat> spf\<cdot>(s)"
    using step_def by blast

qed



lemma compact_list2s[simp]:"compact (<x>)"
  apply (rule compactI)
  apply (rule admI)
proof (rule contrapos_nn)
  fix Y
  assume chain: " chain (Y::nat \<Rightarrow> 'a stream)" 
  assume "<x> \<sqsubseteq> (\<Squnion>i. Y i)"

  have "\<exists>i. <x> \<sqsubseteq> Y i"
  proof- 
      from \<open><x> \<sqsubseteq> (\<Squnion>i. Y i)\<close>
    obtain n where "\<forall>m < n.(x ! m) = (snth m (\<Squnion>i. Y i))"
      by auto 

    from chain have mono: "\<And>i j. i \<le> j \<Longrightarrow> Y i \<sqsubseteq> Y j"
      by (simp add: chain_mono)

    show ?thesis
      using \<open><x> \<sqsubseteq> (\<Squnion>i. Y i)\<close> chain 
      by (metis inf_chainl4 is_ub_thelub l42
          list2s_fin lub_below po_eq_conv
          stream_order_pre_total)
  qed
  then show "\<exists>i. <x> \<sqsubseteq> Y i"
    by simp
next
  show "\<And>Y::nat \<Rightarrow> 'a stream. chain Y \<Longrightarrow> \<forall>i::nat. <x> \<notsqsubseteq> Y i \<Longrightarrow> \<nexists>i::nat. <x> \<sqsubseteq> Y i"
    by auto
qed

lemma alice_out:
  assumes"spf \<in> Alice.StateSems_stream () (ls,b)"
  and "list2s ls \<sqsubseteq> tsyn2ustream\<cdot>(sprojfst\<cdot>i)"
  shows"sprojfst\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>(spf\<cdot>(i)))) \<sqsubseteq> tsyn2ustream\<cdot>(sprojfst\<cdot>i)"
  using assms 
proof(induction i arbitrary: ls spf b)
  case adm
  then show ?case
    apply(rule adm_all)+
    by(rule adm_imp,simp_all)+
next
  case bottom
  then show ?case 
    by simp
next
  case (step a i)
  obtain spf2 aa list where spf2_def:" spf2 \<in> Alice.StateSems_stream () (aa # list,b)"
    by (meson neq_emptyD statesem_notempty)
   show ?case
    using step
    apply simp
    apply(cases a;case_tac aa;simp) 
     apply (case_tac ls; case_tac b; simp_all)
    apply(subst alice_step_simp0[where bool=b and param = "()"],simp_all)
    using step.prems(1) apply blast
    apply auto
    apply (subst alice_step_simp8; simp_all)
       defer

       apply(subst alice_step_simp2[of spf "()"  aa  list b],simp_all)
    using step
    apply auto


        defer
    using step
    apply auto defer
        apply (case_tac list; simp_all)
       apply(subst alice_step_simp3[of spf "()"],simp_all)defer

        defer
        defer
        apply (case_tac ls)
         defer
         apply (case_tac list)
          defer

    sorry
qed

lemma alice_out_infinity:
  assumes"spf \<in> Alice.StateSems_stream () (ls,b)"
  and "list2s ls \<sqsubseteq> tsyn2ustream\<cdot>(sprojfst\<cdot>i)"
  and "#i = \<infinity>"
shows"sprojfst\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>(spf\<cdot>(i)))) = tsyn2ustream\<cdot>(sprojfst\<cdot>i)"
  apply(rule snths_eq)
  apply (simp add: len_stream_def)


  oops



lemma alice_out_bit:
  assumes"spf \<in> Alice.StateSems_stream () (ls,b)"
    and "((snth n (sprojsnd\<cdot>i)) = TSynMsg b) \<Longrightarrow>(snth n (sprojsnd\<cdot>(spf\<cdot>i))) = (TSynMsg (\<not>b) \<or> Eps)"
  shows"sprojsnd\<cdot>((tsyn2ustream\<cdot>(spf\<cdot>(i)))) = tsyn2ustream\<cdot>(sprojsnd\<cdot>i)" 
  using assms 
proof(induction i arbitrary: ls spf b)
  case adm
  then show ?case
    apply(rule adm_all)+
    by(rule adm_imp,simp_all)+
next
  case bottom
  then show ?case 
    by simp
next
  case (step a i)
  then show ?case
    apply(cases a;case_tac aa;simp)
    sorry
qed

(*
lemma alice_out_bit_infinity:
  assumes"spf \<in> Alice.StateSems_stream () (ls,b)"
  and "list2s ls \<sqsubseteq> tsyn2ustream\<cdot>(sprojfst\<cdot>i)"
  and "#i = \<infinity>"
shows"sprojsnd\<cdot>(tsyn2ustream\<cdot>(spf\<cdot>(i))) = tsyn2ustream\<cdot>(sprojsnd\<cdot>i)"
  apply(rule snths_eq) (*Vielleicht hier über induktion über n?*)
  sorry
*)




lift_definition sBoolFilter :: "'a::countable tsyn stream \<rightarrow> bool stream \<rightarrow> 'a tsyn stream" is
"\<lambda> s1.  smap (\<lambda> pair. if snd pair then fst pair else Eps) oo (szip\<cdot>s1)"
  by(intro cont2cont)

definition sbgenInGetter ::"'In sb \<rightarrow> (nat \<times> bool) tsyn stream"where
"sbgenInGetter = undefined"

definition sbgenOutGetter ::"'Out sb \<rightarrow> (nat \<times> bool) tsyn stream"where
"sbgenOutGetter = undefined"


definition wholePredicate::"unit \<Rightarrow> (nat \<times> bool) tsyn stream \<Rightarrow> (nat \<times> bool) tsyn stream \<Rightarrow> bool" where
"wholePredicate u = (\<lambda> s1 s2. (\<exists>bs. sBoolFilter\<cdot>s1\<cdot>bs = s2  \<and> #bs=\<infinity>))"

definition Eve::"unit \<Rightarrow>('In sb \<rightarrow> 'Out sb) set"where
"Eve u = {f | f. \<forall>i. wholePredicate u (sbgenInGetter\<cdot>i) (sbgenOutGetter\<cdot>(f\<cdot>i))}"

lemma eve_out_prefix:
  assumes "spf \<in> sEve ()"
  and "\<And>n. snth n (spf\<cdot>i) \<noteq> snth n i \<Longrightarrow> snth (Suc n) i = snth n i"
  shows "tsyn2ustream\<cdot>(spf\<cdot>(i)) \<sqsubseteq> tsyn2ustream\<cdot>i"
  oops

end
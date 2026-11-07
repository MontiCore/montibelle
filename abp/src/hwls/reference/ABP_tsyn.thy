theory ABP_tsyn
  imports stream.TsynStream move_to_core.TsynStreamExtension  

begin
definition semanticMapping :: "('s \<Rightarrow> 'i \<Rightarrow> ('o \<times> 's)) \<Rightarrow> 's \<Rightarrow> 'i stream \<rightarrow> 'o stream" where
"semanticMapping f s0 \<equiv> \<Lambda>  s. sprojfst\<cdot>(sscanl (\<lambda>(_,b). f b) (undefined, s0)\<cdot>s)"

lemma semanticmapping_arbitrary_output: "sprojfst\<cdot>(sscanl (\<lambda>(_,b). f b) (u1, st)\<cdot>s) 
          = sprojfst\<cdot>(sscanl (\<lambda>(_,b). f b) (u2, st)\<cdot>s)"
proof -
  have "\<forall>a b aa s. sscanl (\<lambda>(a, y). f y) (a, b)\<cdot>s = sscanl (\<lambda>(a, y). f y) (aa, b)\<cdot>s \<or> s = \<epsilon>"
    using streamcases by force
  then show ?thesis
    by (metis (no_types) fair_sscanl slen_empty_eq)
qed

lemma semanticmapping_step: "(semanticMapping f  u)\<cdot> (\<up>a \<Zcat> s) 
      = \<up>(fst(f u a)) \<Zcat> (semanticMapping f (snd(f u a)))\<cdot>s "
  apply (simp add: semanticMapping_def) 
  by (metis eq_snd_iff fst_conv semanticmapping_arbitrary_output sprojfst_scons )


definition Bob :: "('d \<times> bool) tsyn stream \<rightarrow> ('d tsyn stream \<times> bool tsyn stream)" where
"Bob \<equiv> \<Lambda> s. (\<up> Eps \<Zcat> \<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-s),\<up> Eps \<Zcat> \<Pi>\<^sub>2\<^sub>-s)"

lemma bob_cont: "cont( \<lambda> s. (\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-s), \<Pi>\<^sub>2\<^sub>-s))"
  by (intro cont2cont) 

definition BOB :: "(('d \<times> bool) tsyn stream \<rightarrow> ('d tsyn stream \<times> bool tsyn stream)) set" where
"BOB = {Bob}"

fun Bob_LLR_h :: "('d tsyn \<times> bool) \<Rightarrow> ('d \<times> bool) tsyn \<Rightarrow> ('d tsyn \<times> bool tsyn) \<times> ('d tsyn \<times> bool)" where
R1: "Bob_LLR_h state \<sim> = ((\<sim>, \<sim>), state)" |
R2: "Bob_LLR_h (d_state, b_state) (TSynMsg (d_in, b_in)) = 
     (if (d_state, b_state) = (TSynMsg d_in, b_in) then ((\<sim>, TSynMsg b_in), (TSynMsg d_in, b_in))
                                           else ((TSynMsg d_in, TSynMsg b_in), (TSynMsg d_in, b_in)))"

definition Bob_LLR :: "('d \<times> bool) tsyn stream \<rightarrow> ('d tsyn stream \<times> bool tsyn stream)" where
"Bob_LLR \<equiv> \<Lambda> s. ((sprojfst oo (semanticMapping Bob_LLR_h (\<sim>, True)))\<cdot>s,
              (sprojsnd oo (semanticMapping Bob_LLR_h (\<sim>, True)))\<cdot>s)"

lemma test_receiver1: "tsyn2ustream\<cdot>(fst (Bob_LLR\<cdot>(
   <[\<sim>, TSynMsg (h, True), TSynMsg (a, False), \<sim>, \<sim>, \<sim>, TSynMsg (m, True), TSynMsg (m, True), TSynMsg (b, False)]>))) 
 = <[h, a, m, b]>"
  by (simp add: tsynremdups_unfold semanticMapping_def Bob_LLR_def)

lemma Bob_LLR_h_forwards_ack: 
"sprojsnd\<cdot>(sprojfst\<cdot>(sscanl (\<lambda>a. case a of (u, a) \<Rightarrow> Bob_LLR_h a) (u, state)\<cdot>s)) = \<Pi>\<^sub>2\<^sub>-s"
proof (induction s arbitrary: u state)
  case adm
  then show ?case
    apply (rule adm_all)+
    apply (rule adm_eq)
    by auto
next
  case bottom
  then show ?case
    by simp
next
  case (step a s)
  then show ?case 
    apply (case_tac a) 
    apply (simp_all add: tsynprojsnd_sconc_Eps)
    apply (cases state)
    apply (case_tac aa)
    apply (case_tac "aaa = TSynMsg ab")
    by (simp_all add: tsynprojsnd_sconc_msg)
qed

lemma Bob_LLR_refs_HLR_ar: "snd (Bob_LLR\<cdot>s) = \<Pi>\<^sub>2\<^sub>-s"
  by (simp add:  semanticMapping_def Bob_LLR_def Bob_LLR_h_forwards_ack)

fun tsyn_and_bool_to_tsyn_pair :: "('d tsyn \<times> bool) \<Rightarrow> ('d \<times> bool) tsyn" where
  "tsyn_and_bool_to_tsyn_pair (\<sim>,     b) = \<sim>" |
  "tsyn_and_bool_to_tsyn_pair (TSynMsg d, b) = TSynMsg (d, b)"


fun Alice_LLR_h :: "('d list \<times> bool) \<Rightarrow> ('d tsyn \<times> bool tsyn) \<Rightarrow> (('d \<times> bool) tsyn) \<times> ('d list \<times> bool)" where
S1:"Alice_LLR_h ([], Ack) (\<sim>, \<sim>) = (\<sim>, ([], Ack))" |
S2:"Alice_LLR_h ([], Ack) (TSynMsg Data, \<sim>) = (TSynMsg (Data, Ack), ([Data], Ack))" |
S3:"Alice_LLR_h (Buf # Bufs, Ack) (\<sim>, \<sim>) = (TSynMsg (Buf, Ack), (Buf # Bufs, Ack))" |
S4:"Alice_LLR_h ([Buf], Ack) (\<sim>, TSynMsg x) = (if x = Ack then (\<sim>, ([], \<not>Ack)) else undefined)" |
S5:"Alice_LLR_h (Buf1 # Buf2 # Bufs, Ack) (\<sim>, TSynMsg x) = 
 (if x = Ack then (TSynMsg (Buf2, \<not>Ack), (Buf2 # Bufs, \<not>Ack)) else undefined)" |
S6:"Alice_LLR_h (Buf # Bufs, Ack) (TSynMsg Data, \<sim>) = (TSynMsg (Buf, Ack), (Buf # Bufs @ [Data], Ack))" |
S7:"Alice_LLR_h ([Buf], Ack) (TSynMsg Data, TSynMsg x) = 
 (if x = Ack then (TSynMsg (Data, \<not>Ack), ([Data], \<not>Ack)) else undefined)" |
S8:"Alice_LLR_h (Buf1 # Buf2 # Bufs, Ack) (TSynMsg Data, TSynMsg x) = 
 (if x = Ack then (TSynMsg (Buf2, \<not>Ack), (Buf2 # Bufs @ [Data], \<not>Ack)) else undefined)" |
"Alice_LLR_h _ _ = undefined"

definition Alice_LLR :: "('d tsyn stream \<times> bool tsyn stream) \<rightarrow> ('d \<times> bool) tsyn stream" where
"Alice_LLR \<equiv> \<Lambda> (s1, s2). \<up>\<sim> \<Zcat> (semanticMapping Alice_LLR_h ([], True))\<cdot>((szip\<cdot>s1\<cdot>s2))"

definition ALICE_LLR :: "(('d tsyn stream \<times> bool tsyn stream) \<rightarrow> ('d \<times> bool) tsyn stream) set" where
"ALICE_LLR = {Alice_LLR}"

definition asm_a0 :: "('d tsyn stream \<times> bool tsyn stream) \<Rightarrow> ('d \<times> bool) tsyn stream \<Rightarrow> bool"
  where
  "asm_a0 i out \<equiv>  #(fst i) = \<infinity> \<and> #(snd i) = \<infinity>"  

definition pred_a0 :: "('d tsyn stream \<times> bool tsyn stream) \<Rightarrow> ('d \<times> bool) tsyn stream \<Rightarrow> bool"
  where
  "pred_a0 i out \<equiv> tsyn2ustream\<cdot>(tsynProjFst\<cdot>(\<alpha>\<^sub>-out)) \<sqsubseteq> tsyn2ustream\<cdot>(fst i) " 

definition pred_a1 :: "('d tsyn stream \<times> bool tsyn stream) \<Rightarrow> ('d \<times> bool) tsyn stream \<Rightarrow> bool"
  where
  "pred_a1 i out \<equiv> min (#\<^sub>-(fst i)) (1 + #\<^sub>-(\<alpha>\<^sub>-(snd i))) = #\<^sub>-(tsynProjFst\<cdot>(\<alpha>\<^sub>-out)) " 

definition causality :: "('d tsyn stream \<times> bool tsyn stream) \<Rightarrow> ('d \<times> bool) tsyn stream \<Rightarrow> bool"
  where
  "causality i out \<equiv> weakpred i out" 

definition AlicePredicate :: "('d tsyn stream \<times> bool tsyn stream) \<Rightarrow> ('d \<times> bool) tsyn stream \<Rightarrow> bool"
  where
  "AlicePredicate i out \<equiv> causality i out \<and> (asm_a0 i out) \<longrightarrow> (pred_a0 i out) \<and> (pred_a1 i out)" 

definition ALICE_x :: "(('d tsyn stream \<times> bool tsyn stream) \<rightarrow> ('d \<times> bool) tsyn stream) set" 
  where 
  "ALICE_x \<equiv> {spf | spf. \<forall>i.
   AlicePredicate i (spf\<cdot>i)}"

definition ALICE :: "(('d tsyn stream \<times> bool tsyn stream) \<rightarrow> ('d \<times> bool) tsyn stream) set" where
"ALICE \<equiv> {f. strong f \<and> 
(\<forall>x y.
  #x = \<infinity> \<and> #y = \<infinity> \<longrightarrow>
    sprojfst\<cdot>(srcdups\<cdot>(f\<cdot>(x, y))\<^sup>-) \<sqsubseteq> x\<^sup>-
  \<and> srcdups\<cdot>(sprojsnd\<cdot> (srcdups\<cdot>(f\<cdot>(x, y))\<^sup>-)) = sprojsnd\<cdot>(srcdups\<cdot>(f\<cdot>(x, y))\<^sup>-)
  \<and> (#\<^sub>-(\<alpha>\<^sub>-y) < #\<^sub>-x \<longrightarrow> #\<^sub>-(f\<cdot>(x, y)) = \<infinity>)
  \<and> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>(x, y)))) = min (#\<^sub>-x) (Fin 1 + #\<^sub>-(\<alpha>\<^sub>-y)))
}"

definition ALICE_alt :: "(('d tsyn stream \<times> bool tsyn stream) \<rightarrow> ('d \<times> bool) tsyn stream) set" where
"ALICE_alt =  {spf | spf. \<forall>s.  (tsyn2ustream\<cdot>(tsynProjFst\<cdot>(\<alpha>\<^sub>-(spf\<cdot>s))) \<sqsubseteq> tsyn2ustream\<cdot>(fst s))}"

definition EVENonDiscr:: "('a tsyn stream \<rightarrow> 'a tsyn stream) set" where
  "EVENonDiscr \<equiv> {\<Lambda> s.  tsynBoolFilter\<cdot>s\<cdot>ora | ora. #({True} \<ominus> ora)=\<infinity>}"
                                
definition EVENonDiscr_equiv :: "('a tsyn stream \<rightarrow> 'a tsyn stream) set" where
  "EVENonDiscr_equiv \<equiv> {f. \<exists>ora. \<forall>s. (f\<cdot>s =  tsynBoolFilter\<cdot>s\<cdot>ora)  \<and> #({True} \<ominus> ora) = \<infinity>}"

definition EveNice :: "'a tsyn stream \<rightarrow> 'a tsyn stream"
where
  "EveNice \<equiv> \<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>((\<up>True)\<^sup>\<infinity>)"

definition EveN ::  "('a tsyn stream \<rightarrow> 'a tsyn stream) set" where
  "EveN \<equiv> {f. \<exists>n :: nat. \<forall>s. (f\<cdot>s = tsynBoolFilter\<cdot>s\<cdot>((\<up>True \<Zcat> (sntimes n (\<up>False)))\<^sup>\<infinity>))}"

definition EVE :: "('a tsyn stream \<rightarrow> 'a tsyn stream) set" where
"EVE \<equiv> {f. \<forall>i. \<exists>ora. f\<cdot>i = tsynBoolFilter\<cdot>i\<cdot>ora \<and> #({True} \<ominus> ora) = \<infinity>}"

definition EVEunfair :: "('a tsyn stream \<rightarrow> 'a tsyn stream) set" where
"EVEunfair \<equiv> {f. \<forall>i. \<exists>ora. f\<cdot>i = tsynBoolFilter\<cdot>i\<cdot>ora \<and> #ora = \<infinity>}"

abbreviation EVE1 ::"(('a \<times> bool) tsyn stream \<rightarrow> ('a \<times> bool) tsyn stream) set"
  where "EVE1 \<equiv> EVE"

abbreviation EVE2 :: "(bool tsyn stream \<rightarrow> bool tsyn stream) set"
  where "EVE2 \<equiv> EVE"

abbreviation EVE1unfair :: "(('a \<times> bool) tsyn stream \<rightarrow> ('a \<times> bool) tsyn stream) set"
  where "EVE1unfair \<equiv> EVEunfair"

abbreviation EVE2unfair :: "(bool tsyn stream \<rightarrow> bool tsyn stream) set"
  where "EVE2unfair \<equiv> EVEunfair"

lemma eve_eq: "EVENonDiscr = EVENonDiscr_equiv" 
  apply (simp add: EVENonDiscr_def)
  apply (simp add: EVENonDiscr_equiv_def)
  apply auto
  by (metis (lifting) ext Cfun.cfun.Rep_cfun_inverse)

lemma completedEVE_h1:
  shows "(\<forall>sb. \<exists>spf2. (\<exists>ora. spf2 =  (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>ora) \<and> #({True} \<ominus> ora) = \<infinity>) \<and> x\<cdot>sb = spf2\<cdot>sb)
    \<Longrightarrow> \<exists>ora. x\<cdot>s =  tsynBoolFilter\<cdot>s\<cdot>ora \<and> #({True} \<ominus> ora) = \<infinity>"
proof -
  assume H: "\<forall>sb. \<exists>spf2. (\<exists>ora. spf2 = (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>ora) \<and> #({True} \<ominus> ora) = \<infinity>) \<and> x\<cdot>sb = spf2\<cdot>sb"
  from H obtain spf2 where A:
    "(\<exists>ora. spf2 = (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>ora) \<and> #({True} \<ominus> ora) = \<infinity>) \<and> x\<cdot>s = spf2\<cdot>s"
    by blast
  from A obtain ora where B: "spf2 =  (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>ora)" and C: " #({True} \<ominus> ora) = \<infinity>" by blast
  from A B have "x\<cdot>s = (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>ora)\<cdot>s" by simp
  also have "... =   tsynBoolFilter\<cdot>s\<cdot>ora" by simp  
  finally show "\<exists>ora. x\<cdot>s =   tsynBoolFilter\<cdot>s\<cdot>ora \<and>  #({True} \<ominus> ora) = \<infinity>" using C by blast
qed

lemma completedEVE_h2:
  fixes x  :: "'a tsyn stream \<rightarrow> 'a tsyn stream"
    and sb :: "'a tsyn stream"
  assumes H:
    "\<forall>s. \<exists>ora. x\<cdot>s = tsynBoolFilter\<cdot>s\<cdot>ora
          \<and> #({True} \<ominus> ora) = \<infinity>"
  shows "\<exists>spf2 :: 'a tsyn stream \<rightarrow> 'a tsyn stream.
           (\<exists>ora. spf2 = (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>ora)
                 \<and> #({True} \<ominus> ora) = \<infinity>)
           \<and> x\<cdot>sb = spf2\<cdot>sb"
proof -
  from H obtain ora where X:
      "x\<cdot>sb = tsynBoolFilter\<cdot>sb\<cdot>ora"
    and P: "#({True} \<ominus> ora) = \<infinity>"
  by blast
  define spf2 :: "'a tsyn stream \<rightarrow> 'a tsyn stream"  where
    "spf2 = (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>ora)"
  have "x\<cdot>sb = spf2\<cdot>sb" by (simp add: X spf2_def)
  moreover have
    "\<exists>ora. spf2 = (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>ora)
           \<and> #({True} \<ominus> ora) = \<infinity>"
    by (intro exI[of _ ora]) (simp add: spf2_def P)
  ultimately show ?thesis by blast
qed

lemma completedEVE: "spsComplete EVENonDiscr = EVE"
  apply (simp add: spsComplete_def)
  apply (simp add: EVE_def)
  apply (simp add: EVENonDiscr_def)
  apply auto
  subgoal 
    apply (rule completedEVE_h1)
    by auto
  apply (rule completedEVE_h2)
  by auto

lemma EVENonDiscr_subset_EVE: "EVENonDiscr \<subseteq> EVE"
  using completedEVE spscomplete_below  
  by auto

lemma "EveNice \<in> EVENonDiscr"
  apply (simp add: EveNice_def EVENonDiscr_def tsynboolfilter_lemmas)
  apply (rule_tac x="((\<up>True)\<^sup>\<infinity>)" in exI)
  by (simp add: tsynboolfilter_lemmas)

lemma "EveNice \<in> EVE "
  apply (simp add: EveNice_def EVE_def )
  by auto


definition f_discr :: "bool tsyn stream \<rightarrow> bool  tsyn stream" where
  "f_discr \<equiv> \<Lambda> s. (slookahd\<cdot>s\<cdot>(\<lambda>x. if x = TSynMsg True
           then tsynBoolFilter\<cdot>s\<cdot>(\<up>False \<Zcat> ((\<up>True)\<^sup>\<infinity>))
           else tsynBoolFilter\<cdot>s\<cdot>((\<up>True)\<^sup>\<infinity>)))"

lemma f_discr_cont [simp]: "cont (\<lambda>s. (slookahd\<cdot>s\<cdot>(\<lambda>x. if x = TSynMsg True
           then tsynBoolFilter\<cdot>s\<cdot>(\<up>False \<Zcat> ((\<up>True)\<^sup>\<infinity>))
           else tsynBoolFilter\<cdot>s\<cdot>((\<up>True)\<^sup>\<infinity>))))"
  by (intro cont2cont)

definition sT :: "bool tsyn stream" where
  "sT \<equiv> (\<up>(TSynMsg True))\<^sup>\<infinity>"

lemma filter_sT_false_trueinf:
  "tsynBoolFilter\<cdot>sT\<cdot>(\<up>False \<Zcat> ((\<up>True)\<^sup>\<infinity>)) = \<up>\<sim> \<Zcat> sT"
  by (metis sT_def sinftimes_unfold tsynboolfilter_inf_true tsynboolfilter_msg_false_rec)

lemma "f_discr \<notin> EVENonDiscr"
proof
  assume "f_discr \<in> EVENonDiscr"
  then obtain ora where
    Rep: "f_discr = (\<Lambda> s.  (tsynBoolFilter\<cdot>s\<cdot>ora))"
    by (auto simp: EVENonDiscr_def)

  have T1: "f_discr\<cdot>sT = tsynBoolFilter\<cdot>sT\<cdot>(\<up>False \<Zcat> ((\<up>True)\<^sup>\<infinity>))"
    by (simp add: f_discr_def sT_def)
  from Rep have "\<dots> = tsynBoolFilter\<cdot>sT\<cdot>ora" 
    by (metis (no_types, lifting) T1 ext beta_cfun tsynboolfilter_cont)
  then have T1e: " \<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>(\<up>(TSynMsg True) \<Zcat> ((\<up>(TSynMsg True))\<^sup>\<infinity>))\<cdot>(\<up>False \<Zcat> ((\<up>True)\<^sup>\<infinity>)) 
        =  \<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>(\<up>(TSynMsg True) \<Zcat> ((\<up>(TSynMsg True))\<^sup>\<infinity>))\<cdot>ora"
    using  sinftimes_unfold  by (metis sT_def)
   have eqT: "\<exists> bs. ora = (\<up>False \<Zcat> bs)"
    using T1e  sconc_inj'  tsynboolfilter_shd_inj
    by blast 

  define sF where "sF = ((\<up>(TSynMsg False))\<^sup>\<infinity>)"
  have F1: "f_discr\<cdot>sF =  tsynBoolFilter\<cdot>sF\<cdot>((\<up>True)\<^sup>\<infinity>)"
    by (simp add: f_discr_def sF_def)
    also from Rep have "\<dots> = tsynBoolFilter\<cdot>sF\<cdot>ora" 
    by (metis (no_types, lifting) ext beta_cfun calculation tsynboolfilter_cont)
   then have "\<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>(\<up>(TSynMsg False) \<Zcat> ((\<up>(TSynMsg False))\<^sup>\<infinity>))\<cdot>((\<up>True)\<^sup>\<infinity>) 
            =  \<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>(\<up>(TSynMsg False) \<Zcat> ((\<up>(TSynMsg False))\<^sup>\<infinity>))\<cdot>ora " 
      by (metis sF_def sinftimes_unfold)
  then have F1e: "\<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>(\<up>(TSynMsg False) \<Zcat> ((\<up>(TSynMsg False))\<^sup>\<infinity>))\<cdot>(\<up>True \<Zcat>((\<up>True)\<^sup>\<infinity>))
            =  \<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>(\<up>(TSynMsg False) \<Zcat> ((\<up>(TSynMsg False))\<^sup>\<infinity>))\<cdot>ora " 
      by (metis sF_def sinftimes_unfold)
  have eqF: "\<exists> bs. ora = (\<up>True \<Zcat> bs)"
    using F1e  sconc_inj'  sinftimes_unfold tsynboolfilter_shd_inj
    by blast 
  from eqT eqF show False 
  by (metis shd1)
qed

lemma "f_discr \<in> EVE"
  apply (simp add: f_discr_def EVE_def)
  apply (intro allI)
  apply (case_tac i)
   apply auto
  by (metis sfilter_sinftimes_in slen_sup_sinftimes tsynboolfilter_inf_true)

lemma trues_in_sinftimes_infinite: "#({True} \<ominus> ((\<up>True \<Zcat> sntimes n (\<up>False))\<^sup>\<infinity>)) = \<infinity>"
  by (simp add: slen_sinftimes)

lemma EveNsubsetEve: "EveN \<subseteq> EVENonDiscr"  
  apply (simp add: eve_eq EVENonDiscr_equiv_def EveN_def)
  apply (intro subsetI)
  apply (erule CollectE)   
  apply (elim exE conjE)
  apply (rename_tac f n)
  apply (rule CollectI)
  apply (rule_tac x="((\<up>True \<Zcat> sntimes n (\<up>False))\<^sup>\<infinity>)" in exI)
  apply (intro conjI allI)
  apply simp
  using trues_in_sinftimes_infinite by blast

lemma "EveN \<subseteq> EVE"
  using EveNsubsetEve EVENonDiscr_subset_EVE
  by auto

definition f_ftinf :: "bool tsyn stream \<rightarrow> bool  tsyn stream" where
  "f_ftinf \<equiv> \<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>((\<up>False \<Zcat>((\<up>True)\<^sup>\<infinity>)))"

lemma "f_ftinf \<in> EVENonDiscr"
  apply (simp add: f_ftinf_def EVENonDiscr_def)
  apply (rule_tac x="((\<up>False \<Zcat>((\<up>True)\<^sup>\<infinity>)))" in exI)
  by (simp add: tsynboolfilter_lemmas)

lemma "f_ftinf \<notin> EveN"
  apply (simp add: f_ftinf_def EveN_def)
  apply (subst (2) sinftimes_unfold)
  apply (intro allI)
  apply (rule_tac x="(\<up>(TSynMsg d))\<^sup>\<infinity>" in exI)
  apply (subst sinftimes_unfold)
  apply (subst (3) sinftimes_unfold)
  apply (simp add: tsynboolfilter_lemmas) 
  by (metis inject_scons tsyn.distinct(1))

lemma "EveNice \<in> EveN" 
  apply (simp add: EveNice_def EveN_def)
  apply (rule_tac x=0 in exI)  
  by (simp add: tsynboolfilter_lemmas)

lemma eve_weak_causal: "\<forall> eve\<in>EVE. weak eve"
  apply (simp add: strong_def EVE_def weak_def)
  apply auto 
  by (metis sfilterl4 lnat_po_eq_conv slen_tsynboolfilter)

definition tsynBoolFilter_A1 :: "'a tsyn stream \<rightarrow> bool stream \<rightarrow> 'a tsyn stream" where
"tsynBoolFilter_A1 \<equiv> \<Lambda> s1 s2. smap (\<lambda> pair. if snd pair then fst pair else \<sim>)\<cdot>(szip\<cdot>s1\<cdot>s2)"

definition MedInfTrueInOraUnfair:: "('d tsyn stream \<rightarrow> 'd tsyn stream) set" where
  "MedInfTrueInOraUnfair \<equiv> {\<Lambda> s.  tsynBoolFilter_A1\<cdot>s\<cdot>ora | ora. #({True} \<ominus> ora)=\<infinity>}"

lemma tsynBoolFilter_A1_msg_false_rec: "tsynBoolFilter_A1\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(\<up>False \<Zcat> bs) = \<up>\<sim> \<Zcat> tsynBoolFilter_A1\<cdot>as\<cdot>bs"
  by (simp add: tsynBoolFilter_A1_def)

lemma tsynBoolFilter_A1_eps_bool_rec: "tsynBoolFilter_A1\<cdot>(\<up>\<sim> \<Zcat> as)\<cdot>(\<up>b \<Zcat> bs) = \<up>\<sim> \<Zcat> tsynBoolFilter_A1\<cdot>as\<cdot>bs"
  by (simp add: tsynBoolFilter_A1_def)

lemma tsynBoolFilter_A1_unfair: "tsynBoolFilter_A1\<cdot>((\<up>(TSynMsg (Suc 0)) \<Zcat> \<up>\<sim>)\<^sup>\<infinity>)\<cdot>((\<up>False \<Zcat> \<up>True)\<^sup>\<infinity>) = ((\<up>\<sim>)\<^sup>\<infinity>)"
proof -
define s
  where "s = tsynBoolFilter_A1\<cdot>\<up>(TSynMsg (Suc 0)) \<Zcat> \<up>\<sim>\<^sup>\<infinity>\<cdot>\<up>False \<Zcat> \<up>True\<^sup>\<infinity>"
have fp: "s = (\<up>\<sim> \<Zcat> \<up>\<sim>) \<Zcat>  s"
  unfolding s_def
  apply (subst (1 2)sinftimes_unfold)
  by (simp add: tsynBoolFilter_A1_msg_false_rec tsynBoolFilter_A1_eps_bool_rec ) 
then have s_eq: "s = sinftimes (\<up>\<sim> \<Zcat> \<up>\<sim>)"
  by (rule rek2sinftimes) simp 
with s_eq show ?thesis unfolding s_def by (simp add: sinftimes_sconc)
qed

lemma medInfTrueInOraUnfair_is_unfair: 
  "\<exists>i:: nat tsyn stream. #(tsyn2ustream\<cdot>i) = \<infinity> \<and> (\<exists>eve\<in>MedInfTrueInOraUnfair. #(tsyn2ustream\<cdot>(eve\<cdot>i)) \<noteq> \<infinity>)"
  apply (rule_tac x="((<[TSynMsg 1, \<sim>]>)\<^sup>\<infinity>)" in exI)
  unfolding MedInfTrueInOraUnfair_def
  apply (simp add: tsyn2ustream_def)
  apply  (rule_tac x="( \<Lambda> s. tsynBoolFilter_A1\<cdot>s\<cdot>((<[False, True]>)\<^sup>\<infinity>))" in exI)
  apply (intro conjI) 
   apply (rule_tac x="((<[False, True]>)\<^sup>\<infinity>)" in exI)
   apply auto
  by (simp add: tsynBoolFilter_A1_unfair)


lemma fairfilter_singelton_eps: "\<And>ora. #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> tsynBoolFilter\<cdot>(\<up>\<sim>)\<cdot>ora = \<up>\<sim>"
  using tsynboolfilter_Eps_infinite sfilterl4 by blast

lemma fairfilter_eps_rec: "\<And>ora. #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> tsynBoolFilter\<cdot>(\<up>\<sim> \<Zcat> s)\<cdot>(\<up>y \<Zcat> ora) = \<up>\<sim> \<Zcat> tsynBoolFilter\<cdot>s\<cdot>(\<up>y \<Zcat> ora)"
  by (simp add: tsynboolfilter_lemmas)  

lemma eve_empty: "\<forall>med \<in> EVE. med\<cdot>\<epsilon> =  \<epsilon>"
  apply (simp add: EVE_def)
  apply auto
  by (metis strict_tsynboolfilter_fst)
 
lemma eve_singelton: "\<forall>med \<in> EVE. med\<cdot>(\<up>\<sim>) = \<up>\<sim>"
  apply (simp add: EVE_def)
  apply auto
  using tsynboolfilter_Eps_infinite sfilterl4  
  by (metis (no_types, lifting))

lemma eve_unfair_empty: "\<forall>med \<in> EVEunfair. med\<cdot>\<epsilon> = \<epsilon>"
  apply (simp add: EVEunfair_def)
  apply auto
  by (metis strict_tsynboolfilter_fst)

lemma eve_unfair_singelton: "\<forall>med \<in> EVEunfair. med\<cdot>(\<up>\<sim>) = \<up>\<sim>"
  apply (simp add: EVEunfair_def)
  apply auto
  by (metis tsynboolfilter_Eps_infinite)
 
lemma eve_refines_eveunfair: "EVE \<subseteq> EVEunfair"
  apply (simp add: EVE_def EVEunfair_def)
  using sfilterl4 
  by blast

lemma eve1_refines_eve1unfair: "EVE1 \<subseteq> EVE1unfair"
  by (simp add: eve_refines_eveunfair)

lemma eve2_refines_eve2unfair: "EVE2 \<subseteq> EVE2unfair"
  by (simp add: eve_refines_eveunfair)

lemma eveunfair_unfair: "\<exists>med\<in>EVEunfair. med\<cdot>((\<up>x)\<^sup>\<infinity>) = ((\<up>\<sim>)\<^sup>\<infinity>)"
proof -
  define med  where "med ::  'a tsyn stream \<rightarrow> 'a tsyn stream \<equiv> (\<Lambda> i. tsynBoolFilter\<cdot>i\<cdot>((\<up>False)\<^sup>\<infinity>))"
  have med_in: "med \<in> EVEunfair"
    unfolding EVEunfair_def med_def
    by (intro CollectI allI exI[of _ "((\<up>False)\<^sup>\<infinity>)"] conjI)
       (simp_all add: tsynboolfilter_inf_const_false)
  moreover have "med\<cdot>((\<up>x)\<^sup>\<infinity>) = ((\<up>Eps)\<^sup>\<infinity>)"
    by (simp add: med_def tsynboolfilter_inf_const_false)
  hence "med\<cdot>((\<up>x)\<^sup>\<infinity>) = ((\<up>\<sim>)\<^sup>\<infinity>)" by simp  
  ultimately show ?thesis by blast
qed


definition ABPunfair :: "('d tsyn stream \<rightarrow> 'd tsyn stream) set" where
"ABPunfair \<equiv> {\<mu>(Alice \<circle> Eve1 \<circle> Bob \<circle> (ID \<parallel> Eve2)) \<circle> Fst | Alice Bob Eve1 Eve2. 
 Alice \<in> ALICE \<and> Bob \<in> BOB \<and> Eve1 \<in> EVE1unfair \<and> Eve2 \<in> EVE2unfair}"


definition ABP :: "('d tsyn stream \<rightarrow> 'd tsyn stream) set" where
"ABP \<equiv> {\<mu>(Alice \<circle> Eve1 \<circle> Bob \<circle> (ID \<parallel> Eve2)) \<circle> Fst | Alice Bob Eve1 Eve2. 
 Alice \<in> ALICE \<and> Bob \<in> BOB \<and> Eve1 \<in> EVE1 \<and> Eve2 \<in> EVE2}"


lemma alice_empty: "Alice_LLR\<cdot>(\<epsilon>, x)=\<up>\<sim>"
  by (simp add: Alice_LLR_def semanticMapping_def)

lemma bob_empty: "Bob\<cdot>\<epsilon> = (\<up>\<sim>,\<up>\<sim>)"
  by (simp add: Bob_def semanticMapping_def tsynprojfst_singleton_Eps)

lemma bob_inf_eps: "Bob\<cdot>(((\<up>\<sim>)\<^sup>\<infinity>)) = (((\<up>\<sim>)\<^sup>\<infinity>), ((\<up>\<sim>)\<^sup>\<infinity>))"
  apply (simp add: Bob_def semanticMapping_def)
  apply auto
   using  s2sinftimes sinftimes_unfold tsynprojfst_sconc_Eps 
   apply (metis tsynremdups_sconc_eps)
  using  s2sinftimes sinftimes_unfold
  apply (metis tsynprojsnd_sconc_Eps)  
  done

lemma alice_inf_eps: "Alice_LLR\<cdot>(((\<up>\<sim>)\<^sup>\<infinity>), ((\<up>\<sim>)\<^sup>\<infinity>)) = ((\<up>\<sim>)\<^sup>\<infinity>)"
 apply (simp add: Alice_LLR_def semanticMapping_def)
 using S1 case_prod_conv s2sinftimes sinftimes_unfold sprojfst_scons sscanl_scons
  by smt

lemmas eve_lemmas = eve_empty eve_singelton fairfilter_singelton_eps
                     fairfilter_eps_rec eveunfair_unfair  
                     eve_refines_eveunfair

lemmas unfair_eve_lemmas =  eve_unfair_empty eve_unfair_singelton
      tsynfilter_fitandzip_infFalse eveunfair_unfair eve_refines_eveunfair
                eve1_refines_eve1unfair eve2_refines_eve2unfair 

lemmas alice_bob_lemmas = alice_empty bob_empty bob_inf_eps alice_inf_eps 

lemmas tsynzip_lemmas = tsynzip_sconc_msg tsynzip_sconc_Eps
        tsynzip_Eps_sconc tsynzip_Eps_singeltons 
       tsynzip_msg_singeltons tsynzip_tsynabs tsynzip_tsynabs2
       tsynzip_tsynabs_image

lemma abp_refine : "ABP \<subseteq> ABPunfair"
  apply (simp add: ABP_def ABPunfair_def)
  using eve1_refines_eve1unfair eve2_refines_eve2unfair
  by blast

lemma tsyndom_eve_in: "\<forall>g \<in> EVE. a \<in> tsynValues\<cdot>(g\<cdot>y) \<longrightarrow>  a \<in> tsynValues\<cdot>y"
  apply (intro ballI)
  apply (simp add: EVE_def)
 using tsyndom_tsynboolfilter_in 
  by metis

lemma tsyndom_eve_subseteq: "\<forall>g \<in> EVE. tsynValues\<cdot>(g\<cdot>y) \<subseteq> tsynValues\<cdot>y" 
  using tsyndom_eve_in 
  by auto

definition EveTF :: "'a tsyn stream \<rightarrow> 'a tsyn stream"
where
  "EveTF \<equiv> \<Lambda> s.  tsynBoolFilter\<cdot>s\<cdot>((\<up>True\<Zcat>\<up>False)\<^sup>\<infinity>)"

lemma assumes "y = ((\<up>(TSynMsg (1::nat))\<Zcat>\<up>(TSynMsg 2)))" 
  shows"tsynValues\<cdot>(EveTF\<cdot>y) \<subset> tsynValues\<cdot>y"
  using assms apply (simp add: EveTF_def)
  apply (subst sinftimes_unfold)
  apply (simp add: tsynboolfilter_lemmas tsyndom_singleton_Eps tsyndom_singleton_msg)
  by fastforce

lemma "tsynValues\<cdot>(EveNice\<cdot>y) = tsynValues\<cdot>y"
  by (simp add: EveNice_def tsynboolfilter_lemmas)

lemma tsynlen_eve: "\<forall>g\<in>EVE. #\<^sub>-y \<ge> #\<^sub>-(g\<cdot>y)"
  apply (intro ballI)
  apply (simp add: EVE_def)
 using tsynlen_boolfilter 
  by (metis sfilterl4)

lemma assumes "y = ((\<up>(TSynMsg (1::nat))\<Zcat>\<up>(TSynMsg 2)))" 
  shows" #\<^sub>-y > #\<^sub>-(EveTF\<cdot>y)"
  using assms apply (simp add: EveTF_def)
  apply (subst sinftimes_unfold)
  by (simp add: tsynboolfilter_lemmas tsynlen_sconc_Eps tsynlen_sconc_msg 
        tsynlen_singleton_msg tsynlen_singleton_Eps )

lemma " #\<^sub>-y = #\<^sub>-(EveNice\<cdot>y)"
  by (simp add: EveNice_def tsynboolfilter_lemmas tsynlen_sconc_Eps)

lemma lemma0: "\<forall>g \<in> EVE. #\<^sub>-(\<alpha>\<^sub>-y) \<ge> #\<^sub>-(\<alpha>\<^sub>-(g\<cdot>y))"
  apply (simp add: EVE_def)
  using tsynlen_remdups_boolfilter_leq by metis

lemma "\<exists>y:: bool tsyn stream. #\<^sub>-(\<alpha>\<^sub>-y) > #\<^sub>-(\<alpha>\<^sub>-(EveTF\<cdot>y))"
  apply (simp add: EveTF_def)
  apply (rule_tac x="(\<up>(TSynMsg True) \<Zcat> \<up>(TSynMsg False) \<Zcat>\<up>(TSynMsg True) \<Zcat> \<up>(TSynMsg False))" in exI)
  apply (subst sinftimes_unfold)
  apply (subst sinftimes_unfold)
  apply (simp add: tsynboolfilter_lemmas)
  apply (simp add: tsynremdups_unfold)
  by (simp add: tsynlen_sconc_Eps tsynlen_sconc_msg tsynlen_singleton_Eps)
  
lemma "#\<^sub>-(\<alpha>\<^sub>-y) = #\<^sub>-(\<alpha>\<^sub>-(EveNice\<cdot>y))"
  apply (simp add: EveNice_def)
  by (simp add: tsynboolfilter_lemmas)

lemma 03: "\<forall>f\<in>EVE1. #\<^sub>-(\<Pi>\<^sub>2\<^sub>-y) \<ge> #\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y))"
  by (simp add: tsynlen_eve tsynprojsnd_tsynlen)

lemma "y=<[TSynMsg (True, True), TSynMsg (True, True)  ]>  \<longrightarrow> #\<^sub>-(\<Pi>\<^sub>2\<^sub>-y) > #\<^sub>-(\<Pi>\<^sub>2\<^sub>-(EveTF\<cdot>y))"
  apply(simp add: EveTF_def tsynboolfilter_lemmas tsynprojsnd_tsynlen)
  apply (subst sinftimes_unfold)
  apply (subst sinftimes_unfold)
  by (simp add: tsynboolfilter_lemmas tsynlen_insert)

lemma " #\<^sub>-(\<Pi>\<^sub>2\<^sub>-y) = #\<^sub>-(\<Pi>\<^sub>2\<^sub>-(EveNice\<cdot>y))"
  by (simp add: EveNice_def tsynboolfilter_lemmas tsynprojsnd_tsynlen)

lemma 05: "\<forall>f\<in>EVE1. #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))"
  apply (simp add: EVE_def)
  using tsynlen_remdups_boolfilter_leq tsynboolfilter_tsynprojsnd_distr 
  by metis

lemma "y=<[TSynMsg (True, True), TSynMsg (True, True)  ]>  \<longrightarrow> #\<^sub>-(\<Pi>\<^sub>2\<^sub>-y) > #\<^sub>-(\<Pi>\<^sub>2\<^sub>-(EveTF\<cdot>y))"
  apply(simp add: EveTF_def tsynboolfilter_lemmas tsynprojsnd_tsynlen)
  apply (subst sinftimes_unfold)
  apply (subst sinftimes_unfold)
  by (simp add: tsynboolfilter_lemmas tsynlen_insert)

lemma " #\<^sub>-(\<Pi>\<^sub>2\<^sub>-y) = #\<^sub>-(\<Pi>\<^sub>2\<^sub>-(EveNice\<cdot>y))"
  by (simp add: EveNice_def tsynboolfilter_lemmas tsynprojsnd_tsynlen)

lemma bob_tsynlen_fst: "#\<^sub>-(Fst\<cdot>(Bob\<cdot>y)) = #\<^sub>-(\<alpha>\<^sub>-y)"
  apply (simp add: Bob_def)
  by (simp add: Fst_apply tsynprojfst_tsynlen tsynlen_sconc_Eps)


lemma   
  fixes y :: "(nat \<times> bool) tsyn stream"
  defines "y \<equiv> <[ TSynMsg (1, True), TSynMsg (2, False), TSynMsg (3, True) ]>"
  shows"#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) > #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> EveTF)\<cdot>(Bob\<cdot>(EveTF\<cdot>y)))))" 
  apply (simp add: y_def Bob_def EveTF_def parComp_def Snd_apply)
  apply (subst sinftimes_unfold)
  apply (subst sinftimes_unfold)
  apply (simp add: tsynprojsnd_sconc_msg tsynprojsnd_singleton_msg tsynboolfilter_lemmas)
   apply (subst sinftimes_unfold)
  apply (subst sinftimes_unfold)
  apply (simp add: tsynprojsnd_sconc_msg tsynprojsnd_sconc_Eps tsynprojsnd_singleton_msg tsynboolfilter_lemmas)
  by (simp add: tsynremdups_unfold tsynlen_insert)

lemma "#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> EveNice)\<cdot>(Bob\<cdot>(EveNice\<cdot>y)))))" 
  by (simp add: Bob_def EveNice_def parComp_def Snd_apply tsynboolfilter_inf_true tsynlen_sconc_Eps tsynremdups_sconc_eps)

lemma liveMed: "#\<^sub>-i = \<infinity> \<longrightarrow> (\<forall>f \<in> EVE. #\<^sub>-(f\<cdot>i) = \<infinity>)"
  apply (simp add: EVE_def)
  using tsynboolfilter_live by metis

lemma lemma3: "#\<^sub>-y = \<infinity> \<longrightarrow> (\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>y)))) = \<infinity>)"
proof
  assume inf_y: "#\<^sub>-y = \<infinity>"
  have live_f: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. (#\<^sub>-(f\<cdot>y)) = \<infinity>"
    by (simp add: inf_y liveMed)
  have live_proj2: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. (#\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y))) = \<infinity>"
    by (simp add: live_f tsynprojsnd_tsynlen)
  have live_g: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(g\<cdot>(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y))) = \<infinity>"
    by (simp add: inf_y liveMed live_proj2)
  have bob2: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>y)))) = #\<^sub>-(g\<cdot>(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))"
    apply (simp add: parComp_def Snd_def Bob_def )
    by (metis liveMed live_proj2 tsynlen_sconc_Eps) 
  from inf_y live_f live_proj2 live_g bob2 live_g show
    "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>y)))) = \<infinity>" by simp
qed

lemma lemma4: 
  assumes fin: "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) < \<infinity>"
  and eq1: "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))"
  and eq2: "\<forall>f \<in> EVE1. #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))"  
  shows "\<forall>f \<in> EVE1. tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) = tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>y)))" 
proof
  fix f:: "(('a \<times> bool) tsyn stream \<rightarrow> ('a \<times> bool) tsyn stream)" 
  assume fE: "f \<in> EVE1"
  then obtain ora where f_def: "f\<cdot>y = tsynBoolFilter\<cdot>y\<cdot>ora" and ora_inf:"#ora=\<infinity>"
    using EVE_def sfilterl4 by force
  thus "tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) = tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>y)))"
    by (metis eq1 eq2 fE fin tsynprojfst_tsynremdups_tsynbolfilter_id_if_fin_tsynlen_eq)
qed

lemma lemma1: "\<forall>f \<in> EVE. \<forall>g \<in> EVE. #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>y)))))"
proof -
  have "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(g\<cdot>(\<up>\<sim>\<Zcat>\<Pi>\<^sub>2\<^sub>-(f\<cdot>y))))"
    by (metis (no_types, lifting) "05" dual_order.trans lemma0 tsynlen_tsynremdups_cons_eps)
  also have "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(\<alpha>\<^sub>-(g\<cdot>(\<up>\<sim>\<Zcat>\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))) = #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>y)))))"
    by (simp add: Snd_apply parComp_def parComp_Fst Bob_def) 
  ultimately show ?thesis 
    by fastforce
qed





lemma ID_is_medium: "ID \<in> EVE"
unfolding EVE_def  
proof -
  have "\<forall>s. \<exists>sa. ID\<cdot>s = tsynBoolFilter\<cdot>s\<cdot>sa \<and> #({True} \<ominus> sa) = \<infinity>"
    by (metis (no_types) ID1 sfilter_sinftimes_in slen_sup_sinftimes tsynboolfilter_inf_true)
  then show "ID \<in> {c. \<forall>s. \<exists>sa. c\<cdot>s = tsynBoolFilter\<cdot>s\<cdot>sa \<and> #({True} \<ominus> sa) = \<infinity>}"
    by blast
qed

lemma tsyn_abp_fp:
  fixes x
  assumes "Med1 \<in> EVE1"  
  assumes "Med2 \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  defines "as \<equiv> (\<mu> (Sender \<circle> Med1 \<circle> Receiver \<circle> (ID \<parallel> Med2)) \<circle> Snd)\<cdot>x"
  shows   "as = Snd\<cdot>(((ID \<parallel> Med2)\<cdot>(Receiver\<cdot>(Med1\<cdot>(Sender \<cdot>(x, as))))))"
  unfolding as_def mu_def
  apply(subst fix_eq)
  apply (subst helper) by(simp)

lemma tsyn_abp_fp_len_h1:
  fixes x
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<alpha>\<^sub>-as) \<le> #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(Sender\<cdot>(x,as))))"
proof -  
  have "Receiver = Bob"
    by (metis assms(3) singletonD BOB_def)
  also have "#\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>(Sender \<cdot>(x, as)))))))
          \<le>  #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(Sender\<cdot>(x,as))))" 
    using lemma1
    by (metis assms(1,2))
  ultimately show ?thesis 
    using assms by fastforce
qed

lemma tsyn_abp_S2:
  assumes "#x = \<infinity>" and "#y = \<infinity>"
  assumes "Sender \<in> ALICE"
  shows "srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>(Sender\<cdot>(x, y))))) = sprojsnd\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>(Sender\<cdot>(x, y))))"
  using ALICE_def assms  
  by auto 

lemma tsyn_abp_S3:
  assumes "#x = \<infinity>" and "#y = \<infinity>"
  assumes "Sender \<in> ALICE"
  shows "#\<^sub>-(\<alpha>\<^sub>-y) < #\<^sub>-x \<longrightarrow> #\<^sub>-(Sender\<cdot>(x, y)) = \<infinity>"
  using ALICE_def assms  
  by auto 

lemma abp_tsyn_S3b:
  assumes "#x = \<infinity>" and "#y = \<infinity>"
  assumes "Sender \<in> ALICE"
  shows "(#\<^sub>-x \<le> #\<^sub>-(\<alpha>\<^sub>-y) \<and> #\<^sub>-x < \<infinity>) \<longrightarrow> #\<^sub>-(Sender\<cdot>(x, y)) < \<infinity>"
  using ALICE_def assms oops

lemma tsyn_abp_S4:
  assumes "#x = \<infinity>" and "#y = \<infinity>"
  assumes "Sender \<in> ALICE"
  shows "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x, y)))) =  min (#\<^sub>-x) (Fin 1 + #\<^sub>-(\<alpha>\<^sub>-y))"
  using ALICE_def assms  
  by auto 

lemma parComp_Snd: "Snd\<cdot>((f \<parallel> g)\<cdot>(x,y)) = g\<cdot>y"
  by (simp add: parComp_def Snd_def)

lemma parComp_Snd2: "Snd\<cdot>((f \<parallel> g)\<cdot>z) = g\<cdot>(Snd\<cdot>(z))"
  apply(cases z)
  apply(simp add: parComp_Snd)
  by(simp add: Snd_def)

lemma tsyn_abp_inf_x_as :
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#as = \<infinity>"
proof -
  have s:"strong Sender"  using assms(5) ALICE_def  by auto 
  then have 0:"lnsuc\<cdot>(#as) \<le> #(Sender\<cdot>(x,as))"
    using assms(1) strong_def
    by (metis tlen_len_eq tlen_prod_inf_fst)
  have a:"\<And>x. #(f\<cdot>x) = #x"
    using assms(2) EVE_def
    by (smt mem_Collect_eq sfilterl4 slen_tsynboolfilter)
  have b:"\<And> x y. #(Receiver\<cdot>(x)) = lnsuc\<cdot>(#x)"
    apply(subgoal_tac "Receiver=Bob")apply(simp add: Bob_def)
     apply(simp add: len_prod_def tsynprojfst_slen tsynprojsnd_slen)
    using assms(4) BOB_def by auto
  have c:"\<And>x. #(g\<cdot>x) = #x"
    using assms(3) EVE_def
    by (smt mem_Collect_eq sfilterl4 slen_tsynboolfilter)
  show ?thesis 
  proof(rule ccontr)
    assume fin:"#as\<noteq>\<infinity>"
    then obtain n where n_def:"#as = Fin n"
      using LNat.LNat.lnat.exhaust by blast
    then have "Fin n < #(Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as))))))"
      apply(simp add: parComp_Snd2 parComp_Snd a b c)
      apply(cases "Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x, as)))",simp add: Snd_def)
      apply(subgoal_tac "#(a,b) \<le> #b")
      apply(subgoal_tac "Fin n < #(a,b)") 
      using dual_order.strict_trans1 apply blast
      apply (metis "0" a b fin fin_le_inf le2lnle linorder_linear lnle_and_gt_inf(1) lnsuc_inf) 
      using len_prod_minr by blast
    thus False
      using assms(6) n_def by auto
  qed
qed

lemma tsyn_abp_live2: 
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows  "#\<^sub>-(Sender\<cdot>(x,as)) = \<infinity> \<Longrightarrow> #\<^sub>-as = \<infinity>"
  using BOB_def assms 
  by (metis lemma3 singleton_iff)

lemma ustream_L7: 
  assumes "srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot> f)) = sprojsnd\<cdot>(srcdups\<cdot> f)" 
  shows " #(sprojfst\<cdot>(srcdups\<cdot> f)) =  #(srcdups\<cdot>(sprojsnd\<cdot> f))"
  using srcdups_sprojsnd_srcdups 
  by (metis assms slen_sprojs_eq)

lemma L7: 
  assumes "srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>x))) = sprojsnd\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>x))" 
  shows " (#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-x))) =  (#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-x))) "
  using assms ustream_L7
  by (metis tsynlen_insert tsynprojfst_tsynabs tsynprojsnd_tsynabs tsynremdups_tsynabs)

lemma tsyn_abp_len_x_sender_leq: 
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-x \<ge> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as))))" 
proof - 
  have "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) = min (#\<^sub>-x) (Fin 1 +  #\<^sub>-(\<alpha>\<^sub>-as))"
   using ALICE_def assms tsyn_abp_inf_x_as by blast
  then show ?thesis 
    by simp
qed

lemma B2:  
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-x < \<infinity> \<Longrightarrow> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) < \<infinity>" 
  using assms(1,2,3,4,5,6) dual_order.strict_trans2 tsyn_abp_S4 tsyn_abp_inf_x_as by fastforce

lemma B3:                               
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) = \<infinity> \<Longrightarrow> #\<^sub>-x = \<infinity>"
  using assms B2 
  by (metis inf_less_eq verit_comp_simplify1(3))

lemma B5:  
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) \<ge> #\<^sub>-(\<alpha>\<^sub>-(as))"
  using proj1_tsynremdups_proj2_tsynlen tsyn_abp_fp_len_h1 
  assms dual_order.trans by blast

lemma B7:  
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<alpha>\<^sub>-as) = \<infinity> \<Longrightarrow> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) = \<infinity>"
  using assms by (metis inf_less_eq proj1_tsynremdups_proj2_tsynlen tsyn_abp_fp_len_h1)

lemma tsyn_abp_fp_len_leq:  
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-x \<ge> #\<^sub>-(\<alpha>\<^sub>-(as)) "
  using assms tsyn_abp_len_x_sender_leq B5 by fastforce

lemma B9: "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,y)))) = \<infinity> \<Longrightarrow> #\<^sub>-(Sender\<cdot>(x,y)) = \<infinity>" 
  by (metis inf_less_eq tsynlen_tsynremdups_le tsynprojfst_tsynlen)

lemma B10: "#\<^sub>-(\<alpha>\<^sub>-(y)) = \<infinity> \<Longrightarrow> #\<^sub>-y = \<infinity>"
  by (metis inf_less_eq tsynlen_tsynremdups_le)

lemma B11:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-x < \<infinity> \<Longrightarrow> #\<^sub>-(\<alpha>\<^sub>-as) < \<infinity>"
  using assms B10 
  by (simp add: dual_order.strict_trans2 tsyn_abp_fp_len_leq)

lemma B12:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<alpha>\<^sub>-as) = \<infinity> \<Longrightarrow> #\<^sub>-x = \<infinity>"
  using assms B11 by (metis inf_less_eq verit_comp_simplify1(3))

lemma B13: "#\<^sub>-(Sender\<cdot>(x,y)) < \<infinity> \<Longrightarrow> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,y)))) < \<infinity>" 
  by (metis B9 tsynlen_not_inf_eq_inf)

lemma B14: "#\<^sub>-y < \<infinity> \<Longrightarrow> #\<^sub>-(\<alpha>\<^sub>-y) < \<infinity>"
  using B10 by (metis inf_less_eq verit_comp_simplify1(3))

lemma B15:
  assumes "#x = \<infinity>" and "#y = \<infinity>"
  assumes "Sender \<in> ALICE"
  shows "#\<^sub>-(Sender\<cdot>(x,y)) < \<infinity> \<longrightarrow> #\<^sub>-x \<le> #\<^sub>-(\<alpha>\<^sub>-y)"
proof - 
  have "(#\<^sub>-(\<alpha>\<^sub>-y) < #\<^sub>-x \<longrightarrow> #\<^sub>-(Sender\<cdot>(x, y)) = \<infinity>)"
   using ALICE_def assms by auto
  then show ?thesis 
    by (metis leI lnless_def)
qed

lemma B16:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-as < \<infinity> \<Longrightarrow> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(Sender\<cdot>(x,as))) < \<infinity>"
  using assms 
  by (metis tsyn_abp_live2 tsynlen_not_inf_eq_inf tsynprojfst_tsynlen)

lemma tsyn_abp_fp_len_h2:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-as < \<infinity> \<Longrightarrow> #\<^sub>-x \<le> #\<^sub>-(\<alpha>\<^sub>-as)"
  using assms B16 
  by (metis (no_types, lifting) B15 tsyn_abp_inf_x_as tsynprojfst_tsynlen)

lemma B18:
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<alpha>\<^sub>- as) = \<infinity> \<Longrightarrow> #\<^sub>-(Sender\<cdot>(x,as)) = \<infinity>"
  using assms B7 B9 
  by metis

lemma B19:
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(Sender\<cdot>(x,as)) < \<infinity> \<Longrightarrow> #\<^sub>-(\<alpha>\<^sub>-(as)) < \<infinity>"
  using assms B18 
  by (metis tsynlen_not_inf_eq_inf)

lemma B20:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "(#\<^sub>-as = \<infinity> \<Longrightarrow> #\<^sub>-(\<alpha>\<^sub>-(as)) = \<infinity>) \<Longrightarrow>
         (#\<^sub>-(Sender\<cdot>(x,as)) = \<infinity> \<Longrightarrow> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) = \<infinity>)"
  using tsyn_abp_live2 B7 assms by metis

lemma B21:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(Sender\<cdot>(x,as)) < \<infinity> \<Longrightarrow> #\<^sub>-x < \<infinity>"
  using assms B19 B15 
  by (metis tsyn_abp_fp_len_leq tsyn_abp_inf_x_as verit_la_disequality)

lemma B22:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-x = \<infinity> \<Longrightarrow> #\<^sub>-(Sender\<cdot>(x,as)) = \<infinity>"
  using assms B21 by (metis inf_less_eq verit_comp_simplify1(3))

lemma B23:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<alpha>\<^sub>-as) = \<infinity> \<Longrightarrow> #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(Sender\<cdot>(x,as)))) = \<infinity>"
  using assms by (metis  tsyn_abp_fp_len_h1 tsynlen_not_inf_eq_inf verit_comp_simplify1(3))

lemma B24:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(Sender\<cdot>(x,as)))) < \<infinity> \<Longrightarrow> #\<^sub>-(\<alpha>\<^sub>-(as)) < \<infinity>"
  by (meson assms dual_order.strict_trans2 tsyn_abp_fp_len_h1)


lemma B26:
  assumes "#x = \<infinity>" and "#y = \<infinity>"
  assumes "Sender \<in> ALICE"
  shows "(#\<^sub>-(Sender\<cdot>(x,y)) < \<infinity> \<and> #\<^sub>-x = \<infinity>) \<Longrightarrow> #\<^sub>-(\<alpha>\<^sub>-y) = \<infinity>" 
  using assms B15 by (metis inf_less_eq)

lemma B27:
  assumes "#x = \<infinity>" and "#y = \<infinity>"
  assumes "Sender \<in> ALICE"
  shows "#\<^sub>-(\<alpha>\<^sub>-y) < \<infinity> \<Longrightarrow> (#\<^sub>-(Sender\<cdot>(x,y)) = \<infinity> \<or> #\<^sub>-x < \<infinity>)"
  using assms B26 
  by (metis tsynlen_not_inf_eq_inf)

lemma B28:
  assumes "#x = \<infinity>" and "#y = \<infinity>"
  assumes "Sender \<in> ALICE"
  shows "#\<^sub>-x > #\<^sub>-(\<alpha>\<^sub>-y) \<Longrightarrow> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x, y)))) = 1 + #\<^sub>-(\<alpha>\<^sub>-y)" 
  using tsyn_abp_S4 assms by (metis linorder_not_less lnat_suc_plus lnle2le min.absorb2 one_lnat_def)

lemma B29:
  assumes "#x = \<infinity>" and "#y = \<infinity>"
  assumes "Sender \<in> ALICE"
  shows "#\<^sub>-x \<le> #\<^sub>-(\<alpha>\<^sub>-y) \<Longrightarrow> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x, y)))) = #\<^sub>-x"
  using tsyn_abp_S4 assms by (metis lnat_add_leq min.orderE)

lemma B32:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) = \<infinity> \<longleftrightarrow> #\<^sub>-(\<alpha>\<^sub>-as) = \<infinity>"
  using assms B5 
  by (metis B28 B29 inf_less_eq lnat_plus_commu lnat_plus_ineq not_le_imp_less one_lnat_def plus_lnatInf_r
      tsyn_abp_inf_x_as)

lemma B34:
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>S)))"
  shows "#\<^sub>-S < \<infinity> \<Longrightarrow> #\<^sub>-as < \<infinity>"
proof -
  assume inf_y: "#\<^sub>-S < \<infinity>"
  have live_proj2: "(#\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>S))) < \<infinity>"
    using tsynprojsnd_tsynlen inf_y assms
    by (metis antisym_conv3 inf_great leD tsynlen_eve)
  have receiver: "(Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>S)))) = (g\<cdot>(\<up>\<sim>\<Zcat>\<Pi>\<^sub>2\<^sub>-(f\<cdot>S)))"
    by (simp add: parComp_def Snd_def Bob_def)
  from inf_y live_proj2 receiver  show "#\<^sub>-S < \<infinity> \<Longrightarrow> #\<^sub>-as < \<infinity>" 
    using assms by (metis linorder_not_less singletonD BOB_def tsynlen_eve 
          tsynlen_not_inf_eq_inf tsynlen_sconc_Eps)
qed

lemma B36:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(Sender\<cdot>(x,as)) = \<infinity> \<longleftrightarrow> #\<^sub>-as = \<infinity>"
  using assms B34 tsyn_abp_live2 
  by (metis min.strict_order_iff tsynlen_not_inf_eq_inf)

lemma B37:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-x > #\<^sub>-(\<alpha>\<^sub>-as) \<Longrightarrow> #\<^sub>-as = \<infinity>"
  using assms  by (metis linorder_not_less tsyn_abp_fp_len_h2 tsynlen_not_inf_eq_inf)

lemma B38:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-x = \<infinity> \<Longrightarrow> #\<^sub>-as = \<infinity>"
  using assms B22 by (metis tsyn_abp_live2)

lemma B39:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-as < \<infinity> \<Longrightarrow> (#\<^sub>-x < \<infinity> \<and> #\<^sub>-(Sender\<cdot>(x,as)) < \<infinity>)"
  using assms B38 by (metis B36 tsynlen_not_inf_eq_inf)

lemma B40:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-x > #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) \<Longrightarrow> #\<^sub>-x > 1 + #\<^sub>-(\<alpha>\<^sub>-as)"
  using assms
  by (metis B28 B29 linorder_le_less_linear order_less_irrefl tsyn_abp_inf_x_as)

lemma B41:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2"
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) = \<infinity> \<Longrightarrow> #\<^sub>-x > #\<^sub>-(\<alpha>\<^sub>-as) \<or> #\<^sub>-x = \<infinity>"
  using assms
  by (metis B29 linorder_le_less_linear tsyn_abp_inf_x_as)


lemma c2: 
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(Sender\<cdot>(x,as)) = \<infinity> \<Longrightarrow> #\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as))) = \<infinity>"
  using assms B20    sorry

lemma tsyn_abp_fp_len_geq:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<alpha>\<^sub>-as) \<ge> #\<^sub>-x" using assms c2 
  by (metis B28 B34 antisym_conv3 inf_great linorder_not_less lnat_suc_plus lnsuc_inf tsyn_abp_fp_len_h2 tsyn_abp_inf_x_as
      tsynprojfst_tsynlen)

lemma tsyn_abp_fp_len:
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<alpha>\<^sub>-as) = #\<^sub>-x"
  using assms tsyn_abp_fp_len_leq tsyn_abp_fp_len_geq 
  by (metis lnat_po_eq_conv)

lemma tsyn_abp_len1: 
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-x = #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) "
  using assms 
  by (simp add: B29 tsyn_abp_fp_len tsyn_abp_inf_x_as)

lemma tsyn_abp_len2: 
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(Sender\<cdot>(x,as))))"
  using assms tsyn_abp_fp_len 
  by (metis B29 lnat_po_eq_conv proj1_tsynremdups_proj2_tsynlen tsyn_abp_fp_len_h1 tsyn_abp_inf_x_as)

lemma tsyn_abp_len3: 
  assumes "#x = \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(Sender\<cdot>(x,as)))) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>(Sender\<cdot>(x,as)))))"
proof - 
  have geq:  "#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(Sender\<cdot>(x,as)))) \<ge> #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>(Sender\<cdot>(x,as)))))"
    using assms  using "05" by auto   
  also have leq: "#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(Sender\<cdot>(x,as)))) \<le> #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>(Sender\<cdot>(x,as)))))"
  using  assms ID_is_medium B29 ID1 lnat_po_eq_conv proj1_tsynremdups_proj2_tsynlen singletonD BOB_def
          tsyn_abp_fp_len tsyn_abp_inf_x_as
  by (metis lemma1)
  finally show ?thesis 
    by metis
qed

lemma lemma4_alt:"#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) < \<infinity> \<Longrightarrow> #\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) \<Longrightarrow> g\<in>EVE1 \<Longrightarrow> #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(g\<cdot>y))) \<Longrightarrow> (\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y))\<^sup>- = (\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(g\<cdot>y)))\<^sup>-"
proof-
  assume a1:"#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) < \<infinity>"
and a2:"#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y))"
and a3:"g\<in>EVE1"
and a4:"#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(g\<cdot>y)))"
  obtain ora where g_def: "g\<cdot>y = tsynBoolFilter\<cdot>y\<cdot>ora" and ora_inf:"#ora=\<infinity>"
    using EVE_def sfilterl4 a3 by force
  thus "tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y)) = tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(g\<cdot>y)))"
    by (metis a1 a2 a4 tsynprojfst_tsynremdups_tsynbolfilter_id_if_fin_tsynlen_eq)
qed

lemma tsyn_abp_med_nomed_eq:
  assumes "#x = \<infinity>"
  assumes "#\<^sub>-x < \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>(Sender\<cdot>(x,as))))) = tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as))))"
  using lemma4_alt assms tsyn_abp_len1 tsyn_abp_len2 tsyn_abp_len3 
  by metis

lemma tsyn_abp_eq_slen_eq_and_less: 
  assumes "#x = \<infinity>"
  assumes "#\<^sub>-x < \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows "tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) = tsyn2ustream\<cdot>x"
proof -
  have "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x,as)))) = #\<^sub>-x"
    using assms tsyn_abp_len1  by metis
  also have "sprojfst\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>(Sender\<cdot>(x, as)))) \<sqsubseteq> tsyn2ustream\<cdot>x"
    using ALICE_def assms tsyn_abp_inf_x_as by blast
  then have "tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(Sender\<cdot>(x, as)))) \<sqsubseteq> tsyn2ustream\<cdot>x"
    by (simp add: tsynprojfst_tsynabs tsynremdups_tsynabs)
  ultimately show ?thesis 
    using eq_tsynlen_eq_and_less by auto 
qed

lemma tsyn_abp_output_rewrite: 
  fixes x
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  assumes "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))))"
  shows " Fst\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as)))) = \<up>\<sim> \<Zcat> \<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>(Sender\<cdot>(x,as))))"
proof -
  have "Receiver = Bob"
    by (metis assms(3) singletonD BOB_def)
  then show ?thesis 
    by (simp add: Bob_def Fst_def) 
qed


lemma tsyn_abp_output_Eps: "tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>(Sender\<cdot>(x,as))))) = tsyn2ustream\<cdot>(\<up>\<sim> \<Zcat>  \<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>(Sender\<cdot>(x,as)))))"
  by simp

lemma tsyn_abp_fin_correct: 
  assumes "#x = \<infinity>"
  assumes "#\<^sub>-x < \<infinity>"
  assumes "f \<in> EVE1"
  assumes "g \<in> EVE2" 
  assumes "Receiver \<in> BOB"
  assumes "Sender \<in> ALICE"
  defines "as \<equiv> (\<mu> (Sender \<circle> f \<circle> Receiver \<circle> (ID \<parallel> g)) \<circle> Snd)\<cdot>x"
  shows "tsyn2ustream\<cdot>(Fst\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x,as))))) = tsyn2ustream\<cdot>x"
proof - 
  have "as = Snd\<cdot>((ID \<parallel> g)\<cdot>(Receiver\<cdot>(f\<cdot>(Sender \<cdot>(x, as)))))" 
    using assms tsyn_abp_fp by blast
  then show ?thesis using tsyn_abp_output_rewrite assms tsyn_abp_output_Eps
        tsyn_abp_med_nomed_eq tsyn_abp_eq_slen_eq_and_less by metis
qed

lemma tsyn_abp_fin_i_eq_o:
  assumes "#x = \<infinity>"
  assumes "#\<^sub>-x < \<infinity>"
    and "abp \<in> ABP"
  shows "tsyn2ustream\<cdot>(abp\<cdot>x) = tsyn2ustream\<cdot>x"
proof -
  obtain Receiver Sender f g where
    abp_def: "abp = (\<mu>(Sender \<circle> f \<circle> Receiver \<circle> (ID \<parallel> g)) \<circle> Fst)"
    and R: "Receiver \<in> BOB" 
    and S: "Sender \<in> ALICE"
    and f: "f \<in> EVE1"
    and g: "g \<in> EVE2"
    using assms(3) unfolding ABP_def by blast

  have "abp\<cdot>x =  Fst\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x, (\<mu>(Sender \<circle> f \<circle> Receiver \<circle> (ID \<parallel> g)) \<circle> Snd)\<cdot>x))))"
    unfolding abp_def using fp_Fst_Snd_unfold f g S parComp_ID_Fst2
    by (metis (no_types, lifting) cfcomp2) 

  also have fst_receiver_eq:
    "tsyn2ustream\<cdot>(Fst\<cdot>(Receiver\<cdot>(f\<cdot>(Sender\<cdot>(x, (\<mu>(Sender \<circle> f \<circle> Receiver \<circle> (ID \<parallel> g)) \<circle> Snd)\<cdot>x))))) = tsyn2ustream\<cdot>x"
    by (rule tsyn_abp_fin_correct[OF assms(1,2) f g R S])

  ultimately show "tsyn2ustream\<cdot>(abp\<cdot>x) = tsyn2ustream\<cdot>x"
    by fastforce
qed

lemma tsyn_abp_adm:
  shows "adm (\<lambda> x. tsyn2ustream\<cdot>(abp\<cdot>x) = tsyn2ustream\<cdot>x)"
  by (rule adm_eq; simp)

lemma tsyn_stream_infs: "(\<And>s::'a tsyn stream. #\<^sub>-s<\<infinity> \<Longrightarrow> P s) \<Longrightarrow> adm P \<Longrightarrow> P s"
  using stream_infs 
  by (metis tsynEps_tsynEps2slen_infinite_msg tsynlen_not_inf_eq_inf)

lemma tsyn_stream_infs2: "#s = \<infinity> \<Longrightarrow>(\<And>s::'a tsyn stream. #s = \<infinity> \<and> #\<^sub>-s<\<infinity> \<Longrightarrow> P s) \<Longrightarrow> adm P \<Longrightarrow> P s"
  sorry

lemma tsyn_abp_i_eq_o:
  assumes "#x = \<infinity>"
  assumes "abp \<in> ABP"
  shows "tsyn2ustream\<cdot>(abp\<cdot>x) = tsyn2ustream\<cdot>x"
  using assms tsyn_abp_fin_i_eq_o tsyn_stream_infs2 tsyn_abp_adm 
  by (metis (mono_tags, lifting))

lemma tsyn_abp_i_eq_o2: "#x = \<infinity> \<Longrightarrow> (\<forall>abp \<in> ABP. tsyn2ustream\<cdot>(abp\<cdot>x) = tsyn2ustream\<cdot>x)"
  using tsyn_abp_i_eq_o by auto

end
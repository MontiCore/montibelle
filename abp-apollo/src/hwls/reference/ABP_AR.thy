theory ABP_AR
  imports
    stream.TsynStream
    move_to_core.TsynStreamExtension  

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
"Bob \<equiv> \<Lambda> s. (\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-s), \<Pi>\<^sub>2\<^sub>-s)"

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


lemma Bob_LLR_h_output:      
    "sprojfst\<cdot>(sprojfst\<cdot>(sscanl (\<lambda>(u, y). Bob_LLR_h y) (u, state)\<cdot>s)) 
     = \<Pi>\<^sub>1\<^sub>-(sprojfst\<cdot>(sscanl (\<lambda>(u, y). tsynRemDups_h y) (v, tsyn_and_bool_to_tsyn_pair state)\<cdot>s)) "
proof (induction s arbitrary: u state v rule: tsyn_ind)
  case adm
  then show ?case
    apply (rule adm_all)+
    apply (rule adm_eq)
    by auto
next
  case bot
  then show ?case
    by simp
next
  case (msg m s)
  then show ?case 
    apply (cases m)
    apply (simp_all add: tsynprojfst_sconc_Eps tsynprojfst_sconc_msg)
    apply (cases state)
    apply (rename_tac x y z w)
    apply (case_tac z)  
    apply simp
     apply (metis tsyn_and_bool_to_tsyn_pair.simps(2)) 
    apply (case_tac "tsyn_and_bool_to_tsyn_pair state = TSynMsg (x, y)")
     apply simp_all
     apply (metis tsyn_and_bool_to_tsyn_pair.simps(2))
    defer
    apply (case_tac "a=x")
    apply (case_tac "w=y")
    apply (simp_all) 
    by (metis tsyn_and_bool_to_tsyn_pair.simps(2))+
  case (Eps s)
  then show ?case 
    apply (simp_all add: tsynprojfst_sconc_Eps tsynprojfst_sconc_msg)
    by metis
qed

lemma Bob_LLR_refs_HLR_out: "fst (Bob_LLR\<cdot>s) = \<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-s)"
  apply (simp add: semanticMapping_def Bob_LLR_def tsynRemDups_def)
  using Bob_LLR_h_output
  by (metis tsyn_and_bool_to_tsyn_pair.simps(1))

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

definition ALICE :: "(('d tsyn stream \<times> bool tsyn stream) \<rightarrow> ('d \<times> bool) tsyn stream) set" 
  where 
  "ALICE \<equiv> {spf | spf. \<forall>i.
   AlicePredicate i (spf\<cdot>i)}"

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
"ABPunfair \<equiv> {\<mu>(Alice_LLR o Eve1 o Bob o (ID \<parallel> Eve2)) o Fst | Alice_LLR Bob Eve1 Eve2. 
 Alice_LLR \<in> ALICE_LLR \<and> Bob \<in> BOB \<and> Eve1 \<in> EVE1unfair \<and> Eve2 \<in> EVE2unfair}"


definition ABP :: "('d tsyn stream \<rightarrow> 'd tsyn stream) set" where
"ABP \<equiv> {\<mu>(Alice_LLR o Eve1 o Bob o (ID \<parallel> Eve2)) o Fst | Alice_LLR Bob Eve1 Eve2. 
 Alice_LLR \<in> ALICE_LLR \<and> Bob \<in> BOB \<and> Eve1 \<in> EVE1 \<and> Eve2 \<in> EVE2}"


lemma alice_empty: "Alice_LLR\<cdot>(\<epsilon>, x)=\<up>\<sim>"
  by (simp add: Alice_LLR_def semanticMapping_def)

lemma bob_empty: "Bob\<cdot>\<epsilon> = (\<epsilon>,\<epsilon>)"
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
        tsynzip_Eps_sconc tsynzip_Eps_singeltons tsynzip_msg_sconc tsynzip_msg_sconc2 
       tsynzip_msg_singeltons tsynzip_tsynabs tsynzip_tsynabs2
       tsynzip_tsynabs_image

lemma abp_refine : "ABP \<subseteq> ABPunfair"
  apply (simp add: ABP_def ABPunfair_def ALICE_LLR_def BOB_def)
  using eve1_refines_eve1unfair eve2_refines_eve2unfair  apply auto
  done

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
  by (simp add: Fst_apply tsynprojfst_tsynlen)

lemma lemma1: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>y)))))"   
proof -
  have a1: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))"
   by (simp add: 05) 
  hence a2: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y))) \<ge> #\<^sub>-(\<alpha>\<^sub>-(g\<cdot>(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y))))"
  using lemma0 by blast
  hence a3: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(\<alpha>\<^sub>-(g\<cdot>(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))) = #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>y)), g\<cdot>(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))))"
    by (simp add: Snd_apply)
  hence a4: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>y)), g\<cdot>(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))))
                   = #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>((\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>y)), \<Pi>\<^sub>2\<^sub>-(f\<cdot>y))))))"
    by (simp add: parComp_def)
  hence a5: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>((\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(f\<cdot>y)), \<Pi>\<^sub>2\<^sub>-(f\<cdot>y))))))
                   = #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>y)))))"
    by (simp add: Bob_def)
  then show ?thesis using a1 a2 a3 a4 a5
    by fastforce
  qed

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
  by (simp add: Bob_def EveNice_def parComp_def Snd_apply tsynboolfilter_inf_true )

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
  have bob2: "\<forall>f \<in> EVE1. \<forall>g \<in> EVE2. (Snd\<cdot>((ID \<parallel> g)\<cdot>(Bob\<cdot>(f\<cdot>y)))) = (g\<cdot>(\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))"
    by (simp add: parComp_def Snd_def Bob_def)
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

lemma tsyn_abp_remdups_len: "\<forall>f \<in> MEDIUM. \<forall>g \<in> MEDIUM. #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(tsyn_Receiver\<cdot>(f\<cdot>y)))))"
proof -
  have "\<forall>f \<in> MEDIUM1. \<forall>g \<in> MEDIUM2. #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(g\<cdot>(\<up>\<sim>\<Zcat>\<Pi>\<^sub>2\<^sub>-(f\<cdot>y))))"
    using tsyn_med_remdups_projsnd_len tsyn_med_remdups_len tsynlen_sconc_Eps tsynremdups_Eps
    by (metis (no_types, lifting) order.trans)
  also have "\<forall>f \<in> MEDIUM1. \<forall>g \<in> MEDIUM2. #\<^sub>-(\<alpha>\<^sub>-(g\<cdot>(\<up>\<sim>\<Zcat>\<Pi>\<^sub>2\<^sub>-(f\<cdot>y)))) = #\<^sub>-(\<alpha>\<^sub>-(Snd\<cdot>((ID \<parallel> g)\<cdot>(tsyn_Receiver\<cdot>(f\<cdot>y)))))"
    by (simp add: Snd_apply parComp_apply tsyn_Receiver_def)
  ultimately show ?thesis 
    by fastforce
qed

end

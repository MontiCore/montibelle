theory LtlStream

imports stream.StreamLtl eventcomponent.EventAutomatonExec

begin
default_sort countable

text\<open>In this theory we would like to show how one can define specifications using LTL.
     Therefore, we first define an example specification, where we require that a stream-processing
     function f maps all streams which model @{term exampleInputSpec} to streams which model 
     @{term checkAlternating2}.
     Here, @{term exampleInputSpec} describes the property, that a nat stream only consists of
     ones and zeros and @{term checkAlternating2} describes the property that a bool stream is
     a sequence of alternating booleans, e.g., <True,False,True,False>.\<close>


definition exampleInputSpec :: "nat ltl" where
"exampleInputSpec = GloballyLtl (AllPropLtl (\<lambda>x . x=0 \<or> x=1))"

definition exampleSpec :: "(nat stream \<rightarrow> bool stream) set" where
"exampleSpec = {f . \<forall>input. ((ltl_semantics input exampleInputSpec) \<longrightarrow> (ltl_semantics (f\<cdot>input) checkAlternating2))}"


fun exampletransition::"bool \<Rightarrow> nat \<Rightarrow> (bool \<times> bool)"where
"exampletransition stat 0 = (\<not> stat,stat)" |
"exampletransition stat (Suc 0) = (\<not> stat,stat)" |
"exampletransition _ _ = (True, False)"

definition exampleconfig::"bool \<times> bool stream "where
"exampleconfig = (True, \<epsilon>)"

definition exampleautomaton::"(bool,nat,bool stream) dAutomaton"where
"exampleautomaton = (|dautTransition=(\<lambda>s m. apsnd sup' (exampletransition s m))  , 
                    dautInitConfig= (True, \<epsilon>) |)"



definition exampleautomaton_semantics::"nat stream \<rightarrow> bool stream" where
"exampleautomaton_semantics = (daSem stream_step exampleautomaton)"

(*
lemma "exampleautomaton_semantics \<in> exampleSpec"
  apply (simp add: exampleautomaton_semantics_def, simp add: exampleSpec_def)
  apply (simp add: exampleInputSpec_def)
*)  
  

lemma exsemstatesem_len[simp]:
"#(daStateSem stream_step exampleautomaton state\<cdot> input) = #input"
proof(induction input arbitrary: state)
case adm
  then show ?case 
    by (rule adm_all,rule adm_eq,simp_all add:len_stream_def)
next
  case bottom
  then show ?case 
    by (subst dastatesem_step,simp)
next
  case (step a input)
  then show ?case 
    apply (subst dastatesem_step)
    by(simp add: case_prod_beta' Let_def  exampleautomaton_def)
qed

lemma exsem_len[simp]:"#(exampleautomaton_semantics\<cdot>input) = #input"
  apply(simp add: exampleautomaton_semantics_def daSem_def case_prod_beta' )
  by(subst exampleautomaton_def,simp)

lemma EASH_EMPTY: "exampleautomaton_semantics\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: exampleautomaton_semantics_def, simp add: exampleautomaton_def)

lemma EASH_LENGTH_AUX_AUX: "\<forall>s state. #(daStateSem stream_step exampleautomaton state\<cdot>(stake n\<cdot>s)) = #(stake n\<cdot>s)"
  apply (induction n)
  by auto
  (* apply (simp add: exampleautomaton_def)
   apply (subst dastatesem_step, auto)
  apply (subgoal_tac "s = \<epsilon> \<or> (\<exists>a as. (sup' a)\<Zcat>(stake n\<cdot>as) = (stake (Suc n)\<cdot>s) )")
   apply auto
    apply (simp add: exampleautomaton_def)
    apply (subst dastatesem_step, auto)
   defer
  apply (metis stake_Suc surj_scons)

  apply (subgoal_tac "\<exists>st. #(daStateSem stream_step exampleautomaton state\<cdot>((sup' a)\<Zcat>(stake n\<cdot>as))) = lnsuc\<cdot>(#(daStateSem stream_step exampleautomaton st\<cdot>((stake n\<cdot>as))))")
   apply (metis slen_scons)
  apply auto
  apply (subst dastatesem_step, simp add: stream_step_insert)
  apply (subgoal_tac "\<exists>a. lshd\<cdot>(stake (Suc n)\<cdot>s) = up\<cdot>a", auto)
   apply (subgoal_tac "\<exists>ns out. case dautTransition exampleautomaton state (undiscr aa) of
         (nextState, output) \<Rightarrow> output \<Zcat> daStateSem stream_step exampleautomaton nextState\<cdot>(srt\<cdot>(stake (Suc n)\<cdot>s)) = (sup' out) \<Zcat> daStateSem stream_step exampleautomaton ns\<cdot>(stake n\<cdot>as)")
    apply auto
   apply (simp add: exampleautomaton_def)
   apply (subgoal_tac "\<exists>ns out. apsnd sup' (exampletransition state (undiscr aa)) = (ns,(sup' out))")
  apply auto
    apply (rule_tac x="ns" in exI)
    apply (rule_tac x="out" in exI)
    apply (subgoal_tac "srt\<cdot>(stake (Suc n)\<cdot>s) = stake n\<cdot>as")
     apply auto
    apply (metis lscons_conv stream.sel_rews(5) up_defined)
  apply (metis apsnd_conv surj_pair)
  by (metis lshd_updis)*)

lemma EASH_LENGTH_AUX: "\<forall>s. #(daSem stream_step exampleautomaton\<cdot>(stake n\<cdot>s)) = #(stake n\<cdot>s)"
  apply (subgoal_tac "\<forall>s. daSem stream_step exampleautomaton\<cdot>(stake n\<cdot>s) = daStateSem stream_step exampleautomaton True\<cdot>(stake n\<cdot>s)")
  using EASH_LENGTH_AUX_AUX[of n]
   apply auto
  apply (simp add: dasem_unfold)
  by (simp add: exampleautomaton_def)

lemma EASH_LENGTH: "Fin n < #(daSem stream_step exampleautomaton\<cdot>input) \<Longrightarrow> Fin n < #input"
  apply (subgoal_tac "Fin n = #(daSem stream_step exampleautomaton\<cdot>(stake n\<cdot>input))")
   apply (subgoal_tac "#(stake n\<cdot>input) < #input")
  using EASH_LENGTH_AUX[of n]
    apply auto
   apply (metis fin2stake lnless_def mono_len2 stream.take_below)
  by (metis dual_order.strict_implies_order fin2stake_lemma lnat_well_h1 not_le_imp_less slen_stake)

lemma EASH1: "ltl_semantics input ((G\<^sub>l) (allprop\<^sub>l (\<lambda>x. x = 0 \<or> x = Suc 0))) \<Longrightarrow> sValues\<cdot>input \<subseteq> {0,1}"
  using GloballyLtl_def2 [of input "(allprop\<^sub>l (\<lambda>x. x = 0 \<or> x = Suc 0))"]
  apply simp
  apply (simp add: sValues_def2, simp add: snth_def)
  using allprop_setup
  by fastforce 

lemma checkAlternating2_def2_aux: "\<forall>\<sigma>. (Fin k) = #\<sigma> \<longrightarrow>  sdrop k\<cdot>\<sigma> = \<epsilon>"
    apply (induction k)
     apply auto
    apply (subgoal_tac "\<exists>a as. \<sigma> = (sup' a)\<Zcat>as")
     apply auto
     apply (metis Fin_Suc inject_lnsuc)
  by (metis Fin_Suc lnsuc_neq_0_rev slen_zero streamcases)  

lemma checkAlternating2_def2:
"ltl_semantics s checkAlternating2 = (\<forall>i. (Fin (Suc i) < #s \<longrightarrow> ((shd (sdrop i\<cdot>s)) = (\<not> (shd (sdrop (Suc i)\<cdot>s))))))"
proof -
  have a: "\<forall>k p. sdrop (Suc 0)\<cdot>(sdrop k\<cdot>p) = sdrop (Suc k)\<cdot>p"
    by (simp add: sdrop_back_rt)

  have c:"\<forall>a b. ((a = (\<not> b)) = (a \<longleftrightarrow> \<not> b))"
    by simp
  
  show "ltl_semantics s checkAlternating2 = (\<forall>i. (Fin (Suc i) < #s \<longrightarrow> ((shd (sdrop i\<cdot>s)) = (\<not> (shd (sdrop (Suc i)\<cdot>s))))))"
    apply (simp add: checkAlternating2_def)
    using GloballyLtl_def2 [of s "(HasNextLtl (PropLtl (\<lambda>x. x) eq\<^sub>l (X\<^sub>l) (PropLtl Not)))"]
    apply simp
    apply (simp add: ImpliesLtl_def, simp add: EqualityLtl_def, simp add: AndLtl_def)
    apply (simp add: a)
    apply (simp add: allprop_setup)
    apply (subst c)
    using checkAlternating2_def2_aux
    using allprop_setup
    apply auto
    using convert_inductive_asm apply blast+
    by (meson less2lnleD order.not_eq_order_implies_strict)+
qed

lemma EASH2_1: "{shd (sdrop n\<cdot>input) |n. Fin n < #input} \<subseteq> {0, Suc 0} \<Longrightarrow> Fin n < #input \<Longrightarrow>
  (dautTransition exampleautomaton) state (shd (sdrop n\<cdot>input)) = ((\<not> state), sup' state)"
  by (simp add: exampleautomaton_def, auto)

lemma EASH2_2: "{shd (sdrop n\<cdot>input) |n. Fin n < #input} \<subseteq> {0, Suc 0} \<Longrightarrow> Fin n < #input \<Longrightarrow>
   daStateSem stream_step exampleautomaton state\<cdot>(sdrop n\<cdot>input) = (sup' state) \<Zcat> daStateSem stream_step exampleautomaton (\<not> state)\<cdot>(srt\<cdot>(sdrop n\<cdot>input))"
  apply (subst dastatesem_step, simp)
  apply (simp add: stream_step_insert)
  apply (subgoal_tac "\<exists>a as. (sdrop n\<cdot>input) = ((sup' a)\<Zcat>as)", subgoal_tac "\<exists>a. lshd\<cdot>(sdrop n\<cdot>input) = up\<cdot>a")
    apply (subgoal_tac "\<exists>a. shd (sdrop n\<cdot>input) = a")
     apply (subgoal_tac "\<forall>a as st. dautTransition exampleautomaton st (shd ((sup' a)\<Zcat>as)) = dautTransition exampleautomaton st a")
      defer
  apply (simp add: shd_c)
  apply (metis undiscr_Discr)
    apply auto[1]
   apply (meson allprop_setup streamcases) 
  apply (subgoal_tac "\<forall>a as. (sdrop n\<cdot>input) = ((sup' a)\<Zcat>as) \<longrightarrow> ((case dautTransition exampleautomaton state a of
            (nextState, output) \<Rightarrow> output \<Zcat> daStateSem stream_step exampleautomaton nextState\<cdot>as) = (sup' state) \<Zcat> daStateSem stream_step exampleautomaton (\<not> state)\<cdot>as)")
  using EASH2_1 [of input n state]
   apply auto
  using inject_scons by fastforce

lemma EASH2_3_1: "{shd (sdrop n\<cdot>input) |n. Fin n < #input} \<subseteq> {0, Suc 0} \<Longrightarrow> Fin i < #input \<Longrightarrow>
  \<exists>state. Fin (Suc i) < #(daSem stream_step exampleautomaton\<cdot>input) \<longrightarrow> 
    sdrop i\<cdot>(daSem stream_step exampleautomaton\<cdot>input) = (sup' state) \<Zcat> (daStateSem stream_step exampleautomaton (\<not> state)\<cdot>(sdrop (Suc i)\<cdot>input))"
  apply (induction i)
  apply (rule_tac x="True" in exI)
  apply (simp add: dasem_unfold)
   apply (subgoal_tac "fst (dautInitConfig exampleautomaton) = True", subgoal_tac "snd (dautInitConfig exampleautomaton) = \<epsilon>")
  apply (simp add: sdrop_back_rt)
  using EASH2_2 [of input 0 True] apply simp  
     apply (simp add: sdrop_forw_rt)
    apply (simp add: exampleautomaton_def)
   apply (simp add: exampleautomaton_def)
  apply (simp add: sdrop_back_rt)
proof -
  fix ia :: nat
assume a1: "Fin (Suc ia) < #input"
  assume a2: "{shd (sdrop n\<cdot>input) |n. Fin n < #input} \<subseteq> {0, Suc 0}"
  assume a3: "Fin ia < #input \<Longrightarrow> Fin (Suc ia) < #(daSem stream_step exampleautomaton\<cdot>input) \<longrightarrow> (\<exists>state. sdrop ia\<cdot>(daSem stream_step exampleautomaton\<cdot>input) = \<up>state \<Zcat> daStateSem stream_step exampleautomaton (\<not> state)\<cdot> (srt\<cdot>(sdrop ia\<cdot>input)))"
  have f4: "\<And>n s b. \<not> Fin n < #s \<or> \<not> {shd (sdrop n\<cdot>s) |n. Fin n < #s} \<subseteq> {0, Suc 0} \<or> \<up>b \<Zcat> daStateSem stream_step exampleautomaton (\<not> b)\<cdot> (sdrop (Suc n)\<cdot>s) = daStateSem stream_step exampleautomaton b\<cdot>(sdrop n\<cdot>s)"
  by (simp add: EASH2_2 sdrop_back_rt)
  have f5: "Fin ia < #input"
    using a1 by (metis convert_inductive_asm)
  then obtain bb :: bool where
    f6: "\<not> Fin (Suc ia) < #(daSem stream_step exampleautomaton\<cdot>input) \<or> \<up>bb \<Zcat> daStateSem stream_step exampleautomaton (\<not> bb)\<cdot> (sdrop (Suc ia)\<cdot>input) = sdrop ia\<cdot>(daSem stream_step exampleautomaton\<cdot>input)"
    using a3 by (metis (no_types) sdrop_back_rt)
  { assume "\<exists>b. daStateSem stream_step exampleautomaton b\<cdot> (sdrop (Suc ia)\<cdot>input) = sdrop (Suc ia)\<cdot>(daSem stream_step exampleautomaton\<cdot>input)"
    then have "\<exists>b. \<up>b \<Zcat> daStateSem stream_step exampleautomaton (\<not> b)\<cdot> (sdrop (Suc (Suc ia))\<cdot>input) = sdrop (Suc ia)\<cdot>(daSem stream_step exampleautomaton\<cdot>input)"
      using f4 a2 a1 by presburger
    then have "Fin (Suc (Suc ia)) < #(daSem stream_step exampleautomaton\<cdot>input) \<longrightarrow> (\<exists>b. srt\<cdot> (sdrop ia\<cdot>(daSem stream_step exampleautomaton\<cdot>input)) = \<up>b \<Zcat> daStateSem stream_step exampleautomaton (\<not> b)\<cdot> (srt\<cdot>(srt\<cdot>(sdrop ia\<cdot>input))))"
      by (metis (no_types) sdrop_back_rt) }
  moreover
  { assume "sdrop (Suc ia)\<cdot> (daSem stream_step exampleautomaton\<cdot>input) \<noteq> daStateSem stream_step exampleautomaton (\<not> bb)\<cdot> (sdrop (Suc ia)\<cdot>input)"
    then have "sdrop ia\<cdot>(daSem stream_step exampleautomaton\<cdot>input) \<noteq> daStateSem stream_step exampleautomaton bb\<cdot> (sdrop ia\<cdot>input) \<or> \<up>bb \<Zcat> daStateSem stream_step exampleautomaton (\<not> bb)\<cdot> (sdrop (Suc ia)\<cdot>input) \<noteq> sdrop ia\<cdot>(daSem stream_step exampleautomaton\<cdot>input)"
      by (metis (no_types) sdrop_0 sdrop_back_rt sdrop_scons)
    then have "\<not> Fin (Suc ia) < #(daSem stream_step exampleautomaton\<cdot>input)"
      using f6 f5 f4 a2 by force
then have "Fin (Suc (Suc ia)) < #(daSem stream_step exampleautomaton\<cdot>input) \<longrightarrow> (\<exists>b. srt\<cdot> (sdrop ia\<cdot>(daSem stream_step exampleautomaton\<cdot>input)) = \<up>b \<Zcat> daStateSem stream_step exampleautomaton (\<not> b)\<cdot> (srt\<cdot>(srt\<cdot>(sdrop ia\<cdot>input))))"
by (metis convert_inductive_asm) }
ultimately show "Fin (Suc (Suc ia)) < #(daSem stream_step exampleautomaton\<cdot>input) \<longrightarrow> (\<exists>b. srt\<cdot> (sdrop ia\<cdot>(daSem stream_step exampleautomaton\<cdot>input)) = \<up>b \<Zcat> daStateSem stream_step exampleautomaton (\<not> b)\<cdot> (srt\<cdot>(srt\<cdot>(sdrop ia\<cdot>input))))"
by fastforce
qed

lemma EASH2_3: "{shd (sdrop n\<cdot>input) |n. Fin n < #input} \<subseteq> {0, Suc 0} \<Longrightarrow>
    Fin (Suc i) < #(daSem stream_step exampleautomaton\<cdot>input) \<longrightarrow>
        shd (sdrop i\<cdot>(daSem stream_step exampleautomaton\<cdot>input)) = (\<not> shd (sdrop (Suc i)\<cdot>(daSem stream_step exampleautomaton\<cdot>input)))"
  using EASH2_3_1[of input i] apply auto
  using EASH_LENGTH[of "Suc i" input]  apply auto
   apply (simp add: sdrop_back_rt) 
  using EASH2_2 [of input "Suc i" False] apply auto
  apply (simp add: sdrop_back_rt)
  using EASH2_2 [of input "Suc i" False] apply auto
  using convert_inductive_asm apply fastforce
  using convert_inductive_asm [of i "input"] apply simp
  apply auto
  using EASH2_2 [of input "Suc i"] apply auto
  by (simp add: sdrop_back_rt)

lemma EASH2: "sValues\<cdot>input \<subseteq> {0,1} 
\<Longrightarrow> ltl_semantics (daSem stream_step exampleautomaton\<cdot>input)
                  checkAlternating2"
  apply (simp add: checkAlternating2_def2)
  apply (simp add: sValues_def2, simp add: snth_def)
  using EASH2_3 by auto 

theorem "exampleautomaton_semantics \<in> exampleSpec"
  apply (simp add: exampleautomaton_semantics_def, simp add: exampleSpec_def)
  apply (simp add: exampleInputSpec_def)
  using EASH1
  using EASH2  
  by auto 

end
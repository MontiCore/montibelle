theory AutomatonCausality
imports Automaton inc.Causality

begin
context
begin
  private       lemma cont_compose_r:"cont g \<Longrightarrow> cont (\<lambda>x. g (f\<cdot>x))"
    by (simp add: cont_compose)

lemma stateSem_nextspf_def: assumes "spf\<in>stateSem step aut s"
  obtains out f nextState nextSPF where 
    "(nextState,out) \<in> (autTransition\<cdot>aut) s msg"
    and "nextSPF \<in> (stateSem step aut) nextState"
    and "(\<And> input. f msg\<cdot>input = out \<Zcat>\<Zcat> nextSPF\<cdot>input)"
    and "spf = step\<cdot>f"
proof-
  obtain f where f_def: "\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>aut) s msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem step aut) nextState 
        \<and>  (\<forall>sb. f msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
      and spf_def: "spf = step\<cdot>f"
    using stateSemf_def[of spf step aut s] assms by blast
  thus ?thesis
    using that by blast
qed

lemma ndasem_pred:assumes"spf \<in> sem step nda"
  shows"\<exists>initState initOut. (initState,initOut)\<in>autInitConfig\<cdot>nda \<and>
        (\<exists>spf2\<in>(stateSem step nda) initState.
          spf\<cdot>sb = initOut \<Zcat>\<Zcat> spf2\<cdot>sb)"
  using assms
  apply(simp add: sem_def)
  by auto+


theorem statesem_weak_ind:
  fixes aut :: "('state::type, 'msg, 'output::{tlen_cont, tlenconc}) automaton"
    and step :: "('msg \<Rightarrow> 'input::{tlen_cont,conc} \<rightarrow> 'output) \<rightarrow> 'input \<rightarrow> 'output" 
    and conv ::"'msg \<Rightarrow> 'input"
    assumes my_ind:  "\<And>P x. adm P \<Longrightarrow> (\<And>input. #\<^sub>\<surd> input = 0 \<Longrightarrow> P input)
            \<Longrightarrow> (\<And>msg input. P input \<Longrightarrow> P ((conv msg) \<Zcat>\<Zcat> input)) 
            \<Longrightarrow> P x"
        and step_unfold: "\<And>f msg input. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat> input) = f msg\<cdot>input"
        and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> #\<^sub>\<surd>(conv msg) \<le> #\<^sub>\<surd>out \<and> wellformed out"  
        and conv_len: "\<And>msg input. #\<^sub>\<surd>(conv msg\<Zcat>\<Zcat>input) \<le> #\<^sub>\<surd>(conv msg) + #\<^sub>\<surd>input"
        and spf_in: "spf \<in> stateSem step aut s"
      shows "#\<^sub>\<surd>input \<le> #\<^sub>\<surd>(spf\<cdot>input)"
  apply(rule mp [where P="spf \<in> stateSem step aut s"])
proof(induction input arbitrary: s spf rule: my_ind; (rule impI)?)
  case 1
  then show ?case    
    apply((rule adm_all)+, rule adm_imp; simp)
    apply(subst lnle_conv[symmetric], rule adm_below)
    using cont2cont
    by(simp add: cont_compose_r)+
next
  case (2 input)
  then show "#\<^sub>\<surd> input \<le> #\<^sub>\<surd> (spf\<cdot>input)" by simp
next
  case (3 msg input)
  assume "spf\<in>stateSem step aut s" 
  hence spf_in_step: "spf\<in>stateSem_step step aut (stateSem step aut) s"
    by (simp add: stateSem_stepI)
  from this obtain f where f_def: "\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>aut) s msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem step aut) nextState 
        \<and>  (\<forall>sb. f msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
      and spf_def: "spf = step\<cdot>f"
       by(auto simp add: stateSem_step_def ) 
  from this obtain out nextState nextSPF where 
    nextstate_out_def: "(nextState,out) \<in> (autTransition\<cdot>aut) s msg"
    and nextSPF_in: "nextSPF \<in> (stateSem step aut) nextState"
    and f_def2: "(\<And> input. f msg\<cdot>input = out \<Zcat>\<Zcat> nextSPF\<cdot>input)"
    by blast
  have "#\<^sub>\<surd>(conv msg\<Zcat>\<Zcat>input) \<le> #\<^sub>\<surd>(conv msg) + #\<^sub>\<surd>input"
    using conv_len by blast
  moreover have " #\<^sub>\<surd>out + #\<^sub>\<surd>(nextSPF\<cdot>input) \<le> #\<^sub>\<surd>(spf\<cdot>(conv msg\<Zcat>\<Zcat>input))"
    using nextstate_out_def assms(3) f_def2 spf_def step_unfold tlen_conc by fastforce
  moreover have "#\<^sub>\<surd>(conv msg) \<le> #\<^sub>\<surd>out"
    using \<open>(nextState::'state, out::'output) \<in> (autTransition\<cdot>(aut::('state, 'msg, 'output) automaton)) (s::'state) (msg::'msg)\<close> assms(3) by auto 
  moreover have "#\<^sub>\<surd>input \<le> #\<^sub>\<surd>(nextSPF\<cdot>input)"
    using "3.IH" nextSPF_in by auto
  ultimately show "#\<^sub>\<surd> (conv msg\<Zcat>\<Zcat>input) \<le> #\<^sub>\<surd>(spf\<cdot>(conv msg\<Zcat>\<Zcat>input))"
    by (meson dual_order.trans lessequal_addition)
next
  show "spf \<in> stateSem step aut s"
    by (simp add: spf_in) 
qed

theorem sem_weak:
  assumes "(spf::(('in::{wellformed}) \<rightarrow> ('out::{pcpo, tlenconc}))) \<in> (sem step aut)"
    and "\<And>state spf. state \<in> fst ` autInitConfig\<cdot>aut \<Longrightarrow> spf \<in> (stateSem step aut state) \<Longrightarrow> weak spf"
    and "\<And>initState initOut. (initState, initOut) \<in> autInitConfig\<cdot>aut \<Longrightarrow> wellformed initOut "
  shows "weak spf"
proof (rule weakI)
  fix s :: 'in
  obtain initState initOut spf2 where init_state_out_def: "(initState,initOut)\<in>autInitConfig\<cdot>aut"
    and spf2_statesem: "spf2\<in>(stateSem step aut) initState"
    and spf_apply: "spf\<cdot>s = initOut \<Zcat>\<Zcat> spf2\<cdot>s"
    using assms ndasem_pred apply auto[1]
    by (meson ndasem_pred)
  hence "#\<^sub>\<surd> s \<le> #\<^sub>\<surd> (spf2\<cdot>s)"
    using assms apply(simp add: weak_def) by fastforce
  thus " #\<^sub>\<surd> s \<le> #\<^sub>\<surd> (spf\<cdot>s)"
    apply(simp add: spf_apply)
    using tlen_conc[of initOut "spf2\<cdot>s"] assms(3) init_state_out_def
    using lnat_add_leq trans_lnle by blast
qed


theorem sem_strong_ind:
  assumes "(spf::(('in::{wellformed}) \<rightarrow> ('out::{pcpo, tlenconc}))) \<in> (sem step aut)"
    and "\<And>state spf. state \<in> fst ` autInitConfig\<cdot>aut \<Longrightarrow> spf \<in> (stateSem step aut state) \<Longrightarrow> weak spf"
    and "\<forall>(initState, initOut) \<in> autInitConfig\<cdot>aut. 1 \<le> #\<^sub>\<surd>initOut \<and> wellformed initOut "
  shows "strong spf"
proof (rule strongI)
  fix s :: 'in
  obtain initState initOut spf2 where init_state_out_def: "(initState,initOut)\<in>autInitConfig\<cdot>aut"
    and spf2_statesem: "spf2\<in>(stateSem step aut) initState"
    and spf_apply: "spf\<cdot>s = initOut \<Zcat>\<Zcat> spf2\<cdot>s"
    using assms ndasem_pred apply auto[1]
    by (meson ndasem_pred)
  hence "#\<^sub>\<surd> s \<le> #\<^sub>\<surd> (spf2\<cdot>s)"
    using assms apply(simp add: weak_def) by fastforce
  thus " #\<^sub>\<surd> s <\<^sup>l #\<^sub>\<surd> (spf\<cdot>s)"
    apply(simp add: spf_apply)
    using tlen_conc[of initOut "spf2\<cdot>s"] assms(3) init_state_out_def
    by (metis (no_types, lifting) case_prodD 
        dual_order.trans lessequal_addition lnat_suc_plus)
qed
end  

end

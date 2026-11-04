theory Realizability
imports stream.eventStream

begin

default_sort countable


definition unreal:: "nat event stream \<rightarrow> nat event stream" where
"unreal = stream_step\<cdot>(\<lambda>a. \<Lambda> s.
   case a of Tick \<Rightarrow> \<up>(Event 20) \<Zcat> ((\<up>Tick)\<^sup>\<infinity>) | _ \<Rightarrow> ((\<up>Tick)\<^sup>\<infinity>))"

lemma unreal_weak: "weak (unreal)"
  unfolding unreal_def
  apply(rule weakI)
proof(case_tac i,simp,rule)
  fix i ::"nat event stream" and a::"nat event" and s::"nat event stream"
  assume a1:"i = \<up>a \<Zcat> s"
  have "#\<^sub>\<surd> (\<up>a \<Zcat> s)
       \<le> #\<^sub>\<surd> (stream_step\<cdot>
               (\<lambda>a::nat event. \<Lambda> (s::nat event stream). case a of Event (m::nat) \<Rightarrow> (\<up>Tick)\<^sup>\<infinity> | Tick \<Rightarrow> \<up>(Event (20::nat)) \<Zcat> ((\<up>Tick)\<^sup>\<infinity>))\<cdot>
               (\<up>a \<Zcat> s))"
    apply(subst stream_steps_sbe)
    apply(subst beta_cfun,simp)
    by(cases a;simp)
  thus "#\<^sub>\<surd> i
       \<le> #\<^sub>\<surd> (stream_step\<cdot>
               (\<lambda>a. \<Lambda> (s). case a of Event (m) \<Rightarrow> (\<up>Tick)\<^sup>\<infinity> | Tick \<Rightarrow> \<up>(Event (20::nat)) \<Zcat> ((\<up>Tick)\<^sup>\<infinity>))\<cdot>
               i)"
    apply(subst forw_subst[where a= i and b= "\<up>a \<Zcat> s"])
    apply (simp only: a1)
    apply blast
    ..
qed




definition realizable::"('a::{countable} event stream \<rightarrow> 'b::{countable} event stream) \<Rightarrow> bool"where
"realizable f \<equiv> weak f \<and>(\<forall>i. (wellformed i \<and> (#\<^sub>\<surd>(f\<cdot>i) = #\<^sub>\<surd>i))\<longrightarrow> (\<exists>t. f\<cdot>(i \<Zcat> \<up>Tick) \<sqsubseteq> f\<cdot>i \<Zcat>(\<up>Tick \<Zcat> t)))" 


lemma realizableI:
  assumes"\<And>s. wellformed s \<Longrightarrow> (#\<^sub>\<surd>(f\<cdot>s) = #\<^sub>\<surd>s) \<Longrightarrow> \<exists>t. f\<cdot>(s\<Zcat> \<up>Tick) \<sqsubseteq> f\<cdot>s \<Zcat>(\<up>Tick \<Zcat> t)"
  and "weak f"
  shows "realizable f"
  by(simp add: realizable_def assms)

lemma tlenleqlen[simp]:"#\<^sub>\<surd> (s::'a::countable event stream) \<le> #s"
  apply(induction s)
  apply(subst lnle_def)
  apply(rule adm_below)
  apply simp_all
  apply(case_tac a;simp)
  apply (simp add: lnat_suc_plus)
  by (meson dual_order.trans less_lnsuc)
(*
lemma "strong f \<Longrightarrow> realizable f"
proof(rule realizableI)
  fix s::"'a event stream"
  assume a1:"strong f"
  assume a2:"wellformed s"
  then have "#s = \<infinity> \<Longrightarrow> #(f\<cdot>s) = \<infinity>"
    using a1 apply(simp add: wellformed_stream_def strong_def)
    by (metis fold_inf inf_less_eq tlenleqlen)
  obtain t rt where t_def:"f\<cdot>(s) = t \bul rt"
  oops
lemma "realizable f \<Longrightarrow> weak f"
  by(simp add: realizable_def)
 

  text\<open>Show, that the example is indeed not realizable.\<close>
lemma "\<not> realizable (stream_step\<cdot>(\<lambda>a::nat event. \<Lambda> (s::nat event stream). case a of Tick \<Rightarrow> \<up>(Event (20::nat)) \<Zcat> ((\<up>Tick)\<^sup>\<infinity>) | _ \<Rightarrow> ((\<up>Tick)\<^sup>\<infinity>)))"
  oops
*)




(*
context 
begin
  fun new_event_below::"'a event \<Rightarrow> 'a event \<Rightarrow> bool" where
  "new_event_below Tick _ = True" | 
  "new_event_below (Event a) (Event b) = (a=b)" |
  "new_event_below (Event _) Tick = False"
  
  definition new_below::"'a::{countable} event stream \<Rightarrow> 'a event stream \<Rightarrow> bool" where
  "new_below a b = ((#a \<le> #b) \<and> (\<forall>n. Fin n < #a \<longrightarrow> new_event_below (snth n a) (snth n b)))"
  
  definition new_mono::"('a::{countable} event stream \<Rightarrow> 'b::{countable} event stream) \<Rightarrow> bool"where 
  "new_mono f = (\<forall>x y. new_below x y \<longrightarrow> new_below (f x) (f y))"
  
  definition new_realizable::"('a::{countable} event stream \<rightarrow> 'b::{countable} event stream) \<Rightarrow> bool"where
  "new_realizable f = (weak f \<and> new_mono (Rep_cfun f))"
  
  lemma [simp]: "new_below (\<up>a) (\<up>b) = new_event_below a b" 
    by(simp add: new_below_def)
  
  lemma new_below_botL[simp]:"new_below \<epsilon> a = True"
    apply(auto simp add: new_below_def)
    by (simp add: lnzero_def)
  
  lemma new_below_botR[simp]:"new_below a \<epsilon> = (a = \<epsilon>)"
    apply(auto simp add: new_below_def)
    by (simp add: lnzero_def)
  
  lemma new_below_step: "new_below (\<up>a \<Zcat> as) (\<up>b \<Zcat> bs) = (new_event_below a b \<and> new_below as bs)" 
    apply(auto simp add: new_below_def)
        apply(subgoal_tac " Fin 0 < lnsuc\<cdot>(#as) \<longrightarrow> new_event_below (snth 0 (\<up>a \<Zcat> as)) (snth 0 (\<up>b \<Zcat> bs))")
         apply simp
    apply blast
     apply (metis (no_types, lifting) Fin_Suc less2lnleD less_le_trans less_lnsuc lnsuc_lnle_emb order.not_eq_order_implies_strict snth_scons)
    apply(case_tac n; simp)
    done

  lemma "new_below (<[Tick, Tick, Tick]>) (<[Event a, Event b, Event c]>) "
    by(simp add: new_below_step)

  lemma "\<not>new_realizable unreal"
    apply(auto simp add: new_realizable_def unreal_weak new_mono_def)
    apply(rule exI [of _ "\<up>Tick"])
    apply(rule exI [of _  "\<up>(Event 42)"], auto)
    apply(simp add: unreal_def)
    apply(subst (asm)(2) sinftimes_unfold)
    apply(subst (asm) new_below_step)
    by simp
  
  lemma new2old_below: "new_below a b \<Longrightarrow> below a b"
    apply(cases a; cases b; simp)
    apply(auto simp add: new_below_step)
    sorry
  
  lemma new2old_mono: "new_mono f \<Longrightarrow> monofun f"
    apply(rule monofunI)
    apply(auto simp add: new_mono_def)
    sorry
end
hide_const new_event_below new_below new_mono new_realizable
*)




context 
begin
  fun new_event_below::"'a event \<Rightarrow> 'a event \<Rightarrow> bool" where
  "new_event_below Tick _ = True" | 
  "new_event_below (Event a) (Event b) = (a=b)" |
  "new_event_below (Event _) Tick = False"

  definition new_below::"'a::{countable} event stream \<Rightarrow> 'a event stream \<Rightarrow> bool" where
  "new_below a b = ((#a=\<infinity>            \<longrightarrow> a=b) \<and> 
                    ((#a < \<infinity> \<and> a\<noteq>\<epsilon>)  \<longrightarrow> (#a\<le>#b \<and> (\<exists>n. ((Fin (Suc n) = #a) \<and> (new_event_below (snth n a) (snth n b)) \<and> (\<forall>m. (m<n \<longrightarrow> (snth n a = snth n b))))))) \<and>
                     (a=\<epsilon>              \<longrightarrow> True))"

  lemma "new_below (<[Event a, Event b, Tick]>) (<[Event a, Event b, Event c]>)"
    oops

  definition new_mono::"('a::{countable} event stream \<Rightarrow> 'b::{countable} event stream) \<Rightarrow> bool"where 
  "new_mono f = (\<forall>x y. new_below x y \<longrightarrow> new_below (f x) (f y))"
  
  definition new_realizable::"('a::{countable} event stream \<rightarrow> 'b::{countable} event stream) \<Rightarrow> bool"where
  "new_realizable f = (weak f \<and> new_mono (Rep_cfun f))"
  
  lemma [simp]: "new_below (\<up>a) (\<up>b) = new_event_below a b" 
  by(subst new_below_def, simp)
    
  (*
  lemma new_below_botL[simp]:"new_below \<epsilon> a = True"
    by(auto simp add: new_below_def)
  
  lemma new_below_botR[simp]:"new_below a \<epsilon> = (a = \<epsilon>)"
    by(auto simp add: new_below_def)
  
  lemma new_below_step_1: "new_below (\<up>a \<Zcat> \<epsilon>) (\<up>b \<Zcat> bs) = new_event_below a b"
    apply(auto simp add: new_below_def)
  using new_event_below.elims(3) by blast

lemma new_below_step_2: "as\<noteq>\<epsilon> \<Longrightarrow> new_below (\<up>a \<Zcat> as) (\<up>b \<Zcat> bs) = (a=b \<and> new_below as bs)"
  apply(cases "bs = \<epsilon>")
   apply( simp add: new_below_def)+
  apply auto
    using less_all_sconsD apply auto[1]
    using less_all_sconsD apply blast
    using less_all_sconsD apply blast
    sledgehammer

lemma new_below_step: "new_below (\<up>a \<Zcat> as) (\<up>b \<Zcat> bs) = ((as=\<epsilon> \<longrightarrow> new_event_below a b) \<and> (as\<noteq>\<epsilon> \<longrightarrow> (a=b \<and> new_below as bs)))"
    apply(cases "as=\<epsilon>")
    apply(auto simp add: new_below_def)
    using new_event_below.elims(1) apply blast
    using less_all_sconsD apply auto[1]
    using less_all_sconsD apply blast
    using less_all_sconsD apply blast

    oops
        apply(subgoal_tac " Fin 0 < lnsuc\<cdot>(#as) \<longrightarrow> new_event_below (snth 0 (\<up>a \<Zcat> as)) (snth 0 (\<up>b \<Zcat> bs))")
         apply simp
    apply blast
     apply (metis (no_types, lifting) Fin_Suc less2lnleD less_le_trans less_lnsuc lnsuc_lnle_emb order.not_eq_order_implies_strict snth_scons)
    apply(case_tac n; simp)
    done

  lemma "new_below (<[Tick, Tick, Tick]>) (<[Event a, Event b, Event c]>) "
    by(simp add: new_below_step)*)
end

end
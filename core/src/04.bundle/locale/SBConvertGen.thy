theory SBConvertGen

imports SBGen

begin


locale sbUnionGen = 

fixes lFst::" 'a::{pcpo,len,conc} \<Rightarrow> 'fst::{chan}  \<Rightarrow> M stream"
  and lSnd::" 'b::{pcpo,len,conc} \<Rightarrow> 'snd::{chan}  \<Rightarrow> M stream"  
  and f::"'c::{pcpo,len,conc} \<Rightarrow> 'a \<times> 'b" 
  assumes sbgenfst:"sbGen lFst" and sbgensnd:"sbGen lSnd"
      and f_inj: "inj f"
      and f_surj: "\<And>(a::'a) (b::'b). (\<And>chan::'fst \<union> 'snd. Rep chan\<in>chDom TYPE('fst) \<inter> chDom TYPE('snd) \<Longrightarrow> lFst a (Abs (Rep chan)) = lSnd b (Abs (Rep chan))) \<Longrightarrow> \<exists>c. (a,b) = f c"
      and f_fst_surj: "surj (fst o f)"
      and f_snd_surj: "surj (snd o f)" 
      and f_cont: "cont f"
      and f_nbelow:"\<And>c1 c2. \<not>( c1 \<sqsubseteq> c2) \<Longrightarrow> \<not>(f c1 \<sqsubseteq> f c2)"
      and f_len:"\<And>c. #(f c) = #c"
      and disjoint:"(\<And>(c::'c)  (chan::'fst \<union> 'snd). Rep chan\<in>chDom TYPE('fst) \<inter> chDom TYPE('snd) \<Longrightarrow> lFst (fst (f c)) (Abs (Rep chan)) = lSnd (snd (f c)) (Abs (Rep chan)))"       
      and nemptyfst:"chDom TYPE('fst)= {} \<Longrightarrow> (\<And>x c (a::'a).  lFst x c = \<epsilon> \<and> #a = \<infinity>)" 
      and nemptysnd:"chDom TYPE('snd)= {} \<Longrightarrow> (\<And>x c (b::'b).  lSnd x c = \<epsilon> \<and> #b = \<infinity>)"
begin

definition constructor::"'c \<Rightarrow> ('fst \<union> 'snd) \<Rightarrow> M stream" where
"constructor = (\<lambda>c chan. (if (Rep chan) \<in>chDom TYPE('fst) then lFst (fst (f c)) (Abs (Rep chan)) else lSnd (snd (f c)) (Abs (Rep chan))))"

lemma f_surj_empty:"chDom TYPE('fst) \<inter> chDom TYPE('snd) = {} \<Longrightarrow> surj f"
  apply(simp add: surj_def)
  apply(subst f_surj)
  by simp+

lemma fstempty_singleton:
  assumes "chDom TYPE ('fst) = {}"
    shows "\<And> (x::'a) (y::'a). x = y"
proof -
  have inj: "inj lFst"
    by (simp add: sbGen.c_inj sbgenfst)
  then have "\<And> x y. lFst x = lFst y \<Longrightarrow> x=y"
    by (simp add: inj_eq)
  moreover have "\<And> x y. lFst x = lFst y"
    apply(subst fun_eq_iff,rule allI)
    apply(case_tac "Rep xa \<in> chDom TYPE('fst)")
    apply(simp add: assms) 
    by (simp add:  assms nemptyfst)+
  ultimately show "\<And>(x::'a) (y::'a). x = y" 
    by simp
qed

lemma sndempty_singleton:
  assumes "chDom TYPE ('snd) = {}"
  shows "\<And> (x::'b) (y::'b). x = y"
proof -
  have inj: "inj lSnd"
    by (simp add: sbGen.c_inj sbgensnd)
  then have "\<And> x y. lSnd x = lSnd y \<Longrightarrow> x=y"
    by (simp add: inj_eq)
  moreover have "\<And> x y. lSnd x = lSnd y"
    apply(subst fun_eq_iff,rule allI)
    apply(case_tac "Rep xa \<in> chDom TYPE('snd)")
    apply(simp add: assms)
    by (simp add: nemptysnd assms)+
  ultimately show "\<And>(x::'b) (y::'b). x = y" 
    by simp
qed

lemma cons_inj[simp]:"inj constructor"
proof(rule injI)
  fix x y::"('c)"
    assume cons_eq: "constructor x = constructor y"
    then have cons_eq2: "\<And>c. constructor x c = constructor y c"
      by simp
    
    have "\<And>c. Rep c \<in> chDom TYPE('fst) \<Longrightarrow> constructor x c = constructor y c"
          by (simp add: cons_eq)
    then have lfst_eq:"\<And>c. Rep c \<in> chDom TYPE('fst) \<Longrightarrow> lFst (fst (f x)) c = lFst (fst (f y)) c"
          apply(auto simp add: constructor_def)[1]
          by (metis Int_iff abs_reduction abs_rep_id chdom_union inter_union_id)

    show "x = y"
    proof -
      have fst_eq: "fst (f x) = fst (f y)"
      proof -
        have "\<And>c. Rep c \<notin> chDom TYPE('fst) \<Longrightarrow> lFst (fst (f x)) c = lFst (fst (f y)) c"
          by (metis (full_types) chdom_in fstempty_singleton)
        then show ?thesis 
          by (meson lfst_eq ext inj_eq sbGen.c_inj sbgenfst)
      qed

      moreover have snd_eq: "snd (f x) = snd (f y)"
      proof -
        have snd_abs_rep: "\<And> c y. Rep c \<in> chDom TYPE ('snd) \<Longrightarrow> lSnd (snd (f y)) c =  lSnd (snd (f y)) (Abs (Rep ((Abs (Rep c))::'fst \<union>'snd)))"
          by(subst rep_reduction, simp+)

        have "\<And>c. Rep c \<in> chDom TYPE('snd) \<Longrightarrow> constructor x c = constructor y c"
          by (simp add: cons_eq)
        then have "\<And>c. Rep c \<notin> chDom TYPE ('fst) \<Longrightarrow> Rep c \<in> chDom TYPE('snd) \<Longrightarrow> lSnd (snd (f x)) c = lSnd (snd (f y)) c"
          apply(simp add: constructor_def)
          by (metis Un_iff abs_reduction chdom_union snd_abs_rep)
        moreover have "\<And>c. Rep c \<in> chDom TYPE ('fst) \<Longrightarrow> Rep c \<in> chDom TYPE('snd) \<Longrightarrow> lSnd (snd (f x)) c = lSnd (snd (f y)) c"
        proof-
          fix c::"'snd" 
          assume c_fst:"Rep c \<in> chDom TYPE('fst)" and c_snd: "Rep c \<in> chDom TYPE('snd)"
          then have "chDom TYPE('fst) \<inter> chDom TYPE('snd) \<noteq> {}"
            by blast
          then have fst_snd_eq:"\<And>(c::'fst \<union> 'snd) x. Rep c \<in>  chDom TYPE('fst) \<inter> chDom TYPE('snd) \<Longrightarrow>  lFst (fst (f x)) (Abs (Rep c)) = lSnd (snd (f x)) (Abs (Rep c))"
            using disjoint by blast
          then have "\<And>x. lSnd (snd (f x)) c = lFst (fst (f x)) (Abs (Rep ((Abs (Rep c))::'fst \<union> 'snd)))"
            apply(subst snd_abs_rep)
            apply(simp add: c_fst c_snd)
            apply(subst fst_snd_eq, simp add: c_fst c_snd)
            by blast
          then show "lSnd (snd (f x)) c = lSnd (snd (f y)) c" 
            apply(simp)
            by (simp add: fst_eq)
        qed
        moreover have "\<And>c. Rep c \<notin> chDom TYPE('snd) \<Longrightarrow> lSnd (snd (f x)) c = lSnd (snd (f y)) c" 
          by (metis (full_types) cnotempty_cdom sndempty_singleton)
        
        ultimately have "\<And>c. lSnd (snd (f x)) c = lSnd (snd (f y)) c"
          by(case_tac "Rep c \<in> chDom TYPE('snd)"; case_tac "Rep c\<in> chDom TYPE('fst)"; auto)
        then have "lSnd (snd (f x)) = lSnd (snd (f y))"
          by(simp add: fun_eq_iff)  
          then show ?thesis
            apply(subst inj_eq, simp)
            by (simp add: inj_eq sbGen.c_inj sbgensnd)
      qed

      ultimately show ?thesis
        by (metis f_inj inv_f_f prod_eqI)
    qed
  qed

lemma constructor_values[simp]:"sValues\<cdot>(constructor a c) \<subseteq> ctype (Rep c)"
  apply(simp add: constructor_def)
  apply(case_tac "Rep c \<in> chDom TYPE('fst)";simp)
  using sbGen.c_type sbgenfst lsb_well_def
  apply (metis rep_reduction)
  apply(case_tac "Rep c \<in> chDom TYPE('snd)")
  using sbGen.c_type sbgensnd lsb_well_def 
  apply (metis rep_reduction)
  using sbGen.c_type sbgensnd union_empty by fastforce

lemma constructor_sbwell[simp]:"lsb_well (constructor a)"
  by(simp add: lsb_well_def)

lemma cons_cont_h[simp]:"cont(\<lambda> (a, b) chan::'fst \<union> 'snd.
         if Rep chan \<in> chDom TYPE('fst) then lFst a (Abs (Rep chan)) else lSnd b (Abs (Rep chan)))" 
  apply(intro cont2cont)
  by(simp add: cont2cont_fun sbGen.c_cont sbgenfst sbgensnd)+

lemma constructor_cont[simp]:"cont constructor" 
  apply(simp add: constructor_def)
  apply(intro cont2cont)
  apply(rule cont2cont_fun)
  apply(rule cont_compose,simp_all add: sbGen.c_cont sbgenfst f_cont)
  apply(rule cont2cont_fun)
  by(rule cont_compose,simp_all add: sbGen.c_cont sbgensnd f_cont)

lemma cons_eq_lfst[simp]:"chDom TYPE('snd) = {} \<Longrightarrow> chDom TYPE('fst) \<noteq> {} \<Longrightarrow> constructor x c = lFst (fst (f x)) (Abs (Rep c))"
  by (metis Un_empty_right chdom_union cnotempty_cdom constructor_def)

lemma cons_eq_lsnd[simp]:"chDom TYPE('fst) = {} \<Longrightarrow> chDom TYPE('snd) \<noteq> {} \<Longrightarrow>  constructor x c = lSnd (snd (f x)) (Abs (Rep c))"
  by (simp add: constructor_def)

lemma cons_empty[simp]:"chDom TYPE('fst) = {} \<Longrightarrow> chDom TYPE('snd) = {} \<Longrightarrow> constructor x c = \<epsilon>"
  by (simp add: constructor_def nemptysnd)

lemma cons_cinfst[simp]: "Rep c \<in> chDom TYPE('fst) \<Longrightarrow> constructor x c = lFst (fst (f x)) (Abs (Rep c))"
  by(simp add: constructor_def)

lemma cons_cnotinfst[simp]: "Rep c \<notin> chDom TYPE('fst) \<Longrightarrow> constructor x c = lSnd (snd (f x)) (Abs (Rep c))"
  by(simp add: constructor_def)


lemma lfst_well: "lsb_well sb \<Longrightarrow> chDom TYPE('fst) \<noteq> {} \<Longrightarrow> \<exists>a::'a.  sb = lFst a"
  using sbgenfst sbGen.c_surj by blast

lemma lsnd_well: "lsb_well sb \<Longrightarrow> chDom TYPE('fst) = {} \<Longrightarrow> chDom TYPE('snd) \<noteq> {} \<Longrightarrow> \<exists>b::'b.  sb = lSnd b"
  using sbgensnd sbGen.c_surj by blast

lemma f_fst_well: "\<exists>c b. f c = (a,b)" 
  by (metis (mono_tags, opaque_lifting) f_fst_surj comp_apply prod.collapse surjD)

lemma f_snd_well: "\<exists>c a. f c = (a,b)"  
  by (metis (mono_tags, opaque_lifting) f_snd_surj comp_apply prod.collapse surjD)

lemma constructor_well: assumes"lsb_well sb" shows"\<exists>c. sb = constructor c"
  apply(simp add: fun_eq_iff)
  apply(cases "chDom TYPE('fst) = {}"; cases "chDom TYPE('snd) = {}")
  using assms apply(simp add: lsb_well_def)
proof -
  assume a1:"chDom TYPE('fst)={}"
  assume a2:"chDom TYPE('snd)\<noteq>{}"

  have sbwell_snd:"lsb_well (\<lambda>x::'snd. sb (Abs(Rep x)))"
    by(rule subsb_well,simp_all add: assms nemptysnd a2)
  obtain b where b_def:"lSnd b = (\<lambda>x. sb (Abs(Rep x)))"
    by (metis (mono_tags, lifting) sbGen.c_surj sbwell_snd sbgensnd rangeE)
  then obtain a c where c_def:"f c = (a,b)"
    using f_snd_well by blast
  then have "\<And> x. sb x = constructor c x"
    apply(simp add: a1 a2 b_def)
    by(metis rep_reduction Rep_union Rep_union_def a1 a2 chdom_union uniondom_fstempty abs_rep_id)
  then show  "\<exists>c::'c. \<forall>x::'fst \<union> 'snd. sb x = constructor c x"
    by blast

next 
 assume a1:"chDom TYPE('fst)\<noteq>{}"
 assume a2:"chDom TYPE('snd)={}"

  have sbwell_fst:"lsb_well (\<lambda>x::'fst. sb (Abs(Rep x)))"
    by(rule subsb_well,simp_all add: assms nemptyfst a1)
  obtain a where a_def:"lFst a = (\<lambda>x. sb (Abs(Rep x)))"
    by (metis (mono_tags, lifting) sbGen.c_surj sbwell_fst sbgenfst rangeE)
  then obtain b c where c_def:"f c = (a,b)"
    using f_fst_well by blast
  then have "\<And> x. sb x = constructor c x"
    apply(simp add: a1 a2 a_def)
    by(metis rep_reduction Rep_union Rep_union_def a1 a2 chdom_union uniondom_sndempty abs_rep_id)
  then show  "\<exists>c::'c. \<forall>x::'fst \<union> 'snd. sb x = constructor c x"
    by blast

next
  assume a1:"chDom TYPE('fst)\<noteq>{}"
  assume a2:"chDom TYPE('snd)\<noteq>{}"
  have sbwell_fst:"lsb_well (\<lambda>x::'fst. sb (Abs(Rep x)))" and sbwell_snd:"lsb_well (\<lambda>x::'snd. sb (Abs(Rep x)))"
     apply(rule subsb_well,simp_all add: assms nemptyfst a1)
     by(rule subsb_well,simp_all add: assms nemptysnd a2)
  then obtain a where a_def:" lFst a = (\<lambda>c. sb (Abs(Rep c)))"
    by (metis (mono_tags, lifting) rangeE  sbGen.c_surj sbgenfst)
  obtain b where b_def:"lSnd b = (\<lambda>x. sb (Abs(Rep x)))"
    by (metis (mono_tags, lifting) sbGen.c_surj sbwell_snd sbgensnd rangeE)
   have "\<And>chan::'fst \<union> 'snd. Rep chan \<in> chDom TYPE('fst) \<inter> chDom TYPE('snd) \<Longrightarrow> lFst a (Abs (Rep chan)) = lSnd b (Abs (Rep chan))"
    using a_def b_def by auto
  then have "\<exists>c. f c = (a,b)"
    using f_surj by fastforce
  then obtain c where c_def:"f c = (a,b)"
    by auto
  then show "chDom TYPE('fst) \<noteq> {} \<Longrightarrow> chDom TYPE('snd) \<noteq> {} \<Longrightarrow> \<exists>c. \<forall>x. sb x = constructor c x"
    apply(simp add: constructor_def) 
    apply(rule exI[where x="c"],simp)
    apply(simp add: a_def b_def)
    using union_empty by force
  qed

lemma sbconst[simp]:assumes "lsb_well sb"
  shows "sb \<in> range constructor"
  using assms constructor_well by auto

lemma cont_inv[simp]:"\<And> x y. x \<notsqsubseteq> y \<Longrightarrow> constructor x \<notsqsubseteq> constructor y" 
proof(simp add: fun_below_iff)
  fix c1 c2::'c
  assume nbelow: "c1 \<notsqsubseteq> c2"
  obtain a1 b1 where f_c1: "f c1 = (a1, b1)"
    using prod.exhaust_sel by blast
  obtain a2 b2 where f_c2: "f c2 = (a2, b2)"
    using prod.exhaust_sel by blast
 
  have "a1 \<notsqsubseteq> a2 \<Longrightarrow>  lFst a1  \<notsqsubseteq> lFst a2 "
    by (simp add: sbGen.c_nbelow sbgenfst)
  then obtain xa where xa_def: "a1 \<notsqsubseteq> a2 \<Longrightarrow> lFst a1 xa \<notsqsubseteq> lFst a2 xa"
    by (meson fun_belowI)
  then have xa_dom: "a1 \<notsqsubseteq> a2 \<Longrightarrow> Rep xa \<in> chDom TYPE('fst)"
    by (metis (full_types) below_refl cnotempty_cdom fstempty_singleton)
  then obtain xa2::"'fst \<union> 'snd" where xa2_def: "a1 \<notsqsubseteq> a2 \<Longrightarrow> xa2 = Abs (Rep xa)" 
    by blast
  then have a_nbelow:"a1 \<notsqsubseteq> a2 \<Longrightarrow> constructor c1 xa2 \<notsqsubseteq> constructor c2 xa2"
    by(simp add: constructor_def xa_dom f_c1 f_c2 xa_def)

  have "b1 \<notsqsubseteq> b2 \<Longrightarrow>  lSnd b1  \<notsqsubseteq> lSnd b2 "
    by (simp add: sbGen.c_nbelow sbgensnd)
  then obtain xb where xb_def:"b1 \<notsqsubseteq> b2 \<Longrightarrow>  lSnd b1 xb \<notsqsubseteq> lSnd b2 xb"
    by (meson fun_belowI)
  then have xb_dom: "b1 \<notsqsubseteq> b2 \<Longrightarrow> Rep xb \<in> chDom TYPE('snd)"
    by (metis (full_types) below_refl cnotempty_cdom sndempty_singleton)
  then obtain xb2::"'fst \<union> 'snd" where xb2_def: "b1 \<notsqsubseteq> b2 \<Longrightarrow> xb2 = Abs (Rep xb)" 
    by blast
   have b_nbelow:"b1 \<notsqsubseteq> b2 \<Longrightarrow> constructor c1 xb2 \<notsqsubseteq> constructor c2 xb2"
    apply(simp add: constructor_def)
    apply(case_tac "Rep xb2\<in> chDom TYPE('fst)"; simp)
    apply(subst disjoint, simp add: xb2_def xb_dom)+
    by(simp add: f_c1 f_c2 xb2_def xb_def xb_dom)+

    show "\<exists>x::'fst \<union> 'snd. constructor c1 x \<notsqsubseteq> constructor c2 x"
      by (metis Pair_below_iff a_nbelow b_nbelow f_c1 f_c2 f_nbelow nbelow)
qed



lemma constminlen[simp]:"\<not>chDomEmpty TYPE('fst \<union> 'snd) \<Longrightarrow> #c \<le> #(constructor c x)"
  apply(case_tac "Rep x\<in>chDom TYPE('fst)"; simp)

  apply(case_tac "chDomEmpty TYPE('fst)", simp)
  apply(rule trans_lnle[where y="#(fst (f c))"])  
  apply (metis eq_fst_iff f_len len_prod_minl)
  apply(simp add: sbGen.c_len sbgenfst)
 
  apply(case_tac "chDomEmpty TYPE('snd)")
  using cnotempty_cdom uniondom_sndempty apply blast
  apply(rule trans_lnle[where y="#(snd (f c))"]) 
  apply (metis eq_snd_iff f_len len_prod_minr)
  by(simp add: sbGen.c_len sbgensnd)

lemma constlen[simp]:"\<not>chDomEmpty TYPE('fst \<union> 'snd) \<Longrightarrow> \<exists>x::'fst \<union> 'snd. #c = #(constructor c x)" 
  apply(case_tac "chDom TYPE('fst) = {}"; case_tac "chDom TYPE('snd) = {}"; simp)
  
  apply(simp add: f_len[symmetric] nemptyfst len_prod_def)
  apply(subgoal_tac "\<exists>x.  #(snd (f c)) = #(lSnd (snd (f c)) x)")
  apply(metis abs_rep_id chdom_in rep_reduction_alt uniondom_fstempty)
  apply(simp add: sbGen.c_lenex sbgensnd)

  apply(simp add: f_len[symmetric] nemptysnd len_prod_def)
  apply(subgoal_tac "\<exists>x.  #(fst (f c)) = #(lFst (fst (f c)) x)")
  apply(metis abs_rep_id chdom_in rep_reduction_alt uniondom_sndempty)
  apply(simp add: sbGen.c_lenex sbgenfst)

proof-
  fix c
  assume  fstdom: "chDom TYPE('fst) \<noteq> {}" and snddom:"chDom TYPE('snd) \<noteq> {}"
  obtain a b where f_c: "f c = (a,b)"
      by fastforce
  obtain xa where xa_def: "#a = #(lFst a xa)"
    using fstdom sbGen.c_lenex sbgenfst by blast
  then have xa_dom:"Rep xa \<in> chDom TYPE('fst)"
    by (simp add: fstdom)
  obtain xa2::"'fst \<union> 'snd" where xa2_def: "xa2 = Abs (Rep xa)"
      by simp
  then have c_len_1:"#a = #(constructor c xa2)"
    by(simp add: constructor_def xa2_def xa_dom xa_def f_c)    

  obtain xb where xb_def: "#b = #(lSnd b xb)"
    using snddom sbGen.c_lenex sbgensnd by blast
  then have xb_dom:"Rep xb \<in> chDom TYPE('snd)"
    by (simp add: snddom)
  obtain xb2::"'fst \<union> 'snd" where xb2_def: "xb2 = Abs (Rep xb)"
      by simp
  then have c_len_2:"#b = #(constructor c xb2)"
    apply(simp add: constructor_def)
    apply(case_tac "Rep xb \<in> chDom TYPE('fst)")
    apply(subst disjoint)
    by(simp add:  xb_def f_c xb_dom)+

  show "\<exists>x::'fst \<union> 'snd. #c = #(constructor c x)"
    apply(subst f_len[symmetric])
    apply(simp add: f_c len_prod_def)
    apply(case_tac "min (#a) (#b) = #a"; simp?)
    using c_len_1 apply blast 
    by (metis c_len_2 min_def)
qed

end

sublocale sbUnionGen \<subseteq> sbGen constructor
  by(standard, simp_all)


locale subsetGen = 
  fixes lConsSuper::"'sup::{pcpo, len,conc} \<Rightarrow> 'csSuper::{chan} \<Rightarrow> M stream"
    and lConsSub::"'sub::{pcpo, len,conc} \<Rightarrow> 'csSub::{chan} \<Rightarrow> M stream"
    and f :: "'sup \<Rightarrow> 'sub"

  assumes sbgensup:"sbGen lConsSuper" and sbgensub:"sbGen lConsSub"
  and  f_well:"\<And>c super. Rep c \<in> chDom TYPE('csSub) \<Longrightarrow> lConsSuper super (Abs (Rep c)) = lConsSub (f super) c"
  and  subset: "chDom TYPE('csSub) \<subseteq> chDom TYPE('csSuper)"

begin

lemma setter_sub_eq:"(sbGen.setter lConsSuper\<cdot>super)\<star> = sbGen.setter lConsSub\<cdot>(f super)"
  apply(rule sb_eqI,auto)
  apply(simp add: sbgensub sbGen.setter_getch)
  using f_well sbGen.setter_getch2 sbgensup subset by fastforce

lemma getter_sub_eq: "(sbGen.getter lConsSub)\<cdot>(super\<star>) = f ((sbGen.getter lConsSuper)\<cdot>super)"
  by (metis sbGen.get_set sbGen.set_get sbgensub sbgensup setter_sub_eq)

end


lemma subsetgen_transitive: 
    fixes cons1::"'a::{pcpo, len,conc} \<Rightarrow> 'cs1::{chan} \<Rightarrow> M stream"
      and cons2::"'b::{pcpo, len,conc} \<Rightarrow> 'cs2::{chan} \<Rightarrow> M stream"
      and cons3::"'c::{pcpo, len,conc} \<Rightarrow> 'cs3::{chan} \<Rightarrow> M stream"
  assumes "subsetGen cons2 cons1 f" 
      and "subsetGen cons3 cons2 g"
    shows "subsetGen cons3 cons1 ((f::'b \<Rightarrow> 'a) o (g::'c \<Rightarrow> 'b))"
  apply(unfold_locales, simp_all)  
  using assms(2) sbGen.c_type subsetGen.sbgensup apply blast
  using assms(2) sbGen.c_inj subsetGen.sbgensup apply blast
  using assms(2) sbGen.c_surj subsetGen.sbgensup apply blast
  using assms(2) sbGen.c_cont subsetGen.sbgensup apply blast
  using assms(2) sbGen.c_nbelow subsetGen.sbgensup apply blast
  using assms(2) sbGen.c_len subsetGen.sbgensup apply blast
  using assms(2) sbGen.c_lenex subsetGen.sbgensup apply blast
  using assms(1) sbGen.c_type subsetGen.sbgensub apply blast
  using assms(1) sbGen.c_inj subsetGen.sbgensub apply blast
  using assms(1) sbGen.c_surj subsetGen.sbgensub apply blast
  using assms(1) sbGen.c_cont subsetGen.sbgensub apply blast
  using assms(1) sbGen.c_nbelow subsetGen.sbgensub apply blast
  using assms(1) sbGen.c_len subsetGen.sbgensub apply blast
  using assms(1) sbGen.c_lenex subsetGen.sbgensub apply blast

  apply(subgoal_tac "\<And>(c::'cs1) (super::'c).  Rep c \<in> chDom TYPE('cs1) \<Longrightarrow> cons3 super (Abs (Rep c)) = cons2 (g super) (Abs (Rep c))",simp)
  apply(subst subsetGen.f_well[where lConsSuper="cons2" and lConsSub="cons1" and f="f"])
  apply(simp add: assms)+  

  apply(subgoal_tac "\<And>c::'cs2.Rep c \<in> chDom TYPE('cs2) \<Longrightarrow> cons3 supera (Abs (Rep c)) = cons2 (g supera) (Abs (Rep c))")
  apply(simp)
  apply (metis (mono_tags, opaque_lifting) assms(1) in_mono rep_reduction subsetGen.subset)

  apply(subst subsetGen.f_well[where lConsSuper="cons3" and lConsSub="cons2" and f="g"])
  apply(simp add: assms)+

  by (meson assms(1) assms(2) dual_order.trans subsetGen.subset)
             
  

context sbUnionGen
begin

lemma setter_split: "setter\<cdot>c = (sbGen.setter lFst\<cdot>(fst (f c))) \<uplus> (sbGen.setter lSnd\<cdot>(snd (f c)))"
  apply(rule sb_eqI)
  apply(case_tac "Rep ca \<in> chDom TYPE ('fst)")
  apply(auto simp add: constructor_def)[1]
  using constructor_def sbGen.setter_getch2 sbgenfst setter_getch apply fastforce
  using constructor_def sbGen.setter_getch2 sbgensnd setter_getch by fastforce


lemma getter_fst: "(sbGen.getter lFst)\<cdot>(sb\<star>) = fst (f (getter\<cdot>sb))"
  apply(subst set_get[symmetric])
  by(simp add: setter_split sbGen.get_set sbgenfst)

lemma rule_snd: "(\<And>x::'fst \<union> 'snd. Rep x \<in> chDom TYPE('snd ) \<Longrightarrow> P (Abs (Rep x))) \<Longrightarrow> (\<And>x::'snd. Rep x \<in> chDom TYPE('snd ) \<Longrightarrow> P x)"
  by (metis (full_types)UnI2 abs_rep_id chdom_union rep_reduction)

lemma getter_snd:"(sbGen.getter lSnd)\<cdot>(sb\<star>) = snd (f (getter\<cdot>sb))" 
  apply(case_tac "chDom TYPE('fst) \<inter> chDom TYPE('snd) = {}")
  apply (metis sbGen.get_set sbgensnd sbunion_snd set_get setter_split)
  apply(subst set_get[symmetric])
  apply(simp add: setter_split)
  apply(subgoal_tac "((sbGen.setter lFst)\<cdot>(fst (f (getter\<cdot>sb))) \<uplus> (sbGen.setter lSnd)\<cdot>(snd (f (getter\<cdot>sb))))\<star>\<^sub>2 = (sbGen.setter lSnd)\<cdot>(snd (f (getter\<cdot>sb)))")
  apply(simp add: sbGen.get_set sbgensnd)
  apply(rule sb_eqI)
  apply(rule rule_snd)
  apply(case_tac "Rep x \<in> chDom TYPE('fst)"; simp)
  apply(subst sbGen.setter_getch2, (simp add: sbgenfst)+)
  apply(subst sbGen.setter_getch, simp add: sbgensnd)
  by(simp add: disjoint)+

lemma getter_split:"f (getter\<cdot>sb) = ((sbGen.getter lFst)\<cdot>(sb\<star>\<^sub>1), (sbGen.getter lSnd)\<cdot>(sb\<star>\<^sub>2))"
  by(simp add: getter_fst getter_snd)

lemma getter_split2:" (getter\<cdot>sb) = (inv f) ((sbGen.getter lFst)\<cdot>(sb\<star>\<^sub>1), (sbGen.getter lSnd)\<cdot>(sb\<star>\<^sub>2))"
  by (metis f_inj getter_split inv_f_f)

interpretation subset_fst: subsetGen "constructor" "lFst" "fst o f"
  apply(unfold_locales)
  by(simp add: sbgenfst sbGen.c_type sbGen.c_inj sbGen.c_surj sbGen.c_cont sbGen.c_nbelow sbGen.c_len sbGen.c_lenex)+

lemma subset_fst[simp]: "subsetGen constructor lFst (fst o f)"           
  by (simp add: subset_fst.subsetGen_axioms)

interpretation subset_snd: subsetGen "constructor" "lSnd" "snd o f"
  apply(unfold_locales)
  apply(simp add: sbgensnd sbGen.c_type sbGen.c_inj sbGen.c_surj sbGen.c_cont sbGen.c_nbelow sbGen.c_len sbGen.c_lenex)+
  apply(simp add: constructor_def,auto)
  apply(subst rep_reduction[symmetric, where ?'cs2.0="'fst \<union> 'snd"], simp)
  by(subst disjoint, simp+)

lemma subset_snd[simp]: "subsetGen constructor lSnd (snd o f)"           
  by (simp add: subset_snd.subsetGen_axioms)

end

end
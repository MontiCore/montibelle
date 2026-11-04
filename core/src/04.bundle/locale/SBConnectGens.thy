theory SBConnectGens

imports SBEGen SBGen

begin


locale sbesbcon =
  fixes sbCons::"'a::{pcpo,len,conc} \<Rightarrow> 'cs::{chan,finite}  \<Rightarrow> M stream"
  and sbeCons::"'b::countable \<Rightarrow> 'cs \<Rightarrow> M"
  and f::"'b \<Rightarrow> 'a"
  assumes sbcons_well:"sbGen sbCons"
  and sbecons_well:"sbeGen sbeCons"
  and f_well:"\<And>sbe. sbGen.setter sbCons\<cdot>(f sbe) = sbe2sb (sbeGen.setter sbeCons sbe)"
  and conc_well:"sbGen.setter sbCons\<cdot>(a \<Zcat>\<Zcat> b) = sbGen.setter sbCons\<cdot>a \<Zcat>\<^sup>\<Omega> sbGen.setter sbCons\<cdot>b"
  and domnempty:"chDom TYPE('cs) \<noteq>{}"
begin

lemma sbsetter_unfold[simp]:"sbGen.setter sbCons\<cdot>(f start \<Zcat>\<Zcat> rst) = sbeGen.setter sbeCons start \<Zcat>\<^sup>\<surd> sbGen.setter sbCons\<cdot>(rst)"
  by(simp add: conc_well f_well)

lemma sbgetter_unfold[simp]:
  "sbGen.getter sbCons\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = f(sbeGen.getter sbeCons(sbe)) \<Zcat>\<Zcat> sbGen.getter sbCons\<cdot>(sb)"
  by (metis conc_well f_well sbGen.get_set sbGen.set_get sbcons_well sbeGen.set_get sbecons_well)

lemma sbesetter_unfold:"sbeGen.setterSB sbeCons\<cdot>(\<up>a \<Zcat> rst) = sbGen.setter sbCons\<cdot>(f a)  \<Zcat>\<^sup>\<Omega> sbeGen.setterSB sbeCons\<cdot>(rst)"
  by (simp add: f_well sbeGen.settersb_unfold sbecons_well)

lemma sbegetter_unfold:
  "sbeGen.getterSB sbeCons\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = \<up>(inv f(sbGen.getter sbCons\<cdot>(sbe2sb sbe))) \<Zcat> sbeGen.getterSB sbeCons\<cdot>(sb)"
  by (metis (no_types, lifting) f_inv_into_f f_well rangeI sbGen.get_set sbcons_well sbeGen.get_set sbeGen.gettersb_unfold sbeGen.set_get sbecons_well)


lemma getset_reduce[simp]:"(sbeGen.getterSB sbeCons\<cdot>(sbGen.setter sbCons\<cdot>(sbGen.getter sbCons\<cdot>(sbeGen.setterSB sbeCons\<cdot>b))))
       = b"
  by (simp add: sbGen.set_get sbeGen.getset_eq sbcons_well domnempty sbecons_well)

lemma getset_reducepre:"(sbGen.getter sbCons\<cdot>(sbeGen.setterSB sbeCons\<cdot>(sbeGen.getterSB sbeCons\<cdot>(sbGen.setter sbCons\<cdot>a))))
       \<sqsubseteq> a"
  by (metis monofun_cfun_arg sbGen.get_set sbcons_well sbeGen.getset_below sbecons_well)

end

end
<#t><#import "helper/Macros.ftl" as macro>
<#t><#import "helper/Tuple.ftl" as tuple>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="dt"       type="montibelle.focus._ast.ASTBundle" -->
<#t>
<#t>${tc.signature("comment", "th", "dt")}
<#t><#assign symbol = dt.symbol>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) bundle.MsgWithChan
    (* Gen  *) data_inc.Data_inc
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


default_sort type

declare len_prod_inf_snd[simp del]

<#include "Channels.ftl">


section \<open>Stream Bundle Constructors\<close>
<#if symbol.channels?has_content>

                                                             

                                                                                    
                                                                        

fun channelsChan::"<#rt>
<#list symbol.uniqueTypes() as t>('${type.converter(t)} \<Rightarrow> 'M) \<Rightarrow> </#list><#rt>
(<#list symbol.decardinalizedChannels() as c>'${type.converter(c.typeSymbol)}<#sep>\<times></#list>) \<Rightarrow> <#rt>
channels \<Rightarrow> 'M" where
    <#list symbol.decardinalizedChannels() as c>
        <#lt>"channelsChan<#rt>
        <#lt><#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list> <#rt>
        <#lt>(<#list symbol.decardinalizedChannels() as c1>${c1.pattern}<#sep>, </#list>) <#rt>
        <#lt>${c.localName} = <#rt>
        <#lt>${type.converter(c.typeSymbol)} ${c.pattern}"<#sep> |
    </#list>


                                                                                
definition %invisible channelsChan_inv :: "<#rt>
<#list symbol.uniqueTypes() as t>('${type.converter(t)} \<Rightarrow> 'M) \<Rightarrow> </#list><#rt>
(channels \<Rightarrow> 'M) \<Rightarrow> <#rt>
(<#list symbol.decardinalizedChannels() as c>'${type.converter(c.typeSymbol)}<#sep> \<times> </#list>)" where
"channelsChan_inv<#rt>
<#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list> bundle = (<#rt>
<#list symbol.decardinalizedChannels() as c>
    <#lt>inv ${type.converter(c.typeSymbol)} (bundle ${c.localName})<#rt>
<#sep>, </#sep></#list>)"

lemma %invisible channelsChan_surj_helper:
  assumes <#list symbol.decardinalizedChannels() as c>"f ${c.localName} \<in> range ${type.converter(c.typeSymbol)}"<#sep>
      and </#sep></#list>
    shows "channelsChan<#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list> <#rt>
    <#lt>(channelsChan_inv<#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list> f) = f"
  unfolding channelsChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma channelsChan_surj:
  assumes <#list symbol.decardinalizedChannels() as c>"f ${c.localName} \<in> range ${type.converter(c.typeSymbol)}"<#sep>
      and </#sep></#list>
    shows "f \<in> range (channelsChan<#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list>)"
  apply(subst channelsChan_surj_helper[symmetric, where <#list symbol.uniqueTypes() as t>${type.converter(t)}=${type.converter(t)}<#sep> and </#list>])
  by(simp_all add: assms)

lemma channelsChan_inj:
  assumes <#list symbol.uniqueTypes() as t>"inj ${type.converter(t)}"<#sep>
      and </#sep></#list>
    shows "inj (channelsChan<#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list>)"
  apply (auto simp add: inj_def)
  by (metis assms channelsChan.simps injD)+

definition buildSBE where
"buildSBE \<equiv> channelsChan<#rt>
  <#list symbol.uniqueTypes()>
    <#items as t>

    <@type.buildSBEConstructor t/><#sep> </#sep><#rt>
    </#items><#lt>"
  </#list>

declare buildSBE_def [simp]
<#else>

definition buildSBE :: "unit \<Rightarrow> channels \<Rightarrow> M" where
"buildSBE = undefined"
</#if>
<#if symbol.channels?has_content>

theorem build_ctype[simp]: "buildSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a)
  by(auto simp add: ctype_def image_iff)

theorem build_inj[simp]: "inj buildSBE"
  by (simp add: channelsChan_inj)

                                                                                          
                                                                                 
lemma build_range:
  "range (\<lambda>a. buildSBE a c) = ctype (Rep c)"
  apply(cases c)
    <#if symbol.channels[0].typeSymbol.timingSymbol.isTimeSyncronous()>
  apply(auto simp add: image_iff ctype_def)
  by (metis tsyn.simps(8))+
    <#elseif symbol.channels[0].typeSymbol.timingSymbol.isEventBased()>
  apply(auto simp add: image_iff ctype_def)
  by (metis event.simps(8))+
    <#else>
  by(auto simp add: image_iff ctype_def)
    </#if>

theorem build_surj[simp]:
  assumes "\<And>c. sbe c \<in> ctype (Rep c)"
    shows "sbe \<in> range buildSBE"
  apply(simp, rule channelsChan_surj)
    <#list symbol.decardinalizedChannels() as c>
  apply (metis ${c.localName}_rep assms ${c.typeSymbol.name}_ran)
    </#list>
  done
</#if>

declare buildSBE_def [simp del]

global_interpretation SBE: <#if symbol.channels?has_content>sbeGen "buildSBE"<#else>sbeGen_empty</#if>
  defines sbesetter = SBE.setter
  and sbegetter = SBE.getter
  and sbesettersb = SBE.setterSB
<#if symbol.channels?has_content>
  by %visible(unfold_locales,simp_all)
<#else>
  done
</#if>
<#if symbol.channels?has_content>

definition buildSB where
"buildSB \<equiv> channelsChan
    <#list symbol.uniqueTypes() as t>
     (Rep_cfun (smap (${type.prefix(symbol.timing)} ${type.constructor(t)})))${t?is_last?then("\"", "")}
    </#list>

declare buildSB_def [simp]

lemma conc2sconc: "buildSB a1 c \<Zcat> buildSB a2 c = buildSB (a1 \<Zcat>\<Zcat> a2) c"
  apply(cases a1; cases a2; cases c)
    by(auto simp add: conc_prod_apply smap_split)+

theorem buildsb_ctype[simp]: "sValues\<cdot>(buildSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  apply (auto simp add: ctype_def smap_sValues image_iff)
                                                            
  apply (metis surj_pair tsyn.exhaust event.exhaust)?
  done

theorem buildsb_inj[simp]: "inj buildSB"
  by (auto simp add: channelsChan_inj smap_inj)

theorem buildsb_surj[simp]:
  assumes "lsb_well sb"
    shows "sb \<in> range buildSB"
  apply (simp, rule channelsChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
    <#list symbol.decardinalizedChannels() as c>
  using ${c.typeSymbol.name}_ran apply simp
    </#list>
  done

lemma channelsChan_split: "channelsChan<#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list> x = <#rt>
channelsChan<#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list> (${tuple.split(symbol.decardinalizedChannels()?size, "x")})"
  by auto

lemma cont_h:
  shows "<#list symbol.uniqueTypes() as t>cont ${type.converter(t)}<#sep> \<and> </#list> \<Longrightarrow>
         cont (\<lambda>x. channelsChan<#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list> x c)"
  apply(cases c, auto)
    <#if symbol.decardinalizedChannels()?size != 1>
  apply(subst channelsChan_split, simp only: channelsChan.simps, intro cont2cont; simp)+
    </#if>
  done

lemma cont[cont2cont]:
  shows "<#list symbol.uniqueTypes() as t>cont ${type.converter(t)}<#sep> \<and> </#list> \<Longrightarrow>
         cont (channelsChan<#list symbol.uniqueTypes() as t> ${type.converter(t)}</#list>)"
  by (simp add: cont_h)

lemma [simp]: "cont buildSB"
  by(simp, rule cont, simp)

lemma [simp]:"\<not> x \<sqsubseteq> y \<Longrightarrow> \<not> buildSB x \<sqsubseteq> buildSB y"
  apply(subst fun_below_iff,auto)
    <#if symbol.decardinalizedChannels()?size gt 1>
  apply(cases x; cases y; auto)
    </#if>
  apply(<#rt>
    <#list symbol.decardinalizedChannels() as c>
      solves\<open>(rule_tac x="${c.localName}" in exI,simp)\<close><#sep> |
    </#list>)+
  done

declare tlen_prod_inf_snd[simp del]

<#if symbol.timing.isTimeSyncronous()>
lemma [simp]: "(#a) <= (#\<^sub>\<surd>(buildSB a c))"
  apply (cases c; simp; fail)?
  apply (cases c;cases a; auto?, simp_all?)?
  by (simp_all add: tlen_prod_minl tlen_prod_rsmaller len_prod_minl len_prod_rsmaller)?

lemma [simp]: "\<exists>c. (#a) = (#\<^sub>\<surd>(buildSB a c))"
  apply ((rule channels_exists, simp); fail|cases a; auto?, simp?)
  apply (rule channels_exists, simp)?
  apply auto?
  apply ((subst len_prod_def2)+)?
  apply ((subst(asm) len_prod_def2)+)?
  apply ((subst tlen_prod_def2)+)?
  apply ((subst(asm) tlen_prod_def2)+)?
  by (smt min_def)?

</#if>
lemma [simp]: "#a \<le> #(buildSB a c)"
  apply(cases c; simp; fail)?
  apply (cases c; cases a; auto?, simp_all?)?
  by (simp_all add: len_prod_minl len_prod_rsmaller tlen_prod_minl tlen_prod_rsmaller)?

lemma [simp]: "\<exists>c. #a = #(buildSB a c)"
  apply ((rule channels_exists, simp); fail|cases a; auto?, simp?)
  apply (rule channels_exists, simp)?
  apply auto?
  apply ((subst len_prod_def2)+)?
  apply ((subst(asm) len_prod_def2)+)?
  apply ((subst tlen_prod_def2)+)?
  apply ((subst(asm) tlen_prod_def2)+)?
  by (smt min_def)?

lemma [simp]: "(#\<^sub>\<surd>a) <= (#\<^sub>\<surd>(buildSB a c))"
  apply (cases c; simp; fail)?
  apply (cases c;cases a; auto?, simp_all?)?
  by (simp_all add: tlen_prod_minl tlen_prod_rsmaller len_prod_minl len_prod_rsmaller)?

lemma [simp]: "\<exists>c. (#\<^sub>\<surd>a) = (#\<^sub>\<surd>(buildSB a c))"
  apply ((rule channels_exists, simp); fail|cases a; auto?, simp?)
  apply (rule channels_exists, simp)?
  apply auto?
  apply ((subst len_prod_def2)+)?
  apply ((subst(asm) len_prod_def2)+)?
  apply ((subst tlen_prod_def2)+)?
  apply ((subst(asm) tlen_prod_def2)+)?
  by (smt min_def)?

declare buildSB_def[simp del] tlen_len_eq[simp del] tlen_prod_inf_snd[simp]

</#if>

global_interpretation SB: <#if symbol.channels?has_content>sbtGen "buildSB"<#else>sbGen_empty</#if>
  defines sbsetter = SB.setter
      and sbgetter = SB.getter
<#if symbol.channels?has_content>
  apply(unfold_locales)
        by(simp_all add: lsb_well_def)
<#else>
  done
</#if>

lemma getter_fold: "sbGen.getter <#if symbol.channels?has_content>buildSB<#else>${symbol.theorySymbol.filename?lower_case}_buildSB</#if> = sbgetter"
  by (simp add: sbgetter_def)

lemma setter_sbe2sb: "sbe2sb (SBE.setter(<#list symbol.decardinalizedChannels() as c>${c.pattern}<#sep>, </#list>))<#rt>
                <#lt> = SB.setter\<cdot>(<#list symbol.decardinalizedChannels() as c>\<up>${c.pattern}<#sep>, </#list>)"
<#if symbol.channels?has_content>
  apply(rule sb_eqI2)
  apply(case_tac c, auto)
  by(simp add: buildSBE_def buildSB_def)+
<#else>
  by auto
</#if>

lemma setter_conc2sbconc: "SB.setter\<cdot>(s1 \<Zcat>\<Zcat> s2)<#rt>
                   <#lt> = SB.setter\<cdot>s1 \<Zcat>\<^sup>\<Omega> SB.setter\<cdot>s2"
  by(subst SB.getter_conc[symmetric], simp_all<#if symbol.channels?has_content> add: conc2sconc</#if>)

lemma getter_conc2sbconc: "SB.getter\<cdot>sb1 \<Zcat>\<Zcat> SB.getter\<cdot>sb2<#rt>
                   <#lt> = SB.getter\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> sb2)"
  by (metis setter_conc2sbconc SB.get_set SB.set_get)

<#if symbol.channels?has_content>
lemma setter_len[simp]: "#(SB.setter\<cdot>(<#list symbol.decardinalizedChannels() as c>${c.pattern}<#sep>, </#list>)) = <#rt>
  <#lt>Min {<#list symbol.decardinalizedChannels() as c>#${c.pattern}<#sep>, </#list>}"
  apply (subst SB.setter_len, simp)
  <#if symbol.decardinalizedChannels()?size gt 1>
  apply (simp only: len_prod_def2)+
  apply (subst Min2min, simp)+
  </#if>
  by (simp only: Min_singleton)
<#else>
lemma "SB.setter\<cdot>() = \<bottom>"
  by simp
</#if>

declare len_prod_inf_snd[simp]


end

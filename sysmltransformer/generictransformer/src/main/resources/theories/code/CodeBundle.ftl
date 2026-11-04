<#t><#import "../helper/Tuple.ftl" as tuple>
<#t><#import "../helper/Type.ftl" as type>
<#t><#import "../helper/Channel.ftl" as channel>
<#t><#import "../helper/Macros.ftl" as macro>
<#t>
<#t><#-- @ftlvariable name="tc"      type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment" type="Boolean" -->
<#t><#-- @ftlvariable name="th"      type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="dt"      type="montibelle.focus._symboltable.BundleSymbol" -->
<#t><#-- @ftlvariable name="typePrinter" type="trafos.ITypePrinter" -->
<#t>
<#t>${tc.signature("comment", "th", "dt")}
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${dt.codeTheorySymbol.astNode.filename}
  imports
    (* Gen  *) ${dt.theorySymbol.importFrom(dt.codeTheorySymbol)}
    (* Core *) bundle.SBCodegen
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


<#if dt.channels?has_content>
lemma [code]:"Enum.enum_ex (P::channels \<Rightarrow> bool) =  (\<exists>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

lemma [code]:"Enum.enum_all (P::channels \<Rightarrow> bool) =  (\<forall>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

<#list dt.decardinalizedChannels() as c>
lemma [code,simp]:"Rep_channels ${c.localName} = <@channel.description c/>"
using ${c.localName}_rep Rep_channels_def by auto

lemma[code]:" Abs_channels <@channel.description c/> = ${c.localName}"
by(simp add: ${c.localName}_def)

</#list>

<#list dt.uniqueTypes() as t>
fun conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")} ::"M \<Rightarrow> ${type.timedType(t)}" where
"conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")} (Timed ( ${type.timeConstructor(dt.timing)} <#rt>
<#lt>( ${type.messageWrapper(dt.timing)} (${type.constructor(t)} a)))) = ${type.messageWrapper(dt.timing)} a"|
"conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")} (Timed (${type.timeConstructor(dt.timing)} ${type.tickValue(dt.timing)})) = ${type.tickValue(dt.timing)}"|
"conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")}  v = inv <@type.buildSBEConstructor t/> v"

lemma inv2conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")}[code_abbrev]:"(conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")} a) = inv <@type.buildSBEConstructor t/> a"
  apply(cases a,simp_all)
  apply(case_tac x2,simp_all)
  by(rename_tac x1,case_tac x1;
    (rename_tac x2,case_tac x2;
    (simp add: inv_f_eq | rename_tac x3, case_tac x3)+))

</#list>
lemma [code_abbrev]:"sbesetter = sbeGen.setter buildSBE"
  by(simp add: sbesetter_def)

lemma sbegeth: assumes <#rt>
                <#list dt.decardinalizedChannels() as c>
                  <#lt>"a ${c.localName} \<in> range <@type.buildSBEConstructor c.typeSymbol/>"
                    <#sep>and </#sep><#rt>
                </#list>
    shows "inv (channelsChan <#list dt.uniqueTypes() as t><@type.buildSBEConstructor t/><#sep> </#sep></#list>) a = <#rt>
          <#lt>channelsChan_inv <#list dt.uniqueTypes() as t><@type.buildSBEConstructor t/><#sep> </#sep></#list> a"
  unfolding channelsChan_inv_def
(*
  using assms inv_f_f channelsChan_inv_def channelsChan_surj_helper buildSBE_def build_inj by metis
*)
sorry

lemma sbegeth2 :assumes "\<forall>c. a c \<in> ctype (Rep c)"
  shows"sbegetter (Abs_sbElem (Some a)) = inv buildSBE a"
  by (metis assms(1) Abs_sbElem_inverse SBE.getter_def mem_Collect_eq option.simps(5) sbElem_well.simps(2))

lemma [code]:"sbegetter sbe = (case Rep_sbElem sbe of Some (f::channels \<Rightarrow> M)
\<Rightarrow> (<#rt>
  <#list dt.decardinalizedChannels() as c>
    <#lt>(inv <@type.buildSBEConstructor c.typeSymbol/> (the (Rep_sbElem (sbe)) ${c.localName})))<#rt>
    <#sep>, (</#sep><#t>
  </#list><#lt>)"
  apply(cases sbe, case_tac y)
  apply (simp add: option.case_eq_if)+
  apply(subst Abs_sbElem_inverse,simp_all)+
(* Doesn't work for cc
  by (metis buildSBE_def build_surj channelsChan.simps channelsChan_inv_def f_inv_into_f rangeI sbegeth sbegeth2)
*)
  sorry

lemma [code_abbrev]:"sbegetter = sbeGen.getter buildSBE"
by(simp add: sbegetter_def)

lemma [ccode]:" sbesettersb\<cdot>((updis l) && ls) = (sbesetter ( l)) \<Zcat>\<^sup>\<surd> (sbesettersb\<cdot>ls)"
  and [ccode]:" sbesettersb\<cdot> \<epsilon> = botsb"
  using sbesettersb_def apply auto[1]
  by (simp add: botsb_eq)

lemma [code_abbrev]:"(\<lambda>a. sbesettersb\<cdot>a) = (\<lambda>a. sbeGen.setterSB buildSBE\<cdot>a)"
  by(simp add: sbesettersb_def)

lemma [code]:"Rep_cfun sbesettersb = sbesettersb_nc"
  by(simp add: sbesettersb_nc_def)

definition insbsetter_nc::" <@channel.streamTypes dt.decardinalizedChannels()/> \<Rightarrow> channels\<^sup>\<Omega>" where
"insbsetter_nc =  Abs_lsb o buildSB"

lemma[code]:"Rep_lsb(insbsetter_nc a) = buildSB a"
  using insbsetter_nc_def SB.setter.rep_eq SB.setter_rep by auto

lemma[code]:"Rep_cfun(sbsetter) =  insbsetter_nc"
  using insbsetter_nc_def SB.setter.rep_eq sbsetter_def by auto

lemma[code]:"Rep_cfun(sbgetter) = (inv buildSB) o  Rep_lsb"
  by(simp add: SB.getter.rep_eq)

<#list dt.decardinalizedChannels() as c>
lemma sbgetterh${c?index+2}:"Rep_lsb sb ${c.localName} = smap <@type.buildSBEConstructor c.typeSymbol/><#rt>
  <#lt>\<cdot>${tuple.getNth(dt.decardinalizedChannels()?size, c?index, "((inv buildSB o Rep_lsb) sb)")}"
(* Doesn't work for cc
  by (metis SB.getter.rep_eq SB.set_get SB.setter_rep buildSB_def channelsChan.simps)
*)
  sorry

</#list>
<#list dt.uniqueTypes() as t>
lemma smap_conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")}:" smap (inv  <@type.buildSBEConstructor t/>)\<cdot>s = smap conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")}\<cdot>s"
  apply(induction s,simp_all)
  apply(subst inject_scons,simp_all)
  by(simp add: inv2conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")} comp_def)

</#list>

lemma sbgetterh:"sbgetter\<cdot> sb = ( <#list dt.decardinalizedChannels() as c>
  smap conv_${typePrinter.print(c.typeSymbol.symType)?replace("[^A-Za-z0-9]", "", "r")}\<cdot> (Rep_lsb sb ${c.localName}) <#rt>
  <#sep>, </#sep>
</#list> ) "
  apply(simp add: sbgetter_def)
(*
  using SB.getter_def  smapsmap2smap <#list dt.decardinalizedChannels() as c>sbgetterh${c?index+2} </#list>
  SB.getter.abs_eq inj_compose inj_tonetimed sbgetter_def <#list dt.uniqueTypes() as t>${type.constructor(t)}_inj </#list> smap_inv_eq
  by (metis prod.collapse <#list dt.uniqueTypes() as t>smap_conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")} </#list>)
*)
  sorry

lemma [code_abbrev]:"(\<lambda>a. (<#list dt.decardinalizedChannels() as c><#rt>
  <#lt>smap conv_${typePrinter.print(c.typeSymbol.symType)?replace("[^A-Za-z0-9]", "", "r")}\<cdot> (Rep_lsb a ${c.localName})<#sep>, </#sep></#list>)) <#rt>
= (\<lambda>a. ((inv buildSB) o  Rep_lsb) a)"
  apply(simp add: buildSB_def channelsChan_inv_def)
  using SB.getter.rep_eq buildSB_def sbgetterh <#list dt.uniqueTypes() as t>smap_conv_${typePrinter.print(t.symType)?replace("[^A-Za-z0-9]", "", "r")} </#list>
  by auto
</#if>
<#if !dt.channels?has_content>
lemma [code]:"Enum.enum_ex (P::channels \<Rightarrow> bool) =  (\<exists>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

lemma [code]:"Enum.enum_all (P::channels \<Rightarrow> bool) =  (\<forall>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)
</#if>


end

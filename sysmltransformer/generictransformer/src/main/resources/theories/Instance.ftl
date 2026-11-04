<#t><#import "helper/Parameter.ftl" as para>
<#t><#import "helper/Import.ftl" as import>
<#t><#import "helper/Macros.ftl" as macro>
<#t>
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="inst" type="montibelle.focus._ast.ASTInstance" -->
<#t>
<#function inputTypeInst inst>
<#-- @ftlvariable name="inst" type="montibelle.focus._ast.ASTInstance" -->
  <#if inst.input.channels?has_content>
    <#return inst.inputBundleSymbol.theorySymbol.filename + ".channels">
  <#else>
    <#return inst.spsSymbol.input.theorySymbol.filename + ".channels">
  </#if>
</#function>
<#function outputTypeInst inst>
<#-- @ftlvariable name="inst" type="montibelle.focus._ast.ASTInstance" -->
  <#if inst.output.channels?has_content>
    <#return inst.outputBundleSymbol.theorySymbol.filename + ".channels">
  <#else>
    <#return inst.spsSymbol.output.theorySymbol.filename + ".channels">
  </#if>
</#function>
<#t>
<#t>
<#t><#-- @ftlvariable name="tc"        type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="inst"      type="montibelle.focus._ast.ASTInstance" -->
<#t>
<#t>${tc.signature("comment", "th", "inst")}
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) ${import.datatype(inst.symbol)}<#rt>
         <#lt> ${inst.spsSymbol.theorySymbol.importFrom(inst.theorySymbol)}<#rt>
         <#lt> ${inst.inputMap.theorySymbol.importFrom(inst.theorySymbol)}<#rt>
         <#lt> ${inst.outputMap.theorySymbol.importFrom(inst.theorySymbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


definition Sps :: "<@para.type inst.symbol/> \<Rightarrow> <#rt>
  <#lt>(${inputTypeInst(inst)}\<^sup>\<Omega> \<rightarrow> ${outputTypeInst(inst)}\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> <@para.pattern inst.symbol/>. <#rt>
<#lt><#if inst.spsSymbol.input.channels?has_content>${inst.inputMap.theorySymbol.filename}.Sps <@para.pattern inst.inputMap.symbol/> \<then> </#if><#rt>
<#lt>${inst.spsSymbol.theorySymbol.filename}.Sps <@para.value inst.symbol/><#rt>
<#lt><#if inst.spsSymbol.output.channels?has_content> \<then> ${inst.outputMap.theorySymbol.filename}.Sps <@para.pattern inst.outputMap.symbol/></#if>"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> ${inst.spsSymbol.theorySymbol.filename}.Sps <@para.value inst.symbol/> <#rt>
  <#lt>\<Longrightarrow> P (${inst.spsSymbol.input.theorySymbol.filename}.SB.getter\<cdot>sb) (${inst.spsSymbol.output.theorySymbol.filename}.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps <@para.pattern inst.symbol/>"
    shows "P (${inst.input.theorySymbol.filename}.SB.getter\<cdot>sb) (${inst.output.theorySymbol.filename}.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def ${inst.inputMap.theorySymbol.filename}.Sps_def ${inst.outputMap.theorySymbol.filename}.Sps_def
    oo_def ${inst.inputMap.theorySymbol.filename}.connector.rep_eq ${inst.outputMap.theorySymbol.filename}.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis ${inst.spsSymbol.input.theorySymbol.filename}.SB.get_set)


end

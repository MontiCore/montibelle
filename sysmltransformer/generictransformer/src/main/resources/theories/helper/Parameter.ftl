<#---->
<#macro pattern sps>
<#---->
<#-- @ftlvariable name="sps"       type="montibelle.focus._symboltable.SpsSymbol"-->
  <#lt>(<#rt>
    <#list sps.parameters as p>
      <#lt>${p.name}<#rt>
      <#sep>, <#t>
    </#list>
  <#lt>)<#rt>
</#macro>

<#macro type sps>
<#---->
<#-- @ftlvariable name="sps" type="montibelle.focus._symboltable.SpsSymbol"-->
  <#if sps.parameters?has_content>
    <#list sps.parameters>
      <#lt>(<#rt>
      <#items as p>
        <#lt>${typePrinter.print(p.symType)}<#rt>
        <#sep> \<times> <#t>
      </#items>
      <#lt>)<#rt>
    </#list>
  <#else>
    <#lt>unit<#rt>
  </#if><#t>
</#macro>

<#macro value inst>
<#---->
<#-- @ftlvariable name="inst"      type="montibelle.focus._symboltable.InstanceSymbol"-->
  <#lt>(<#rt>
  <#list inst.parameterValues as v>
    <#lt>${v.value}<#rt>
    <#sep>, <#t>
  </#list>
  <#lt>)<#rt>
</#macro>

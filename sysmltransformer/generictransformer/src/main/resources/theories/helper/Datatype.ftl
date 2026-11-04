<#import "Type.ftl" as type>
<#import "Channel.ftl" as channel>

<#macro pattern dt>
<#---->
<#-- @ftlvariable name="dt" type="montibelle.focus._symboltable.BundleSymbol"-->
  <#if dt.channels?has_content>
    <#list dt.decardinalizedChannels()>
      <#lt>(<#rt>
      <#items as c>
        <#lt>${c.pattern}<#rt>
        <#sep>, </#sep><#t>
      </#items>
      <#lt>)<#rt>
    </#list>
  <#else>
    <#t>()
  </#if><#t>
</#macro>

<#macro letPattern dt>
<#---->
<#-- @ftlvariable name="dt" type="montibelle.focus._symboltable.BundleSymbol"-->
  <#list dt.channels as c>
    <#if c.cardinality gt 1><#---->
      <#lt>let ${c.pattern} = [<#list 1..c.cardinality as i> ${c.pattern}_${i}<#sep>, </#list>] in<#rt>
    </#if>
  </#list>
</#macro>

<#macro parameter dt>
<#---->
<#-- @ftlvariable name="dt" type="montibelle.focus._symboltable.BundleSymbol"-->
  <@channel.parameter dt.channels/>
</#macro>

<#macro types dt suffix="">
<#---->
<#-- @ftlvariable name="dt" type="montibelle.focus._symboltable.BundleSymbol"-->
  <@channel.types dt.decardinalizedChannels() suffix/>
</#macro>

<#macro streamTypes dt>
<#---->
<#-- @ftlvariable name="dt" type="montibelle.focus._symboltable.BundleSymbol"-->
  <@types dt "stream"/><#t>
</#macro>

<#function buildSB dt>
<#---->
<#-- @ftlvariable name="dt" type="montibelle.focus._symboltable.BundleSymbol"-->
  <#if dt.channels?has_content>
    <#return "${dt.theorySymbol.filename}.buildSB">
  <#else>
    <#return "${dt.theorySymbol.filename?lower_case}_buildSB">
  </#if>
</#function>

<#import "Type.ftl" as type>

<#macro description channel>
<#---->
<#-- @ftlvariable name="channel" type="montibelle.focus._symboltable.ChannelSymbol" -->
  <#lt>(CH ''${channel.localName}'' ${type.timeType(channel.typeSymbol.timingSymbol)} ${type.msgType(channel.typeSymbol)})<#rt>
</#macro>

<#function constructor channel>
<#---->
<#-- @ftlvariable name="channel" type="montibelle.focus._symboltable.ChannelSymbol" -->
    <#return channel.name + "Constr">
</#function>

<#macro list channels>
<#---->
<#-- @ftlvariable name="channels"  type="java.util.List<montibelle.focus._symboltable.ChannelSymbol>" -->
  <#if channels?has_content>
    <#list channels as c>
      <@description c/>
      <#sep>, <#t>
    </#list>
  <#else>
    <#lt>(CH ''cempty'' TUntimed TNone)<#rt>
  </#if>
</#macro>

<#macro uniqueTypes dt suffix="">
<#---->
<#-- @ftlvariable name="dt" type="montibelle.focus._symboltable.BundleSymbol"-->
  <#if dt.uniqueTypes()?has_content>
    <#lt>(<#rt>
    <#list dt.uniqueTypes() as t>
      <#lt>${type.timedType(t)}<#if suffix?has_content> ${suffix}</#if><#rt>
      <#sep> \<times> <#t>
    </#list>
    <#lt>)<#rt>
  <#else>
    <#lt>unit<#rt>
  </#if><#t>
</#macro>

<#macro types channels suffix="">
<#---->
<#-- @ftlvariable name="channels" type="java.util.List<montibelle.focus._symboltable.ChannelSymbol>"-->
  <#if channels?has_content>
    <#lt>(<#rt>
    <#list channels as c>
      <#lt>${type.timedType(c.typeSymbol)}<#if suffix?has_content> ${suffix}</#if><#rt>
      <#sep> \<times> <#t>
    </#list>
    <#lt>)<#rt>
  <#else>
      <#lt>unit<#rt>
  </#if><#t>
</#macro>

<#macro streamTypes channels>
<#---->
  <@types channels "stream"/><#t>
</#macro>

<#macro parameter channels>
<#---->
<#-- @ftlvariable name="channels" type="java.util.List<montibelle.focus._symboltable.ChannelSymbol>"-->
  <#lt>(<#rt>
  <#list channels as c>
    <#lt>${c.pattern}<#rt>
    <#sep>, <#t>
  </#list>
  <#lt>)<#rt>
</#macro>


<#function constructor type>
<#---->
<#-- @ftlvariable name="type" type="montibelle.focus._symboltable.ChannelTypeSymbol"-->
  <#return typePrinter.print(type.symType)?replace("[^A-Za-z0-9]", "", "r") + type.timingSymbol.name + "Constr">
</#function>

<#function converter type>
<#---->
<#-- @ftlvariable name="type" type="montibelle.focus._symboltable.ChannelTypeSymbol"-->
  <#return typePrinter.print(type.symType)?replace("[^A-Za-z0-9]", "", "r") + type.timingSymbol.name + "Conv">
</#function>

<#function timedType type>
<#---->
<#-- @ftlvariable name="type" type="montibelle.focus._symboltable.ChannelTypeSymbol"-->
  <#if type.timingSymbol.isTimeSyncronous()>
    <#return typePrinter.print(type.symType) + " tsyn">
  <#elseif type.timingSymbol.isEventBased()>
    <#return typePrinter.print(type.symType) + " event">
  <#elseif type.timingSymbol.isStrictlyTimeSyncronous()>
    <#return typePrinter.print(type.symType)>
  </#if>
</#function>

<#function prefix timing>
<#---->
<#-- @ftlvariable name="timing" type="montibelle.focus._symboltable.TimingSymbol"-->
  <#if timing.isTimeSyncronous()>
    <#return "Timed o Tsyn o map_tsyn">
  <#elseif timing.isEventBased()>
    <#return "Timed o TLive o map_event">
  <#elseif timing.isStrictlyTimeSyncronous()>
    <#return "Timed o TOne o">
  </#if>
</#function>

<#function msgType type>
<#---->
<#-- @ftlvariable name="type" type="montibelle.focus._symboltable.ChannelTypeSymbol"-->
    <#return "T" + typePrinter.print(type.symType)?replace("[^A-Za-z0-9]", "", "r") + type.timingSymbol.name>
</#function>

<#function timeType timing>
<#---->
<#-- @ftlvariable name="timing" type="montibelle.focus._symboltable.TimingSymbol"-->
    <#if timing.isTimeSyncronous()>
      <#return "TTsyn">
    <#elseif timing.isStrictlyTimeSyncronous()>
      <#return "TTOne">
    <#elseif timing.isEventBased()>
      <#return "TTLive">
    </#if>
</#function>

<#function messageWrapper timing>
<#---->
<#-- @ftlvariable name="timing" type="montibelle.focus._symboltable.TimingSymbol"-->
  <#if timing.isEventBased()>
    <#return "EventMsg">
  <#elseif timing.isTimeSyncronous()>
    <#return "TSynMsg">
  </#if>
</#function>

<#function timeConstructor timing>
<#---->
<#-- @ftlvariable name="timing" type="montibelle.focus._symboltable.TimingSymbol"-->
  <#if timing.isEventBased()>
    <#return "TLive">
  <#elseif timing.isTimeSyncronous()>
    <#return "Tsyn">
  </#if>
</#function>

<#function tickValue timing>
<#---->
<#-- @ftlvariable name="timing" type="montibelle.focus._symboltable.TimingSymbol"-->
  <#if timing.isEventBased()>
    <#return "Tick">
  <#elseif timing.isTimeSyncronous()>
    <#return "Eps">
  </#if>
</#function>

<#function mapFunction timing>
<#---->
<#-- @ftlvariable name="timing" type="montibelle.focus._symboltable.TimingSymbol"-->
  <#if timing.isEventBased()>
    <#return "map_event">
  <#elseif timing.isTimeSyncronous()>
    <#return "map_tsyn">
  </#if>
</#function>

<#macro buildSBEConstructor type>
<#---->
<#-- @ftlvariable name="type" type="montibelle.focus._symboltable.ChannelTypeSymbol"-->
(${prefix(type.timingSymbol)} ${constructor(type)})<#rt>
</#macro>

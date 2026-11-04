<#-- @ftlvariable name="comp"   type="montibelle.focus._ast.ASTComposition" -->

<#---->

<#function MsgOutBrackets string comp>
  <#if comp.isTimed()>
    <#return "Msg (" + string + ")">
  <#else>
    <#return string>
  </#if>
</#function>

<#function MsgInBrackets string comp>
  <#if comp.isTimed()>
    <#return "(Msg " + string + ")">
  <#else>
    <#return string>
  </#if>
</#function>

<#---->

<#function injDef comp >
  <#if comp.isTimed()>
    <#return "inj_def">
  <#else>
    <#return "inj_on_def">
  </#if>
</#function>

<#function invId comp>
  <#if comp.isTimed()>
    <#return "tsynmap_inv_id">
  <#else>
    <#return "smap_inv_id">
  </#if>
</#function>

<#function ctype comp>
  <#if comp.isTimed()>
    <#return "tsynbundle_ctype">
  <#else>
    <#return "bundle_ctype">
  </#if>
</#function>

<#---->
<#function sconc comp>
  <#if comp.isTimed()>
    <#return "tsynmap_sconc">
  <#else>
    <#return "smap_split">
  </#if>
</#function>

<#function split comp>
  <#return sconc(comp)>
</#function>

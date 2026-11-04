<#t><#-- @ftlvariable name="interface" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
<#t><#-- @ftlvariable name="types" type="java.util.List<de.monticore.umlcd4a.symboltable.CDTypeSymbol>" -->

<#function springRoute interface>
  <#---->
  <#-- @ftlvariable name="interface" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
  <#if interface.getPackageName()?has_content>
    <#return interface.getPackageName()?replace(".", "/") + "/" + interface.name?uncap_first>
  <#else>
    <#return interface.name?uncap_first>
  </#if>
</#function>

<#function tsFQN type>
  <#-- @ftlvariable name="type" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
  <#if type.name?contains("Boolean") || type.name?contains("String") || type.name?contains("void")>
    <#return type.name>
  </#if>
  <#if type.name?contains("Integer") >
    <#return "Number">
  </#if>
  <#return type.getPackageName()?replace(".", "_") + "_" + type.enclosingScope.name.get()?lower_case + "_" + type.name>
</#function>

<#function javaFQN type>
<#-- @ftlvariable name="type" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
  <#assign javaPackage_ = javaPackage(type)>
  <#if !javaPackage_?has_content>
    <#return type.name>
  <#else>
    <#return javaPackage_ + "." + type.name>
  </#if>
</#function>

<#function javaPackage type>
<#-- @ftlvariable name="type" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
  <#if type.name?contains("Boolean") || type.name?contains("String") || type.name?contains("Integer") || type.name?contains("void")>
    <#return "">
  </#if>
  <#if type.getPackageName()?has_content>
    <#return type.getPackageName() + "." + type.enclosingScope.name.get()?lower_case>
  <#else>
    <#return type.enclosingScope.name.get()?lower_case>
  </#if>
</#function>

<#function tsImportAIntoB a b>
  <#-- @ftlvariable name="a" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
  <#-- @ftlvariable name="b" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
  <#---->
  <#assign packagesHere = tsFQN(b)?split("_")?reverse[1..]?reverse>
  <#assign packagesThere = tsFQN(a)?split("_")>
  <#assign result = ".">
  <#---->
  <#assign pruned = false>
  <#list packagesThere as package>
    <#if !pruned && (packagesHere?size == package?index || package != packagesHere[package?index])>
      <#assign pruned = true>
      <#list 0..<(packagesHere?size-package?index) as i>
        <#assign result = result + "/..">
      </#list>
    </#if>
    <#if pruned>
      <#assign result = result + "/" + package>
    </#if>
  </#list>
  <#return result>
</#function>

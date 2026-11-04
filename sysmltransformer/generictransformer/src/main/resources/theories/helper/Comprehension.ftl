

<!-- Build set comprehension for the provided initial configuration.
     Returns empty string, if no comprehension was found. -->
<#function initial config>
<#-- @ftlvariable name="config" type="montibelle.focus._ast.ASTConfiguration" -->
  <#local patterns = "">
  <#local compr = "">
  <#list config.state.variableValueList as var>
    <#if var.isComprehension>
      <#if patterns == "">
        <#local patterns = var.definitionDefinition.pattern>
        <#local compr = "(" + var.value + ")">
      <#else>
        <#local patterns = patterns + " " + var.definitionDefinition.pattern>
        <#local compr = compr + " \\<and> (" + var.value + ")">
      </#if>
    </#if>
  </#list>
  <#list config.outputList as out>
    <#if out.isComprehension>
      <#if patterns == "">
        <#local patterns = out.channelSymbol.pattern>
        <#local compr = "(" + out.value + ")">
      <#else>
        <#local patterns = patterns + " " + out.channelSymbol.pattern>
        <#local compr = compr + " \\<and> (" + out.value + ")">
      </#if>
    </#if>
  </#list>
  <#if patterns != "">
    <#return " | "+patterns+" . "+compr>
  <#else>
    <#return "">
  </#if>
</#function>



<!-- Build set comprehension for transitions.
     Returns empty string, if no comprehension was found. -->
<#function transition trans>
  <#t><#-- @ftlvariable name="trans" type="montibelle.focus._ast.ASTTransition" -->
  <#local patterns = ""><#t>
  <#local compr = ""><#t>
  <#list trans.result.state.variableValueList as var>
    <#if var.isComprehension>
      <#if patterns == "">
        <#local patterns = var.definitionDefinition.pattern><#t>
        <#local compr = "(" + var.value + ")"><#t>
      <#else>
        <#local patterns = patterns + " " + var.definitionDefinition.pattern><#t>
        <#local compr = compr + " \\<and> (" + var.value + ")"><#t>
      </#if>
    </#if>
  </#list>
  <#list trans.result.outputList as out>
    <#if out.isComprehension>
      <#if patterns == "">
        <#local patterns = out.channelSymbol.pattern><#t>
        <#local compr = "(" + out.value + ")"><#t>
      <#else>
        <#local patterns = patterns + " " + out.channelSymbol.pattern><#t>
        <#local compr = compr + " \\<and> (" + out.value + ")"><#t>
      </#if>
    </#if>
  </#list>
  <#if patterns != "">
    <#return " | "+patterns+" . "+compr>
  <#else>
    <#return "">
  </#if>
</#function>

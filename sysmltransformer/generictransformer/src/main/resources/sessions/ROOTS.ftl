<#t>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="paths"    type="java.util.List<String>" -->
<#t>
<#t>${tc.signature("paths")}
<#t>
<#list paths as path>
  <#lt>${path}
</#list>

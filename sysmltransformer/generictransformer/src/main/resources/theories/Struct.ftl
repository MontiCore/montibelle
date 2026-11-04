<#t><#import "helper/Type.ftl" as type>
<#t><#import "helper/Macros.ftl" as macro>
<#t>
<#t><#-- @ftlvariable name="tc" type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment" type="Boolean" -->
<#t><#-- @ftlvariable name="th" type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="struct" type="montibelle.focus._ast.ASTUserDefinedStruct" -->
<#t><#-- @ftlvariable name="constants" type="montibelle.transformer.generic.Constants" -->
<#t><#-- @ftlvariable name="typePrinter" type="trafos.ITypePrinter" -->
<#t>${tc.signature("comment", "th", "struct", "constants")}
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports "HOL-Library.Countable_Set"

begin

section \<open>User-defined Datatypes\<close>

datatype ${struct.name} = ${struct.name}Constr <#rt>
    <#lt><#list struct.getFieldList() as field>(* ${field.name} = *) "${typePrinter.print(field.symbol.symType)}"<#sep> </#list>

<#assign allCountable = true>
<#list struct.getFieldList() as field>
  <#if !constants.isTypeCountable(field.symbol.symType)>
    <#assign allCountable = false>
  </#if>
</#list>

<#if allCountable>
instance ${struct.name}::countable
by(countable_datatype)
</#if>

<#list struct.getFieldList() as field>
fun ${struct.name}_get_${field.name} :: "${struct.name} => ${typePrinter.print(field.symbol.symType)}" where
"${struct.name}_get_${field.name} (${struct.name}Constr<#list struct.getFieldList() as f> ${f.pattern}</#list>) = ${field.pattern}"

</#list>
end

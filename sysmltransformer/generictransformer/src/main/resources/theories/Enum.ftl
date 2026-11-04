<#t><#import "helper/Type.ftl" as type>
<#t><#import "helper/Macros.ftl" as macro>
<#t>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="enum"     type="montibelle.focus._ast.ASTEnumType" -->
<#t>${tc.signature("comment", "th", "enum")}
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports "HOL-Library.Countable_Set"

begin

datatype ${enum.name} = <#list enum.literalsList as literal>${literal}<#sep> | </#list>

instance ${enum.name}::countable
  apply(intro_classes)
  by(countable_datatype)

end

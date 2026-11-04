<#t><#import "helper/Macros.ftl" as macro>
<#t>
<#t><#-- @ftlvariable name="tc"         type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="stateSpace" type="montibelle.focus._ast.ASTStateSpace" -->
<#t><#-- @ftlvariable name="constants" type="montibelle.transformer.generic.Constants" -->
<#t>
<#t>${tc.signature("comment", "th", "stateSpace", "constants")}
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


                                                                    
datatype Substate = <#list stateSpace.statesList as state>${state}<#sep> | </#list>

                                       
datatype State = StateConstr Substate <#rt>
<#list stateSpace.stateVariableList as var>(* ${var.name} = *) "${typePrinter.print(var.symbol.symType)}"<#sep> </#list>

                                  
fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s <#list stateSpace.stateVariableList as var>_<#sep> </#list>) = s"
<#list stateSpace.stateVariableList>

                                    
  <#items as var>
      <@macro.seperatorRows var?index/>
fun get${var.name?capitalize} :: "State \<Rightarrow> ${typePrinter.print(var.symbol.symType)}" where
"get${var.name?capitalize} (StateConstr _<#list stateSpace.stateVariableList as var2> ${var2.pattern}</#list>) = ${var.pattern}"
  </#items>
</#list>

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)
    <#assign allCountable = true>
    <#list stateSpace.stateVariableList as var>
      <#if !constants.isTypeCountable(var.symbol.symType)>
        <#assign allCountable = false>
      </#if>
    </#list>
<#if allCountable>

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)
</#if>


end

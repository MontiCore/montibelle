<#t><#import "../Functions.ftl" as f>
<#t>
<#t>${signature("type", "customTypes")}
<#t><#-- @ftlvariable name="type" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
<#t><#-- @ftlvariable name="customTypes" type="java.util.List<de.monticore.umlcd4a.symboltable.CDTypeSymbol>" -->
<#t>
<#t><#assign customTypeNames = customTypes?map(it -> it.getName())/>
<#t>
<#list customTypes as t>
import { ${t.name} as ${f.tsFQN(t)}, is${t.name} as is${f.tsFQN(t)} } from '${f.tsImportAIntoB(t, type)}';
</#list>

<#list type.getAstNode().get().get_PreComments() as comment>
${comment}
</#list>
export interface ${type.name} {
<#list type.getAllVisibleFields() as field>

  <#list field.getAstNode().get().get_PreComments() as comment>
  ${comment}
  </#list>
  <#if field.getStereotype("Opt").isPresent()>
  ${field.name}?: ${f.tsFQN(field.type)};
  <#else>
  ${field.name}: ${f.tsFQN(field.type)};
  </#if>
</#list>

}

   
                                                                
   
export function is${type.name}(o: any): boolean {
  return <#rt>
<#list type.getAllVisibleFields() as field>
  <#if !field.getStereotype("Opt").isPresent()>
    <#if customTypeNames?seq_contains(field.getType().getName())>
      <#lt>('${field.getName()}' in o) && is${f.tsFQN(field.getType())}(o.${field.getName()})<#rt>
    <#else>
      <#lt>('${field.getName()}' in o)<#rt>
    </#if>
  <#else>
    <#if customTypeNames?seq_contains(field.getType().getName())>
      <#lt>(!('${field.getName()}' in o) || is${f.tsFQN(field.getType())}(o.${field.getName()}))<#rt>
    <#else>
      <#lt>true<#rt>
    </#if>
  </#if>
  <#lt><#sep>

      && </#sep><#rt>
</#list>;
}

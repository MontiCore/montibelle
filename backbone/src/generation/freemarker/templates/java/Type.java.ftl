<#t><#import "../Functions.ftl" as f>
<#t>
<#t>${signature("type")}
<#t>
<#t><#-- @ftlvariable name="type" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
<#t>
package ${f.javaPackage(type)};

import org.springframework.lang.NonNull;
import java.util.Optional;

<#list type.getAstNode().get().get_PreComments() as comment>
${comment}
</#list>
public class ${type.getName()} {
<#list type.getAllVisibleFields() as field>

  <#if !field.getStereotype("Opt").isPresent()>
  @NonNull
  </#if>
  private ${f.javaFQN(field.getType())} ${field.getName()};
</#list>

<#list type.getAllVisibleFields()>
  /**
  <#items as field>
    <#if field.getAstNode().get().get_PreComments()?has_content>
   * @param ${field.name} ${field.getAstNode().get().get_PreComments()[0].toString()?replace("/*", "")?replace("*/", "")?replace("*", "")?replace("\n", "")?trim}
    </#if>
  </#items>
   */
</#list>
  public ${type.getName()} (<#rt>
<#list type.getAllVisibleFields() as field>
  <#if field.getStereotype("Opt").isPresent()>
    <#assign nonNullString = "">
  <#else>
    <#assign nonNullString = "@NonNull ">
  </#if>
  <#lt>${nonNullString}${f.javaFQN(field.getType())} ${field.getName()}<#rt>
  <#t><#sep>, </#sep>
</#list>) {
<#list type.getAllVisibleFields() as field>
    this.${field.getName()} = ${field.getName()};
</#list>
  }

                                              
  public ${type.getName()} () {
  }
<#list type.getAllVisibleFields() as field>

  <#if field.getAstNode().get().get_PreComments()?has_content>
  /** @return ${field.getAstNode().get().get_PreComments()[0].toString()?replace("/*", "")?replace("*/", "")?replace("*", "")?replace("\n", "")?trim} */
  </#if>
  <#if field.getStereotype("Opt").isPresent()>
  public Optional<${f.javaFQN(field.getType())}> get${field.getName()?cap_first}() {
    return Optional.ofNullable(${field.getName()});
  }
  <#else>
  @NonNull
  public ${f.javaFQN(field.getType())} get${field.getName()?cap_first}() {
    return ${field.getName()};
  }
  </#if>
</#list>

  @Override
  public String toString(){
    return "${type.getName()} {\n" +
    <#list type.getAllVisibleFields() as field>
    "${field.getName()}: " + ${field.getName()} + "<#if field?has_next>,</#if>\n" +
    </#list>
    "}";
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    else if(o instanceof ${type.getName()}) {
      <#assign otherObject = "other${type.getName()}">
      ${type.getName()} ${otherObject} = (${type.getName()}) o;
      return
      <#list type.getAllVisibleFields() as field>
          <#assign fieldGetter = "get${field.getName()?cap_first}()">
          ${fieldGetter}.equals(${otherObject}.${fieldGetter})<#if field?has_next> &&<#else>;</#if>
      </#list>
    }
    else {
      return false;
    }
  }
}

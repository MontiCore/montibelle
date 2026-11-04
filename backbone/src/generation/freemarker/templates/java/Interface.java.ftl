<#t><#import "../Functions.ftl" as f>
<#t>
<#t>${signature("interface")}
<#t>
<#t><#-- @ftlvariable name="interface" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
<#t>
package ${f.javaPackage(interface)};

import com.googlecode.jsonrpc4j.JsonRpcMethod;
import com.googlecode.jsonrpc4j.JsonRpcService;

<#list interface.getAstNode().get().get_PreComments() as comment>
${comment}
</#list>
@JsonRpcService("${f.springRoute(interface)}")
public interface ${interface.getName()}
<#if interface.getSuperTypes()?has_content >
  extends
  <#list interface.getSuperTypes() as superType>
    <#lt>    ${f.javaFQN(superType)}<#rt>
    <#lt><#sep>, </#sep>
  </#list>
</#if>
{

<#list interface.getMethods() as method>
  <#list method.getAstNode().get().get_PreComments() as comment>
  ${comment}
  </#list>
  ${f.javaFQN(method.getReturnType())} ${method.getName()}(<#rt>
  <#list method.getParameters() as p>
    <#lt>${f.javaFQN(p.getType())} ${p.getName()}<#rt>
    <#t><#sep>, </#sep>
  </#list><#t>
  <#lt>) throws Exception;

</#list>
}

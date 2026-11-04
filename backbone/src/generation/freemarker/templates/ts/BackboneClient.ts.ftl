<#t><#import "../Functions.ftl" as f>
<#t>
<#t>${signature("interfaces", "clients")}
<#t>
<#t><#-- @ftlvariable name="interfaces" type="java.util.List<de.monticore.umlcd4a.symboltable.CDTypeSymbol>" -->
<#t><#-- @ftlvariable name="clients" type="java.util.List<Clients>" -->
<#t>
import { JsonRpcClient } from "./JsonRpcClient";

<#list interfaces as interface>
import { ${interface.name} as ${f.tsFQN(interface)}, ${interface.name}Client as ${f.tsFQN(interface)}Client } from './${f.tsFQN(interface)?replace("_", "/")}';
</#list>
<#list clients as client>

<#if client.export>export </#if>class ${client.name} extends JsonRpcClient {
  <#list client.fields as field>

  ${field.name}: ${field.type};
  </#list>

  constructor(host: string) {
    super(host);
  <#list client.fields as field>
    this.${field.name} = new ${field.type}(host);
  </#list>
  }

}
</#list>

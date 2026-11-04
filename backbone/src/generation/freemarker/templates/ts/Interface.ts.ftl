<#t><#import "../Functions.ftl" as f>
<#t>
<#t>${signature("interface", "customTypes")}
<#t>
<#t><#-- @ftlvariable name="interface" type="de.monticore.umlcd4a.symboltable.CDTypeSymbol" -->
<#t><#-- @ftlvariable name="customTypes" type="java.util.List<de.monticore.umlcd4a.symboltable.CDTypeSymbol>" -->
<#t>
<#t><#assign typeNames = customTypes?map(it -> it.getName())/>
<#t>
<#t>
<#t>
import { JsonRpcClient } from './<#list 0..<interface.packageName?split(".")?size as i>../</#list>../JsonRpcClient';

<#list customTypes as type>
import { ${type.name} as ${f.tsFQN(type)}, is${type.name} as is${f.tsFQN(type)} } from '${f.tsImportAIntoB(type, interface)}';
</#list>

<#list interface.getSuperTypes() as type>
import { ${type.name} as ${f.tsFQN(type)} } from '${f.tsImportAIntoB(type, interface)}';
</#list>

<#list interface.getAstNode().get().get_PreComments() as comment>
${comment}
</#list>
export interface ${interface.getName()}
<#list interface.getSuperTypes()>
  extends
  <#items as type>
    ${f.tsFQN(type)}<#sep>,</#sep>
  </#items>
</#list>
{
<#list interface.getMethods() as method>

  <#list method.getAstNode().get().get_PreComments() as comment>
  ${comment}
  </#list>
  ${method.name}(<#rt>
  <#list method.getParameters() as p>
    <#lt>${p.getName()}<#if method.getStereotype("Opt")??>?</#if>: ${f.tsFQN(p.getType())}<#rt>
    <#sep>, </#sep><#t>
  </#list><#rt>
  <#lt>): Promise<${f.tsFQN(method.getReturnType())}<#if method.getStereotype("Opt")??> | undefined</#if>>;
</#list>

}

   
                        
   
export class ${interface.getName()}Client extends JsonRpcClient implements ${interface.getName()} {

  constructor(host: string){
    super(host);
  }

  <#list interface.getAllVisibleMethods() as method>
  async ${method.name}(<#list method.getParameters() as p>${p.getName()}: ${f.tsFQN(p.getType())}<#sep>, </#list>)<#rt>
    <#lt>: Promise<${f.tsFQN(method.getReturnType())}<#if method.getStereotype("Opt")??> | undefined</#if>> {
    return new Promise((resolve, reject) => {
      this.sendRequest("${f.springRoute(interface)}", "${method.name}", [<#list method.getParameters() as p>${p.getName()}<#sep>, </#list>])
        .then(res => {
    <#if typeNames?seq_contains(method.getReturnType().getName())>
           const output = res.result;
           if(is${f.tsFQN(method.getReturnType())}(output)) {
             resolve(output);
           }
           else {
             reject("Type error: Received object does not implement ${method.getReturnType().getName()}. " + JSON.stringify(output));
           }
    <#else>
           resolve(res.result);
    </#if>
        })
        .catch(err => reject(err));
    });
  }

  </#list>
}

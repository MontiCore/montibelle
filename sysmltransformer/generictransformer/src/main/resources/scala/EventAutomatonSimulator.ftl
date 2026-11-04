<#t><#import "ScalaHelper.ftl" as helper>
<#t>
<#t><#-- @ftlvariable name="tc"                 type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"            type="boolean" -->
<#t><#-- @ftlvariable name="className"          type="String" -->
<#t><#-- @ftlvariable name="codeTheoryFilename" type="String" -->
<#t><#-- @ftlvariable name="aut"                type="montibelle.focus._ast.ASTEventAutomaton" -->
<#t><#-- @ftlvariable name="typePrinter" type="trafos.ITypePrinter" -->
<#t>
<#t>${tc.signature("comment", "className", "codeTheoryFilename", "aut")}
<#t>
import ${codeTheoryFilename}_scalaExec._
import montibelle.simulation.{ISimulator, InputParameter}
import java.util.Map
import scala.collection.JavaConverters._
import scala.math.BigInt
import scala.runtime.BoxedUnit

                                    
class ${className}(override val input: Map[String, java.util.List[Object]], inputParameter: InputParameter) extends ISimulator(input, inputParameter) {

  override def simulate(): Map[String, java.util.List[Object]] = {
    val inputParameters = new Tuple2[Unit, ((natural, natural), (natural, natural))](
      BoxedUnit.UNIT,
      Tuple2(
        Tuple2(
          Nata(BigInt.apply(inputParameter.seed1)),
          Nata(BigInt.apply(inputParameter.seed2))
        ),Tuple2(
          Nata(BigInt.apply(inputParameter.seed3)),
          Nata(BigInt.apply(inputParameter.seed4))
        )
      )
    )

<#list aut.inputBundleSymbol.channels as c>
    val ${c.localName} = input.get("${c.localName}").asScala.toList;
    val ${c.localName}Converted: List[event[${helper.scalaType(typePrinter.print(c.typeSymbol.symType))}]] = ${c.localName}.map(item => {
      (if (item.isInstanceOf[de.monticore.lang.testdsl.Tick]) Tick[${helper.scalaType(typePrinter.print(c.typeSymbol.symType))}] else <#rt>
  <#switch typePrinter.print(c.typeSymbol.symType)>
    <#case "bool">
      <#lt>Eventa(item.asInstanceOf[Boolean])<#rt>
      <#break>
    <#case "nat">
      <#lt>Eventa(nat_of_integer(BigInt.apply(item.asInstanceOf[Int])))<#rt>
      <#break>
    <#case "string">
      <#lt>Eventa(item.asInstanceOf[java.lang.String].toCharArray.toList.asInstanceOf[List[char]])<#rt>
      <#break>
    <#default>
      <#lt>Eventa(item.asInstanceOf[${typePrinter.print(c.typeSymbol.symType)}])<#rt>
  </#switch>)
    });
    val ${c.localName}Stream = list2s(${c.localName}Converted);

</#list>
    val sb = insbsetter_nc<#list aut.inputBundleSymbol.channels as c>(${c.localName}Stream<#sep>, </#sep></#list><#list aut.inputBundleSymbol.channels as c>)</#list>
    val outputStream = execsem(inputParameters, sb);
    val output = new java.util.HashMap[String, java.util.List[Object]]
    val streams = sbToList(outputStream)
<#list aut.outputBundleSymbol.channels as c>
    output.put("${c.localName}", streams.get(${c?index}))
</#list>
    return output
  };
     
                                                                                                                          
     
  def sbToList[E](sb:sb[channelsa]) : java.util.List[java.util.List[Object]] = {
    var result = new java.util.ArrayList[java.util.List[Object]]()
    var stream:Any = sb2stream(sb)
    while (stream.isInstanceOf[(stream[event[Any]], Object)]) {
      result.add(streamToList(stream.asInstanceOf[(stream[event[Any]], Object)]._1))
      stream = stream.asInstanceOf[(stream[event[Any]], Object)]._2
    }
    result.add(streamToList(stream.asInstanceOf[stream[event[Any]]]))
    return result
  }

  def streamToList[E](input:stream[event[Any]]) : java.util.List[Object] = {
    var result = new java.util.ArrayList[Object]()
    var remainder = input
    while (remainder != new stream_bottom_nc) {
      val value = remainder.asInstanceOf[lscons_u_nc[event[Any]]].a
      if (value == Tick[Any]){
        result.add(de.monticore.lang.testdsl.Tick.getInstance())
      } else {
      val item = value.asInstanceOf[Eventa[Object]].a;
        if(item.isInstanceOf[nat]) {
          result.add(integer_of_nat(item.asInstanceOf[nat]))
        } else {
          result.add(value.asInstanceOf[Eventa[Object]].a)
        }
      }
      remainder = remainder.asInstanceOf[lscons_u_nc[event[Any]]].b
    }
    return result
  }

}




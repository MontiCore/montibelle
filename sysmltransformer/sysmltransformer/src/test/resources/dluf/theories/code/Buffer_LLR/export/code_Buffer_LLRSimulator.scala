import code_Buffer_LLR_scalaExec._
import montibelle.simulation.{ISimulator, InputParameter}
import java.util.Map
import scala.collection.JavaConverters._
import scala.math.BigInt
import scala.runtime.BoxedUnit

class code_Buffer_LLRSimulator(override val input: Map[String, java.util.List[Object]], inputParameter: InputParameter) extends ISimulator(input, inputParameter) {

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

    val channel_control_data = input.get("channel_control_data").asScala.toList;
    val channel_control_dataConverted: List[event[CtrlEnum]] = channel_control_data.map(item => {
      (if (item.isInstanceOf[de.monticore.lang.testdsl.Tick]) Tick[CtrlEnum] else Eventa(item.asInstanceOf[CtrlEnum])  )
    });
    val channel_control_dataStream = list2s(channel_control_dataConverted);

    val channel_input_data = input.get("channel_input_data").asScala.toList;
    val channel_input_dataConverted: List[event[Packet]] = channel_input_data.map(item => {
      (if (item.isInstanceOf[de.monticore.lang.testdsl.Tick]) Tick[Packet] else Eventa(item.asInstanceOf[Packet])  )
    });
    val channel_input_dataStream = list2s(channel_input_dataConverted);

    val sb = insbsetter_nc(channel_control_dataStream, (channel_input_dataStream))
    val outputStream = execsem(inputParameters, sb);
    val output = new java.util.HashMap[String, java.util.List[Object]]
    val streams = sbToList(outputStream)
    output.put("channel_output_data", streams.get(0))
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




import Event3_scalaExec._
import montibelle.simulation.{ISimulator, InputParameter}
import java.util.Map
import scala.collection.JavaConverters._
import scala.math.BigInt
import scala.runtime.BoxedUnit

class Event3Simulator(override val input: Map[String, java.util.List[Object]], inputParameter: InputParameter) extends ISimulator(input, inputParameter) {

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

    val beInChannel_rep = input.get("beInChannel_rep").asScala.toList;
    val beInChannel_repConverted: List[event[Boolean]] = beInChannel_rep.map(item => {
      (if (item.isInstanceOf[de.monticore.lang.testdsl.Tick]) Tick[Boolean] else Eventa(item.asInstanceOf[Boolean]))
    });
    val beInChannel_repStream = list2s(beInChannel_repConverted);

    val natInChannel_rep = input.get("natInChannel_rep").asScala.toList;
    val natInChannel_repConverted: List[event[nat]] = natInChannel_rep.map(item => {
      (if (item.isInstanceOf[de.monticore.lang.testdsl.Tick]) Tick[nat] else Eventa(nat_of_integer(BigInt.apply(item.asInstanceOf[Int]))))
    });
    val natInChannel_repStream = list2s(natInChannel_repConverted);

    val sInChannel_rep = input.get("sInChannel_rep").asScala.toList;
    val sInChannel_repConverted: List[event[List[char]]] = sInChannel_rep.map(item => {
      (if (item.isInstanceOf[de.monticore.lang.testdsl.Tick]) Tick[List[char]] else Eventa(item.asInstanceOf[java.lang.String].toCharArray.toList.asInstanceOf[List[char]]))
    });
    val sInChannel_repStream = list2s(sInChannel_repConverted);

    val sb = insbsetter_nc(beInChannel_repStream, (natInChannel_repStream, (sInChannel_repStream)))
    val outputStream = execsem(inputParameters, sb);
    val output = new java.util.HashMap[String, java.util.List[Object]]
    val streams = sbToList(outputStream)
    output.put("beOutChannel_rep", streams.get(0))
    output.put("natOutChannel_rep", streams.get(1))
    output.put("sOutChannel_rep", streams.get(2))
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




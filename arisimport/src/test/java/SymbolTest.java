import bpmn.BPMNMill;
import bpmn.BPMNTool;
import bpmn._ast.ASTIncoming;
import de.se_rwth.commons.logging.LogStub;
import epc.EPCMill;
import epc.EPCTool;
import epc._cocos.EPCCoCoChecker;
import epc._symboltable.ObjectSymbol;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.AssertionsForClassTypes.assertThat;

public class SymbolTest {

  @Test
  public void referenceCheck() {
    var tool = new BPMNTool();

    LogStub.init();
    BPMNMill.init();

    var ast = tool.parse("src/test/resources/ModelInformation.txt");
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);

    var endEvent = ast.getDiagram(0).getSpannedScope()
        .resolveObject("End event");

    assertThat(endEvent).isPresent();
    assertThat(endEvent.get().isPresentAstNode());

    var relations = endEvent.get().getAstNode().getRelationshipList();

    assertThat(relations.size()).isEqualTo(1);
    assertThat(relations.get(0)).isInstanceOf(ASTIncoming.class);

    var incoming = (ASTIncoming)relations.get(0);

    assertThat(incoming.getName()).isEqualTo("B");
    assertThat(incoming.isPresentNameSymbol());
    assertThat(incoming.getNameSymbol().isPresentAstNode());

    var b = incoming.getNameSymbol().getAstNode();

    assertThat(b.isPresent_SourcePositionStart());
    assertThat(b.get_SourcePositionStart().getLine()).isEqualTo(46);
  }

  @Test
  public void epcResolveTest() {
    var tool = new EPCTool();
    LogStub.init();
    EPCMill.init();

    var ast = tool.parse("src/test/resources/CreateWeightCalculationForecast.Processed.txt");
    tool.createSymbolTable(ast);

    var objNameWithFunnySymbols =
        "Compare between Weight Calculation Forecast and Requirements -...";

    var obj = ast.getDiagram(0).getObjects().getObject(75);
    assertThat(obj.getName()).isEqualTo(objNameWithFunnySymbols);
    assertThat(obj.getSymbol()).isNotNull();
    assertThat(obj.getSymbol().getName()).isEqualTo(objNameWithFunnySymbols);
    assertThat(obj.getSymbol()).isInstanceOf(ObjectSymbol.class);

    var res = EPCMill.globalScope()
        .resolveObjectDown("CreateWeightCalculationForecast." + objNameWithFunnySymbols);
    assertThat(res).isPresent();

  }
}

import bpmn.BPMNMill;
import bpmn.BPMNTool;
import bpmn._ast.ASTIncoming;
import de.se_rwth.commons.logging.LogStub;
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
}

import de.monticore.lang.sysmlactions._ast.ASTCalcDef;
import de.monticore.lang.sysmlactions._visitor.SysMLActionsVisitor2;
import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.se_rwth.commons.logging.LogStub;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

public class ValExampleTest {

  @Test
  public void testValExample() throws IOException {
    var model = "attribute def A {\n" +
        "  attribute val: boolean;\n" +
        "}\n" +
        "\n" +
        "calc def Test {\n" +
        "  in a: A;\n" +
        "  a.val\n" +
        "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        focusModels.add(CalcDefTransformer.transform(node));
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);
    assertThat(focusModels.get(0))
        .isEqualTo("fun Test(a: A)  = \"(A_get_val a)\"");
  }
}

import de.monticore.lang.sysmlactions._ast.ASTSendActionUsage;
import de.monticore.lang.sysmlconstraints._ast.ASTConstraintUsage;
import de.monticore.lang.sysmlparts._ast.ASTSysMLPackage;
import de.monticore.lang.sysmlparts._ast.ASTPartDef;
import de.monticore.lang.sysmlstates._ast.ASTStateDef;
import de.monticore.lang.sysmlstates._ast.ASTSysMLTransition;
import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.se_rwth.commons.logging.Log;
import de.se_rwth.commons.logging.LogStub;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestInstance;

import static montibelle.transformer.sysml.extensions.ASTExpressionKt.print;
import static org.assertj.core.api.Assertions.assertThat;

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class PrinterTest {

  private static final String AUTOMATA_MODEL =
      "package test {\n" +
          "  state def Test {\n" +
          "    entry; then State;\n" +
          "    state State\n;" +
          "    transition trans\n" +
          "      first State\n" +
          "      do action {send a + b to c; }\n" +
          "      then State;\n" +
          "  }\n" +
          "}";

  private static final String SPECIFICATION_MODEL =
      "package test {\n" +
          "  part def Test {\n" +
          "    assert constraint test {\n" +
          "      i == o\n" +
          "    }\n" +
          "  }\n" +
          "}";

  @BeforeAll
  public void up() {
    LogStub.init();
    new SysMLv2Tool().init();
  }

  @BeforeEach
  public void clear() {
    Log.clearFindings();
  }

  @Test
  public void testPrintTransition() throws Exception {
    ASTSysMLPackage ast =
        (ASTSysMLPackage) SysMLv2Mill.parser()
            .parse_String(AUTOMATA_MODEL)
            .get()
            .getSysMLElementList()
            .stream()
            .filter(e -> e instanceof ASTSysMLPackage)
            .findFirst()
            .get();

    assertThat(ast).isNotNull();

    ASTStateDef stateDef = (ASTStateDef) ast.getSysMLElementList().get(0);
    ASTSysMLTransition transition =
        (ASTSysMLTransition) stateDef.getSysMLElementList().get(2);

    String result =
        print(((ASTSendActionUsage) transition.getDoAction()
            .getSysMLElementList()
            .get(0))
            .getPayload());

    assertThat(result).isEqualTo("(a + b)");
  }

  @Test
  public void testPrintPredicate() throws Exception {
    ASTSysMLPackage ast =
        (ASTSysMLPackage) SysMLv2Mill.parser()
            .parse_String(SPECIFICATION_MODEL)
            .get()
            .getSysMLElementList()
            .stream()
            .filter(e -> e instanceof ASTSysMLPackage)
            .findFirst()
            .get();

    assertThat(ast).isNotNull();

    ASTPartDef partDef = (ASTPartDef) ast.getSysMLElementList().get(0);
    ASTConstraintUsage constraint =
        (ASTConstraintUsage) partDef.getSysMLElementList().get(0);

    String result = print(constraint.getExpression());

    assertThat(result).isEqualTo("(i = o)");
  }

  @Test
  public void testPrintNotPredicate() throws Exception {
    var parser = SysMLv2Mill.parser();
    var expression = parser.parse_StringExpression("!foo");

    assertThat(Log.getFindings()).isEmpty();
    assertThat(parser.hasErrors()).isFalse();
    assertThat(expression).isPresent();

    String result = print(expression.get());
    assertThat(result).isEqualTo("(Not foo)");
  }

  @Test
  public void testImplication() throws Exception {
    var parser = SysMLv2Mill.parser();
    var expression = parser.parse_StringExpression("a implies b");

    assertThat(Log.getFindings()).isEmpty();
    assertThat(parser.hasErrors()).isFalse();
    assertThat(expression).isPresent();

    String result = print(expression.get());
    assertThat(result).isEqualTo("a \\<longrightarrow> b");
  }
}

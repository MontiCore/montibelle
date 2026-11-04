import de.monticore.expressions.expressionsbasis._ast.ASTExpression;
import de.monticore.lang.sysmlconstraints._ast.ASTConstraintUsage;
import de.monticore.lang.sysmlconstraints._visitor.SysMLConstraintsVisitor2;
import de.monticore.lang.sysmlparts._ast.ASTPartDef;
import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.se_rwth.commons.logging.LogStub;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.concurrent.atomic.AtomicReference;

import static montibelle.transformer.sysml.Main.getEventExpressionPrinter;
import static org.assertj.core.api.AssertionsForClassTypes.assertThat;

public class ExpressionPrinterTest {

  @Test
  public void testChannelName() throws IOException {
    LogStub.init();
    var tool = new SysMLv2Tool();
    tool.init();
    var parser = SysMLv2Mill.parser();
    var printer = getEventExpressionPrinter(tool.getInheritanceTraverser());

    var model = "port def B { attribute b: boolean; }";
    var ast = parser.parse_String(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    model = "part def P { port b:B; constraint { b.b }}";
    ast = parser.parse_String(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var part = (ASTPartDef) ast.getSysMLElement(0);
    var constr = (ASTConstraintUsage) part.getSysMLElement(1);
    var expr = constr.getExpression();

    var str = printer.print(expr);

    assertThat(str).isEqualTo("channel_b_b_pattern");
  }

  @Test
  public void testConditionalAnd2() throws IOException {
    var tool = new SysMLv2Tool();
    tool.init();
    var printer = getEventExpressionPrinter(tool.getInheritanceTraverser());

    var astExp = SysMLv2Mill.parser().parse_StringExpression("a & b").get();
    var str = printer.print(astExp);

    assertThat(str).isEqualTo("(a \\<and> b)");
  }

  @Test
  public void testConditionalOr2() throws IOException {
    var tool = new SysMLv2Tool();
    tool.init();
    var printer = getEventExpressionPrinter(tool.getInheritanceTraverser());

    var astExp = SysMLv2Mill.parser().parse_StringExpression("a | b").get();
    var str = printer.print(astExp);

    assertThat(str).isEqualTo("(a \\<or> b)");
  }

  @Test
  public void testFieldAccessOfStruct() throws Exception {
    var model = "attribute def A {\n" +
        "  attribute val: boolean;\n" +
        "}\n" +
        "\n" +
        "attribute a: A;\n" +
        "\n" +
        "constraint {\n" +
        "  a.val\n" +
        "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    AtomicReference<ASTExpression> exprRef = new AtomicReference<>();

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLConstraints(new SysMLConstraintsVisitor2() {

      @Override
      public void visit(ASTConstraintUsage node) {
        exprRef.set(node.getExpression());
      }
    });
    ast.accept(traverser);

    var expr = exprRef.get();
    var printer = getEventExpressionPrinter(tool.getInheritanceTraverser());
    var actual = printer.print(expr);

    Assertions.assertThat(actual).isEqualTo("(A_get_val var_a)");
  }
}

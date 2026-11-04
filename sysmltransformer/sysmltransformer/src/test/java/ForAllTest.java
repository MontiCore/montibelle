import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.se_rwth.commons.logging.LogStub;
import org.junit.jupiter.api.Test;
import static org.assertj.core.api.Assertions.assertThat;
import static montibelle.transformer.sysml.Main.getEventExpressionPrinter;

public class ForAllTest {

  @Test
  public void testForallExpressionPrinter() throws Exception {
    var sysmlExpr = "(1,2,3)->forAll { in e:E; true }";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    var printer = getEventExpressionPrinter(tool.getInheritanceTraverser());

    var astExpr = SysMLv2Mill.parser().parse_StringExpression(sysmlExpr).get();
    var str = printer.print(astExpr);

    assertThat(str).isEqualTo("Ball {1,2,3} (\\<lambda> e. True)");
  }
}

import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.se_rwth.commons.logging.LogStub;
import org.junit.jupiter.api.Test;

import static montibelle.transformer.sysml.Main.getEventExpressionPrinter;
import static org.assertj.core.api.Assertions.assertThat;

public class BodyExpressionTest {

  @Test
  public void testBodyExpressionPrinter() throws Exception {
    var sysmlExpr = "{ attribute b: Boolean; return : Boolean; b == false }";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var printer = getEventExpressionPrinter(tool.getInheritanceTraverser());
    var astExpr = SysMLv2Mill.parser().parse_StringExpression(sysmlExpr).get();

    var result = printer.print(astExpr);

    assertThat(result).isEqualTo("(\\<lambda> var_b. (b = False))");
  }
}

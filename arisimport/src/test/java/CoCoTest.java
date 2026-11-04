import de.se_rwth.commons.logging.Log;
import de.se_rwth.commons.logging.LogStub;
import epc.*;
import epc._cocos.EPCCoCoChecker;
import org.junit.Test;

import static org.assertj.core.api.Assertions.assertThat;

public class CoCoTest {

  @Test
  public void testResolveRelationshipCoCo() {
    var tool = new EPCTool();

    LogStub.init();
    EPCMill.init();

    var ast = tool.parse("src/test/resources/CreateWeightCalculationForecast.Untangled.txt");
    tool.createSymbolTable(ast);

    var checker = new EPCCoCoChecker();
    checker.addCoCo(new ResolveRelationshipCoCo());
    checker.checkAll(ast);

    assertThat(Log.getFindings()).isEmpty();
  }

  @Test
  public void testMatchingPairsCoCo() {
    var tool = new EPCTool();

    LogStub.init();
    EPCMill.init();

    var ast = tool.parse("src/test/resources/CreateWeightCalculationForecast.Processed.txt");
    tool.createSymbolTable(ast);

    var checker = new EPCCoCoChecker();
    checker.addCoCo(new MatchingPairsCoCo());
    checker.checkAll(ast);

    assertThat(Log.getFindings()).isEmpty();
  }

  @Test
  public void testOutgoingCoCo() {
    var tool = new EPCTool();

    LogStub.init();
    EPCMill.init();

    var ast = tool.parse("src/test/resources/CreateWeightCalculationForecast.Processed.txt");
    tool.createSymbolTable(ast);

    var checker = new EPCCoCoChecker();
    checker.addCoCo(new OutgoingCoCo());
    checker.checkAll(ast);

    assertThat(Log.getFindings()).isEmpty();
  }
}

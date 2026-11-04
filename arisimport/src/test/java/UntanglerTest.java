import de.se_rwth.commons.logging.Log;
import epc.EPCTool;
import epc.Untangler;
import org.junit.Test;

import java.nio.file.Paths;

public class UntanglerTest {

  @Test
  public void testUntangler() {
    Log.init();
    var tool = new EPCTool();
    tool.init();
    Untangler.untangle(
        tool,
        Paths.get("src/test/resources/CreateWeightCalculationForecast.Processed.txt"),
        Paths.get("src/test/resources/CreateWeightCalculationForecast.Untangled.txt")
    );
  }

}

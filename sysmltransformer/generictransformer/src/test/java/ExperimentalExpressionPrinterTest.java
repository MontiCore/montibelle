import de.se_rwth.commons.logging.Log;
import de.se_rwth.commons.logging.LogStub;
import montibelle.focus.FocusMill;
import trafos.ExperimentalExpressionPrinter;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

public class ExperimentalExpressionPrinterTest {

  @BeforeAll
  public static void init() {
    LogStub.init();
    FocusMill.init();
  }

  @BeforeEach
  public void clear() {
    Log.clearFindings();
    Log.enableFailQuick(true);
  }

  @Test
  public void testPrint() {
    var ast = FocusMill.nameExpressionBuilder()
        .setName("myChannel")
        .build();
    ast.setEnclosingScope(FocusMill.globalScope());

    var channel = FocusMill.channelSymbolBuilder()
        .setName("myChannel")
        .setPattern("ch_myChannel")
        .build();
    FocusMill.globalScope().add(channel);

    var printer = new ExperimentalExpressionPrinter();
    assertThat(printer.print(ast)).isEqualTo("ch_myChannel");
  }

}

import de.se_rwth.commons.logging.Log;
import de.se_rwth.commons.logging.LogStub;
import montibelle.transformer.generic.Constants;
import montibelle.transformer.util.FreemarkerInterface;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.StringWriter;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class RootsTest {

  @BeforeEach
  public void setUp() {
    LogStub.init();
    Log.getFindings().clear();
  }

  @Test
  public void testRoots() {
    List<String> input = List.of("this/is/a/test", "it/should/produce/two/lines");
    StringWriter writer = new StringWriter();

    FreemarkerInterface.instance.generate(Constants.ROOTS_TEMPLATE, writer, input);

    String outcome = writer.toString();
    String expected = String.join("\n", input) + "\n";

    assertEquals(expected, outcome, "The generated ROOTS doesnt match the expected output");
  }

  @AfterEach
  public void fileCompare() throws IOException {
    assertTrue(Log.getFindings().isEmpty(), Log.getFindings().toString());
  }
}

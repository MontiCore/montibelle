import epc.Preprocessor;
import org.junit.Test;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.nio.file.Paths;

public class PreprocessorTest {

  @Test
  public void testPreprocessor() throws IOException {
    var res = new StringWriter();
    var out = new BufferedWriter(res);

    var prep = new Preprocessor(
        Paths.get("src/test/resources/CreateWeightCalculationForecast.txt"),
        Paths.get("src/test/resources/CreateWeightCalculationForecast.Processed.txt")
    );
    prep.run();

    out.flush();
  }

}

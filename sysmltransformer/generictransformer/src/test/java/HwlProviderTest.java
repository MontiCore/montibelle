import de.se_rwth.commons.logging.LogStub;
import montibelle.transformer.generic.hwls.FilebasedHwlProvider;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.nio.file.Paths;

public class HwlProviderTest {

  private static final String YAML = "src/test/resources/substitute/HWL.yaml";
  private static final String SESSION = "DummySession";
  private static final String THY = "DummyTheory";

  @Test
  public void testFilebasedSubstitution() {
    LogStub.init();

    var hwlProvider = new FilebasedHwlProvider(Paths.get(YAML));
    Assertions.assertThat(hwlProvider.substituteFor(SESSION, THY)).isNotNull();
  }
}

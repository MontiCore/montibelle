import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.se_rwth.commons.logging.Log;
import de.se_rwth.commons.logging.LogStub;
import montibelle.focus.FocusMill;
import montibelle.transformer.generic.hwls.InMemoryHwlProvider;
import montibelle.transformer.sysml.Main;
import org.apache.commons.io.FileUtils;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import static org.assertj.core.api.Assertions.assertThat;


class StreamConstraintsTest {
  final String BASE = "src/test/resources/streamConstraints";

  final String MODELS = BASE + "/models";

  @Test
  public void testMainFromScratch() throws IOException {
    LogStub.init();

    FileUtils.deleteDirectory(Paths.get(BASE + "/focusSymbols").toFile());
    FileUtils.deleteDirectory(Paths.get(BASE + "/sysmlSymbols").toFile());
    FileUtils.deleteDirectory(Paths.get(BASE + "/theories").toFile());

    List<String> modelSets = List.of(
        MODELS + "/Booleans.sysml",
        MODELS + "/Inverter.sysml"
    );

    Path target = Paths.get(BASE);
    InMemoryHwlProvider hwlProvider = new InMemoryHwlProvider();

    modelSets.stream().forEach(modelSet -> {
      List<Path> sources = Arrays.stream(modelSet.split(";"))
          .map(s -> Paths.get(s))
          .collect(Collectors.toList());
      Main.transformIncrementally(sources, target, hwlProvider, false);
      assertThat(Log.getFindings()).filteredOn(e -> e.isError()).isEmpty();

      SysMLv2Mill.globalScope().clear();
      FocusMill.init();
      FocusMill.globalScope().clear();
      SysMLv2Mill.reset();
      FocusMill.reset();
    });
  }
}

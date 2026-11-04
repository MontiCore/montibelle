import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.se_rwth.commons.logging.Log;
import de.se_rwth.commons.logging.LogStub;
import extension.comparator.FileCompare;
import montibelle.focus.FocusMill;
import montibelle.transformer.generic.hwls.InMemoryHwlProvider;
import montibelle.transformer.sysml.Main;
import org.apache.commons.io.FileUtils;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import static org.assertj.core.api.Assertions.assertThat;

public class LambdasTest {

  final String BASE = "src/test/resources/lambdas";
  final String MODELS = BASE + "/models";

  @FileCompare(base = BASE, recursive = true)
  @Test
  public void testLambdas() throws IOException {
    LogStub.init();

    FileUtils.deleteDirectory(Paths.get(BASE + "/focusSymbols").toFile());
    FileUtils.deleteDirectory(Paths.get(BASE + "/sysmlSymbols").toFile());
    FileUtils.deleteDirectory(Paths.get(BASE + "/theories").toFile());

    var modelSets = List.of(
        MODELS + "/Booleans.sysml",
        MODELS + "/Lambdas.sysml",
        MODELS + "/Nats.sysml",
        MODELS + "/LambdasAddition.sysml"
    );

    var target = Paths.get(BASE);
    var hwlProvider = new InMemoryHwlProvider();

    modelSets.stream().forEach( modelSet -> {
      var sources = Arrays.stream(modelSet.split(";"))
          .map(s -> Paths.get(s))
          .collect(Collectors.toList());
      Main.transformIncrementally(sources, target, hwlProvider, false);

      assertThat(Log.getFindings()).filteredOn(e->e.isError()).isEmpty();

      FocusMill.init();
      FocusMill.globalScope().clear();
      FocusMill.reset();
      SysMLv2Mill.init();
      SysMLv2Mill.globalScope().clear();
      SysMLv2Mill.reset();
    });
  }
}

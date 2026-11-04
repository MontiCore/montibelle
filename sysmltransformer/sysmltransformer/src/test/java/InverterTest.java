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

class InverterTest {
  final String BASE = "src/test/resources/inverter";

  final String MODELS = BASE + "/models";

  @FileCompare(base = BASE, recursive = true)
  @Test
  public void testMainFromScratch() throws IOException {
    LogStub.init();

    FileUtils.deleteDirectory(Paths.get(BASE + "/focusSymbols").toFile());
    FileUtils.deleteDirectory(Paths.get(BASE + "/sysmlSymbols").toFile());
    FileUtils.deleteDirectory(Paths.get(BASE + "/theories").toFile());

    var modelSets = List.of(
        MODELS + "/Booleans.sysml",
        MODELS + "/Inverter_HLR1.sysml",
        MODELS + "/Inverter_HLR2.sysml",
        MODELS + "/Inverter_LLR1.sysml",
        MODELS + "/Inverter_LLR2.sysml",
        MODELS + "/Requirement.sysml"
    );

    var target = Paths.get(BASE);
    var hwlProvider = new InMemoryHwlProvider();

    modelSets.stream().forEach(modelSet -> {
      var sources = Arrays.stream(modelSet.split(";"))
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

  @FileCompare(base = BASE, recursive = true)
  @Test
  public void testMainWithSymfiles() {
    LogStub.init();

    var modelSets = List.of(
        MODELS + "/Booleans.sysml",
        MODELS + "/Inverter_HLR1.sysml",
        MODELS + "/Inverter_HLR2.sysml",
        MODELS + "/Inverter_LLR1.sysml",
        MODELS + "/Inverter_LLR2.sysml",
        MODELS + "/Requirement.sysml"
    );

    var target = Paths.get(BASE);
    var hwlProvider = new InMemoryHwlProvider();

    modelSets.stream().forEach(modelSet -> {
      var sources = Arrays.stream(modelSet.split(";"))
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
